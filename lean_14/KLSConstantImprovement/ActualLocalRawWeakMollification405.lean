import KLS.WeakDerivativeMollification
import KLS.LocalWeakDerivativeUniqueness
import KLS.MollificationLocalization

/-! Actual mollification of raw local weak derivatives.  The reflected-kernel
argument needs only local integrability, so no artificial global L2 hypothesis
is needed. Compact multipliers then give genuine strong L2 convergence of the
classical derivatives of the same mollifiers. -/
noncomputable section
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology ContDiff ENNReal Convolution
namespace KLSConstantImprovement.ActualLocalRawWeakMollification405
open KLS
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem local_weak_scalarConvolution_eq
    {f F κ : Space n → ℝ} {i : Fin n}
    (hf : LocallyIntegrable f volume)
    (hF : HasLocalWeakCoordinateDerivative f F i)
    (hκ : ContDiff ℝ 1 κ) (hc : HasCompactSupport κ) (a : Space n) :
    coordinateDerivative (scalarConvolution f κ) i a = scalarConvolution F κ a := by
  rw [coordinateDerivative_scalarConvolution hf hκ hc]
  have ht : ContDiff ℝ 1 (fun y => κ (a - y)) :=
    hκ.comp (contDiff_const.sub contDiff_id)
  have htc : HasCompactSupport (fun y => κ (a - y)) :=
    hc.comp_homeomorph (Homeomorph.subLeft a)
  have he := hF (fun y => κ (a - y)) ht htc
  have hl : (∫ y, f y * coordinateDerivative (fun z => κ (a - z)) i y) =
      -(scalarConvolution f (coordinateDerivative κ i) a) := by
    unfold scalarConvolution
    rw [convolution_def, ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [coordinateDerivative_const_sub (hκ.differentiable (by norm_num))]
      simp
  rw [hl] at he
  exact neg_injective he

theorem local_weak_mollify_eq
    {f F : Space n → ℝ} {i : Fin n}
    (hf : LocallyIntegrable f volume)
    (hF : HasLocalWeakCoordinateDerivative f F i) (k : ℕ) :
    coordinateDerivative (mollify k f) i = mollify k F := by
  funext x
  exact local_weak_scalarConvolution_eq hf hF
    ((mollifierKernel_contDiff k).of_le (by simp))
    (mollifierKernel_hasCompactSupport k) x

theorem local_weak_mollified_derivative_strong_L2
    {f F χ : Space n → ℝ} {i : Fin n}
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E))
    (hFloc : ∀ E, IsCompact E → MemLp F 2 (volume.restrict E))
    (hF : HasLocalWeakCoordinateDerivative f F i)
    (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    Tendsto (fun k => eLpNorm (fun x =>
      χ x * coordinateDerivative (mollify k f) i x - χ x * F x) 2 volume)
      atTop (𝓝 0) := by
  have hfloc := locallyIntegrable_of_memLp_two_on_compacts hf
  simp_rw [local_weak_mollify_eq hfloc hF]
  exact eLpNorm_compact_mul_mollify_sub_tendsto_zero hχ hc hFloc

end KLSConstantImprovement.ActualLocalRawWeakMollification405
#print axioms KLSConstantImprovement.ActualLocalRawWeakMollification405.local_weak_scalarConvolution_eq
#print axioms KLSConstantImprovement.ActualLocalRawWeakMollification405.local_weak_mollify_eq
#print axioms KLSConstantImprovement.ActualLocalRawWeakMollification405.local_weak_mollified_derivative_strong_L2
