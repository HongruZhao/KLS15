import KLSConstantImprovement.ActualWeightedL2PairingContinuity
import KLS.LocalWeakDerivativeUniqueness
import KLS.WeakMomentLipschitzInverseTests

/-! Closure of genuine raw local weak derivatives under actual local strong
L2 limits. No global Sobolev or operator-core assertion is used. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualLocalRawWeakClosure405
open KLS ActualWeightedL2PairingContinuity
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem local_weak_derivative_of_strong_L2_limits
    {f F : ℕ → Space n → ℝ} {u U : Space n → ℝ} {i : Fin n}
    (hf : ∀ k E, IsCompact E → MemLp (f k) 2 (volume.restrict E))
    (hF : ∀ k E, IsCompact E → MemLp (F k) 2 (volume.restrict E))
    (hu : ∀ E, IsCompact E → MemLp u 2 (volume.restrict E))
    (hU : ∀ E, IsCompact E → MemLp U 2 (volume.restrict E))
    (hweak : ∀ k, HasLocalWeakCoordinateDerivative (f k) (F k) i)
    (hlim : ∀ E, IsCompact E → Tendsto
      (fun k => eLpNorm (f k - u) 2 (volume.restrict E)) atTop (𝓝 0))
    (hDlim : ∀ E, IsCompact E → Tendsto
      (fun k => eLpNorm (F k - U) 2 (volume.restrict E)) atTop (𝓝 0)) :
    HasLocalWeakCoordinateDerivative u U i := by
  intro ψ hψ hc
  let E := tsupport ψ
  have hE : IsCompact E := hc
  have hdψ : MemLp (coordinateDerivative ψ i) 2 (volume.restrict E) :=
    memLp_continuous_on_compact
      (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous hE
  have hψ2 : MemLp ψ 2 (volume.restrict E) := memLp_continuous_on_compact hψ.continuous hE
  have hzero (b : Space n → ℝ) :
      Tendsto (fun _k : ℕ => eLpNorm (b - b) 2 (volume.restrict E)) atTop (𝓝 0) := by
    simp only [sub_self, eLpNorm_zero]
    exact tendsto_const_nhds
  have hl := tendsto_integral_mul_of_weighted_L2 (fun k => hf k E hE) (fun _ => hdψ)
    (hu E hE) hdψ (hlim E hE) (hzero (coordinateDerivative ψ i))
  have hr := tendsto_integral_mul_of_weighted_L2 (fun k => hF k E hE) (fun _ => hψ2)
    (hU E hE) hψ2 (hDlim E hE) (hzero ψ)
  have hleft (b : Space n → ℝ) :
      (∫ x in E, b x * coordinateDerivative ψ i x) =
        ∫ x, b x * coordinateDerivative ψ i x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hd : coordinateDerivative ψ i x = 0 :=
      image_eq_zero_of_notMem_tsupport fun ht => hx (tsupport_coordinateDerivative_subset ψ i ht)
    rw [hd, mul_zero]
  have hright (b : Space n → ℝ) : (∫ x in E, b x * ψ x) = ∫ x, b x * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hl' : Tendsto (fun k => ∫ x, f k x * coordinateDerivative ψ i x)
      atTop (𝓝 (∫ x, u x * coordinateDerivative ψ i x)) := by
    simpa only [hleft] using hl
  have hr' : Tendsto (fun k => ∫ x, F k x * ψ x)
      atTop (𝓝 (∫ x, U x * ψ x)) := by
    simpa only [hright] using hr
  exact tendsto_nhds_unique hl' (hr'.neg.congr fun k => (hweak k ψ hψ hc).symm)

end KLSConstantImprovement.ActualLocalRawWeakClosure405
#print axioms KLSConstantImprovement.ActualLocalRawWeakClosure405.local_weak_derivative_of_strong_L2_limits
