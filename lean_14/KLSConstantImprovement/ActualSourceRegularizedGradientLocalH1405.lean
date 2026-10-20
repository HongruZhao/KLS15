import KLSConstantImprovement.ActualSourceRegularizedInteriorH2405
import EllipticPdes.Extension.C1Test

/-!
Local raw H1 regularity of the ordinary gradient of the actual regularized
inverse. The second derivative representatives are constructed from H2,
extended as genuine whole-space L2 classes, and their weak identities are
proved for every compact C1 test inside a neighborhood of a given compact
set. This is the domain needed by compact flux products and vector Bochner.
-/
noncomputable section
open MeasureTheory Set Filter Matrix Metric InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceRegularizedGradientLocalH1405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyForm405
open ActualSourceRegularizedInteriorH2405
open EllipticPdes.Sobolev EllipticPdes.Embedding EllipticPdes.Regularity EllipticPdes.Extension
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_regularizedOrdinaryGradient_local_rawH1
    (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ) {ε : ℝ} (hε : 0 < ε)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    {K : Set (Space n)} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ K ⊆ ball (0 : Space n) R ∧
      ∃ D : Fin n → Fin n → Lp ℝ 2 (volume : Measure (Space n)),
        ∀ i j (ψ : Space n → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ ball (0 : Space n) R →
          (∫ x, weightedH1Derivative d.potential i
            (regularizedOrdinaryInverse d hn k hε g) x * coordinateDerivative ψ j x) =
            -(∫ x, D i j x * ψ x) := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : Space n)
  let E : Set (Space n) := closedBall (0 : Space n) R
  have hE : IsCompact E := isCompact_closedBall _ _
  let U := regularizedOrdinaryInverse d hn k hε g
  choose w hw using fun i j => regularizedOrdinaryInverse_local_second_weak_derivative
    d hn k hε g hg hE i j
  let D (i j : Fin n) : Lp ℝ 2 (volume : Measure (Space n)) := extendL2 hE.measurableSet (w i j)
  have hDE (i j : Fin n) : (D i j : Space n → ℝ) =ᵐ[volume.restrict E] (w i j : Space n → ℝ) := by
    filter_upwards [ae_restrict_of_ae (coeFn_extendL2 hE.measurableSet (w i j)),
      ae_restrict_mem hE.measurableSet] with x hx hxE
    change extendL2 hE.measurableSet (w i j) x = _
    rw [hx, indicator_of_mem hxE]
  have hweakE (i : Fin n) : HasWeakGradOn E (weightedH1Derivative d.potential i U)
      (fun j x => D i j x) := by
    intro ψ hψ hψc hψE j
    have he := hw i j ψ hψ hψc hψE
    have hr : (∫ x in E, D i j x * ψ x) = ∫ x in E, w i j x * ψ x :=
      integral_congr_ae ((hDE i j).fun_mul EventuallyEq.rfl)
    rw [← hr] at he
    exact he
  letI : IsFiniteMeasure ((volume : Measure (Space n)).restrict (ball (0 : Space n) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hpI (i : Fin n) : IntegrableOn (weightedH1Derivative d.potential i U)
      (ball (0 : Space n) R) volume := by
    have hp := weightedH1Derivative_memLp_restrict d.source_C1.continuous U i hE
    exact (hp.mono_measure (Measure.restrict_mono_set volume ball_subset_closedBall)).integrable (by norm_num)
  have hDI (i j : Fin n) : IntegrableOn (fun x => D i j x) (ball (0 : Space n) R) volume :=
    ((Lp.memLp (D i j)).restrict _).integrable (by norm_num)
  refine ⟨R, hR, hKR, D, ?_⟩
  intro i j ψ hψ hψc hψB
  have hweakB : HasWeakGradOn (ball (0 : Space n) R) (weightedH1Derivative d.potential i U)
      (fun j x => D i j x) := HasWeakGradOn.mono ball_subset_closedBall (hweakE i)
  have he := hasWeakGradOn_contDiffOne isOpen_ball (hpI i) (hDI i) hweakB hψ hψc hψB j
  have hl : (∫ x in ball (0 : Space n) R, weightedH1Derivative d.potential i U x * partialD j ψ x) =
      ∫ x, weightedH1Derivative d.potential i U x * coordinateDerivative ψ j x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : coordinateDerivative ψ j x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (hψB (tsupport_coordinateDerivative_subset ψ j h)))
    change weightedH1Derivative d.potential i U x * coordinateDerivative ψ j x = 0
    rw [hz, mul_zero]
  have hr : (∫ x in ball (0 : Space n) R, D i j x * ψ x) = ∫ x, D i j x * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [show ψ x = 0 from image_eq_zero_of_notMem_tsupport (fun h => hx (hψB h)), mul_zero]
  rwa [hl, hr] at he

end KLSConstantImprovement.ActualSourceRegularizedGradientLocalH1405
#print axioms KLSConstantImprovement.ActualSourceRegularizedGradientLocalH1405.exists_regularizedOrdinaryGradient_local_rawH1
