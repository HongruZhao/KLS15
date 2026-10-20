import RetainedObservationGram
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! Keep a finite coupled observation budget as one positive operator.
The old sum of individual norm caps is a certified fallback, rather than
the definition of the new budget. No new universal numerical cap is assumed.+-/
noncomputable section
open InnerProductSpace ContinuousLinearMap
open scoped BigOperators ContDiff
namespace KLSImprovement.WeightedObservation
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {H E ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def weightedObservationGram (s : Finset ι) (w : ι → ℝ)
    (O : ι → H →L[ℝ] E) : H →L[ℝ] H :=
  ∑ i ∈ s, w i • ((O i).adjoint.comp (O i))

theorem weightedObservationGram_quadratic (s : Finset ι) (w : ι → ℝ)
    (O : ι → H →L[ℝ] E) (f : H) :
    inner ℝ (weightedObservationGram s w O f) f =
      ∑ i ∈ s, w i * ‖O i f‖^2 := by
  classical
  simp only [weightedObservationGram, sum_apply, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [smul_apply, real_inner_smul_left, comp_apply]
  have h := apply_norm_sq_eq_inner_adjoint_left (O i) f
  simp only [RCLike.re_to_real, comp_apply] at h
  rw [← h]

theorem weighted_observation_bound (s : Finset ι) (w : ι → ℝ)
    (O : ι → H →L[ℝ] E) (f : H) :
    (∑ i ∈ s, w i * ‖O i f‖^2) ≤
      ‖weightedObservationGram s w O‖ * ‖f‖^2 := by
  rw [← weightedObservationGram_quadratic]
  calc
    _ ≤ ‖weightedObservationGram s w O f‖ * ‖f‖ := real_inner_le_norm _ _
    _ ≤ (‖weightedObservationGram s w O‖ * ‖f‖) * ‖f‖ :=
      mul_le_mul_of_nonneg_right ((weightedObservationGram s w O).le_opNorm f)
        (norm_nonneg _)
    _ = _ := by ring

theorem weighted_gram_norm_le_sum (s : Finset ι) (w : ι → ℝ)
    (O : ι → H →L[ℝ] E) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ‖weightedObservationGram s w O‖ ≤ ∑ i ∈ s, w i * ‖O i‖^2 := by
  classical
  calc
    _ ≤ ∑ i ∈ s, ‖w i • ((O i).adjoint.comp (O i))‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i hi),
        ContinuousLinearMap.norm_adjoint_comp_self, pow_two]

/-- The retained norm never exceeds any already proved joint budget. -/
theorem weighted_gram_norm_le_budget (s : Finset ι) (w : ι → ℝ)
    (O : ι → H →L[ℝ] E) (hw : ∀ i ∈ s, 0 ≤ w i) {C : ℝ} (hC : 0 ≤ C)
    (hbudget : ∀ f : H, (∑ i ∈ s, w i * ‖O i f‖^2) ≤ C*‖f‖^2) :
    ‖weightedObservationGram s w O‖ ≤ C := by
  classical
  let Q := weightedObservationGram s w O
  have hs : Q.IsSymmetric := by
    intro x y
    change inner ℝ (Q x) y = inner ℝ x (Q y)
    simp only [Q, weightedObservationGram, sum_apply, sum_inner, inner_sum,
      smul_apply, real_inner_smul_left, real_inner_smul_right, comp_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [adjoint_inner_left, adjoint_inner_right]
  rw [Q.norm_eq_iSup_rayleighQuotient hs]
  apply ciSup_le
  intro f
  have hpos : 0 ≤ ∑ i ∈ s, w i * ‖O i f‖^2 :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
  change |inner ℝ (Q f) f / ‖f‖^2| ≤ C
  rw [show inner ℝ (Q f) f = ∑ i ∈ s, w i * ‖O i f‖^2 from
    weightedObservationGram_quadratic s w O f]
  rw [abs_of_nonneg (div_nonneg hpos (sq_nonneg _))]
  by_cases hf : f = 0
  · subst f
    simpa using hC
  · exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hf))).mpr (hbudget f)

end KLSImprovement.WeightedObservation

namespace KLSImprovement.WeightedObservation
open MeasureTheory Matrix KLS KLS.DeterministicBridgeIntegration
open KLSImprovement.ObservationGram
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Actual graded observations of the existing KLS15 operator pipeline. -/
def actualWeightedObservationGram
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hiso : IsIsotropic (potentialMeasure φ)) (K : ℝ) (M : ℕ) :
    GradedCenteredTensorHilbert hφ →L[ℝ] GradedCenteredTensorHilbert hφ :=
  weightedObservationGram (Finset.Icc 1 M) (fun m => K⁻¹^(m+1))
    (actualHeadObservation hφ hκ hlower hiso)

theorem actual_weighted_observation_bound
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hiso : IsIsotropic (potentialMeasure φ)) (K : ℝ) (M : ℕ)
    (f : GradedCenteredTensorHilbert hφ) :
    (∑ m ∈ Finset.Icc 1 M, K⁻¹^(m+1)*
      ‖actualHeadObservation hφ hκ hlower hiso m f‖^2) ≤
    ‖actualWeightedObservationGram hφ hκ hlower hiso K M‖*‖f‖^2 :=
  weighted_observation_bound _ _ _ f

/-- The old scalar coupled certificate controls the retained actual Gram,
so replacing C by this finite norm never worsens an existing valid budget. -/
theorem actual_weighted_gram_norm_le_coupled_budget
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hμ : admissibleMeasure (potentialMeasure φ))
    {K C : ℝ} (hK : 0 < K) (hC : 0 ≤ C)
    (hcoupled : ∀ (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)),
      ∑ d ∈ Finset.Icc 2 N, K⁻¹^d *
        KLS.DeterministicBridgeNext.actualAppellEnergy (potentialMeasure φ) f d /
          (d.factorial : ℝ)^2 ≤ C*‖f‖^2)
    (M : ℕ) :
    ‖actualWeightedObservationGram hφ hκ hlower hμ.isotropic K M‖ ≤ C := by
  apply weighted_gram_norm_le_budget _ _ _
    (fun m _ => pow_nonneg (inv_nonneg.mpr hK.le) _) hC
  intro f
  exact actual_joint_graded_observability hφ hκ hlower hμ hK hC hcoupled M f

end KLSImprovement.WeightedObservation

#print axioms KLSImprovement.WeightedObservation.weightedObservationGram_quadratic
#print axioms KLSImprovement.WeightedObservation.weighted_observation_bound
#print axioms KLSImprovement.WeightedObservation.weighted_gram_norm_le_sum
#print axioms KLSImprovement.WeightedObservation.weighted_gram_norm_le_budget
#print axioms KLSImprovement.WeightedObservation.actual_weighted_observation_bound
#print axioms KLSImprovement.WeightedObservation.actual_weighted_gram_norm_le_coupled_budget
