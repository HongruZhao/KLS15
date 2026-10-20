import KLS.WeightedSmoothVariance

/-! A scalar-test combined energy budget gives the actual variance bound
using the proved smooth diffusion-range density. Hessian and curvature
are retained together. The budget is an explicit analytic hypothesis;
no Poisson optimizer, Riesz-field existence, or universal numerical
combined-energy estimate is asserted. This file uses the identity metric
and a finite C2 full-space potential. -/

open MeasureTheory ProbabilityTheory InnerProductSpace Filter Set KLS
open scoped ContDiff Topology

noncomputable section
namespace KLSConstantImprovement.ActualCombinedEnergyVarianceReduction

variable {n : ℕ}

def CombinedGradientBochnerBudget (φ f : Space n → ℝ) (K : ℝ) : Prop :=
  ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
    2 * (∫ x, inner ℝ (gradient f x) (gradient g x) ∂potentialMeasure φ) -
      (∫ x, hessianSquare g x ∂potentialMeasure φ) -
      (∫ x, hessianGradientForm φ g x ∂potentialMeasure φ) ≤ K

theorem compact_combined_objective_eq {φ f g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    2 * (∫ x, f x * (-weightedDiffusion φ g x) ∂potentialMeasure φ) -
      (∫ x, (weightedDiffusion φ g x) ^ 2 ∂potentialMeasure φ) =
    2 * (∫ x, inner ℝ (gradient f x) (gradient g x) ∂potentialMeasure φ) -
      (∫ x, hessianSquare g x ∂potentialMeasure φ) -
      (∫ x, hessianGradientForm φ g x ∂potentialMeasure φ) := by
  have hi : (∫ x, f x * (-weightedDiffusion φ g x) ∂potentialMeasure φ) =
      ∫ x, inner ℝ (gradient f x) (gradient g x) ∂potentialMeasure φ := by
    calc
      _ = -(∫ x, f x * weightedDiffusion φ g x ∂potentialMeasure φ) := by
        rw [← integral_neg]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = _ := by
        rw [integral_mul_weightedDiffusion_of_hasCompactSupport
          (hφ.of_le (by norm_num)) hf (hg.of_le (by norm_num)) hc]
        ring
  have hb := integral_weightedDiffusion_sq_eq_sum hφ hg
    (bochnerIntegrability_of_hasCompactSupport hφ hg hc)
  rw [hi, hb]
  ring

/-- Actual smooth-law variance reduction, with range density discharged.
The all-test combined budget is precisely the remaining hypothesis. -/
theorem variance_le_of_combined_budget_smooth {φ f : Space n → ℝ} {K : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp f 2 (potentialMeasure φ))
    (hbudget : CombinedGradientBochnerBudget φ f K) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤ K := by
  let F : Lp ℝ 2 (potentialMeasure φ) := hf2.toLp f
  have hF : (F : Space n → ℝ) =ᵐ[potentialMeasure φ] f := hf2.coeFn_toLp
  have hclosure : CenteredL2.center (potentialMeasure φ) F ∈
      closure (compactDiffusionRange φ : Set (Lp ℝ 2 (potentialMeasure φ))) :=
    diffusionRangeDense_of_contDiff hφ _ (CenteredL2.integral_center _ F)
  have hbound : ∀ v ∈ compactDiffusionRange φ,
      2 * inner ℝ F v - ‖v‖ ^ 2 ≤ K := by
    rintro v ⟨g, hg, hc, hv⟩
    have hi : inner ℝ F v =
        ∫ x, f x * (-weightedDiffusion φ g x) ∂potentialMeasure φ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hF, hv] with x hx hy
      simp [hx, hy, RCLike.inner_apply, mul_comm]
    have hn : ‖v‖ ^ 2 =
        ∫ x, (weightedDiffusion φ g x) ^ 2 ∂potentialMeasure φ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      simp [hx, RCLike.inner_apply, pow_two]
    rw [hi, hn, compact_combined_objective_eq hφ hf hg hc]
    exact hbudget g hg hc
  have he := CenteredL2.variance_le_of_center_mem_closure
    (potentialMeasure φ) hclosure hbound
  rwa [ProbabilityTheory.variance_congr hF] at he

end KLSConstantImprovement.ActualCombinedEnergyVarianceReduction
#print axioms KLSConstantImprovement.ActualCombinedEnergyVarianceReduction.compact_combined_objective_eq
#print axioms KLSConstantImprovement.ActualCombinedEnergyVarianceReduction.variance_le_of_combined_budget_smooth
