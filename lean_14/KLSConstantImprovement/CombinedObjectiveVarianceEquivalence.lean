import KLSConstantImprovement.ActualCombinedEnergyVarianceReduction

/-! Exact scientific strength of the identity-metric compact-test gate.
The actual objective is bounded by variance through a Hilbert square.
Together with the accepted range-density passage, its all-test budget
is equivalent to the variance bound. No new numerical estimate follows.
The potential is finite C2 on the full Euclidean space, the law is a
probability, and the target is an actual C1 L2 function. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Filter Set KLS
open scoped ContDiff Topology
namespace KLSConstantImprovement.CombinedObjectiveVarianceEquivalence
open ActualCombinedEnergyVarianceReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem objective_eq_square_deficit (f v : E) :
    2 * inner ℝ f v - ‖v‖ ^ 2 = ‖f‖ ^ 2 - ‖f-v‖ ^ 2 := by
  rw [norm_sub_sq_real]
  ring

theorem objective_le_square_norm (f v : E) :
    2 * inner ℝ f v - ‖v‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [objective_eq_square_deficit]
  exact sub_le_self _ (sq_nonneg _)

theorem compact_combined_objective_le_variance {n : ℕ} {φ f g : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp f 2 (potentialMeasure φ))
    (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    2 * (∫ x, inner ℝ (gradient f x) (gradient g x) ∂potentialMeasure φ) -
      (∫ x, hessianSquare g x ∂potentialMeasure φ) -
      (∫ x, hessianGradientForm φ g x ∂potentialMeasure φ) ≤
        ProbabilityTheory.variance f (potentialMeasure φ) := by
  let F : Lp ℝ 2 (potentialMeasure φ) := hf2.toLp f
  let hA := (memLp_weightedDiffusion_of_hasCompactSupport hφ hg hc).neg
  let v : Lp ℝ 2 (potentialMeasure φ) :=
    hA.toLp (fun x => -weightedDiffusion φ g x)
  have hF : (F : Space n → ℝ) =ᵐ[potentialMeasure φ] f := hf2.coeFn_toLp
  have hv : (v : Space n → ℝ) =ᵐ[potentialMeasure φ]
      (fun x => -weightedDiffusion φ g x) := hA.coeFn_toLp
  have hv0 : (∫ x,v x ∂potentialMeasure φ) = 0 :=
    integral_eq_zero_of_mem_compactDiffusionRange hφ (toLp_neg_weightedDiffusion_mem hφ hg hc)
  have hcenter : inner ℝ (CenteredL2.center (potentialMeasure φ) F) v = inner ℝ F v := by
    rw [CenteredL2.center, inner_sub_left, real_inner_smul_left,
      CenteredL2.inner_oneLp, hv0]
    ring
  have hi : inner ℝ F v =
      ∫ x,f x * (-weightedDiffusion φ g x) ∂potentialMeasure φ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hF,hv] with x hx hy
    simp [hx,hy,RCLike.inner_apply,mul_comm]
  have hn : ‖v‖ ^ 2 = ∫ x,(weightedDiffusion φ g x)^2 ∂potentialMeasure φ := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    simp [hx,RCLike.inner_apply,pow_two]
  have hb := objective_le_square_norm (CenteredL2.center (potentialMeasure φ) F) v
  rw [hcenter,hi,hn,CenteredL2.norm_center_sq_eq_variance,
    ProbabilityTheory.variance_congr hF,compact_combined_objective_eq hφ hf hg hc] at hb
  exact hb

theorem combined_budget_iff_variance_bound {n : ℕ} {φ f : Space n → ℝ} {K : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp f 2 (potentialMeasure φ)) :
    CombinedGradientBochnerBudget φ f K ↔
      ProbabilityTheory.variance f (potentialMeasure φ) ≤ K := by
  constructor
  · exact variance_le_of_combined_budget_smooth hφ hf hf2
  · intro hbudget g hg hc
    exact (compact_combined_objective_le_variance hφ hf hf2 hg hc).trans hbudget

end KLSConstantImprovement.CombinedObjectiveVarianceEquivalence
#print axioms KLSConstantImprovement.CombinedObjectiveVarianceEquivalence.objective_eq_square_deficit
#print axioms KLSConstantImprovement.CombinedObjectiveVarianceEquivalence.objective_le_square_norm
#print axioms KLSConstantImprovement.CombinedObjectiveVarianceEquivalence.compact_combined_objective_le_variance
#print axioms KLSConstantImprovement.CombinedObjectiveVarianceEquivalence.combined_budget_iff_variance_bound
