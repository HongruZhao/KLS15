import ActualJointOptimality

/-! The previous actual-law coefficient bound applies to every genuine local
damped tilt after its constructed whitening. Hence the normalized lower
energy remains in the closed induction interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem covariance_Appell_ratio_mem_Icc_of_whitening {n k : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (hp : (covarianceMatrix μ).PosDef)
    (hadm : admissibleMeasure (whitenedMeasure μ))
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {h : ℝ} (hh : 0 < h)
    (hprevious : ∀ (ν : Measure (Space n)), admissibleMeasure ν → ∀ g : Space n → ℝ,
      MemLp g 2 ν → actualAppellEnergy ν g k ≤ h*(∫ x, (g x)^2 ∂ν)) :
    actualCovarianceAppellEnergy μ f k/(h*(∫ x, (f x)^2 ∂μ)) ∈ Icc (0 : ℝ) 1 := by
  have htest := actual_whitening_test_memLp hp hf
  have hb := hprevious (whitenedMeasure μ) hadm
    (fun y => f ((actualWhiteningEquiv μ hp).symm y)) htest
  rw [actualAppellEnergy_whitening hLC hp hf,actual_whitening_test_L2_energy μ hp f] at hb
  have hy : 0 ≤ actualCovarianceAppellEnergy μ f k := by
    rw [← actualAppellEnergy_whitening hLC hp hf]
    exact actualAppellEnergy_nonneg _ _ _
  have hg : 0 ≤ ∫ x, (f x)^2 ∂μ := integral_nonneg fun x => sq_nonneg _
  by_cases hgpos : 0 < ∫ x, (f x)^2 ∂μ
  · exact ⟨div_nonneg hy (mul_nonneg hh.le hg),
      (div_le_one (mul_pos hh hgpos)).mpr hb⟩
  · have hgzero : (∫ x, (f x)^2 ∂μ) = 0 := le_antisymm (le_of_not_gt hgpos) hg
    simp [hgzero]

 theorem exists_local_actual_damped_induction_ratio {n k : ℕ}
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (p : MvPolynomial (Fin n) ℝ) {h : ℝ} (hh : 0 < h)
    (hprevious : ∀ (ν : Measure (Space n)), admissibleMeasure ν → ∀ f : Space n → ℝ,
      MemLp f 2 ν → actualAppellEnergy ν f k ≤ h*(∫ x, (f x)^2 ∂ν)) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      actualCovarianceAppellEnergy (actualDampedTiltLaw μ z s) (polynomialEval p) k/
        (h*(∫ x, (polynomialEval p x)^2 ∂actualDampedTiltLaw μ z s)) ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨r,hr,hfamily⟩ := exists_local_actual_damped_whitening hμ
  refine ⟨r,hr,?_⟩
  intro z hz s hs
  obtain ⟨hprob,hsupp,hpos,hadm⟩ := hfamily z hz s hs
  letI : IsProbabilityMeasure (actualDampedTiltLaw μ z s) := hprob
  have hLC := actualDampedTiltLaw_logConcave hμ z hs
  exact covariance_Appell_ratio_mem_Icc_of_whitening hLC hpos hadm
    (polynomialEval_memLp_two hLC p) hh hprevious

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.exists_local_actual_damped_induction_ratio
