import ActualTiltMaximum

/-! The same constructed actual joint maximizer satisfies both optimality
relations: every L² test-function first variation and the actual law-family
maximum on a two-sided tilt / one-sided damping neighborhood. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem actual_covariance_polynomial_quotient_isotropic {n k : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (p : MvPolynomial (Fin n) ℝ) (h : ℝ) (φ : ℝ → ℝ) :
    actualCovarianceAppellQuotient μ (polynomialEval p) k h φ =
      coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
        (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ (polynomialLp hμ.logConcave p) := by
  unfold actualCovarianceAppellQuotient
  rw [actualCovarianceAppellEnergy_isotropic hμ.isotropic,
    actualCovarianceAppellEnergy_isotropic hμ.isotropic,← polynomialLp_norm_sq hμ.logConcave p]
  change _ = ‖fullClassAppellTensor (k+1) (polynomialLp hμ.logConcave p)‖^2/
    (‖polynomialLp hμ.logConcave p‖^2*φ
      (‖fullClassAppellTensor k (polynomialLp hμ.logConcave p)‖^2/
        (h*‖polynomialLp hμ.logConcave p‖^2)))
  rw [← actualAppellEnergy_eq_norm_sq,← actualAppellEnergy_eq_norm_sq,
    actualAppellEnergy_congr_ae (polynomialLp_coe hμ.logConcave p),
    actualAppellEnergy_congr_ae (polynomialLp_coe hμ.logConcave p)]

 theorem actual_polynomial_joint_max_tilt_maximum {n k d : ℕ}
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (c : DegreeIndex n d → ℝ) (h : ℝ) (φ : ℝ → ℝ)
    (hmax : ∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν : Measure (Space n)))
      (g : Lp ℝ 2 (ν : Measure (Space n))),
      coefficientQuotient (fullClassAppellLinearMap hν.logConcave k)
        (fullClassAppellLinearMap hν.logConcave (k+1)) h φ g ≤
      coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
        (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ
        (polynomialLp hμ.logConcave (boundedDegreePolynomial c))) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      actualCovarianceAppellQuotient (actualDampedTiltLaw (μ : Measure (Space n)) z s)
        (polynomialEval (boundedDegreePolynomial c)) k h φ ≤
      actualCovarianceAppellQuotient (μ : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial c)) k h φ := by
  obtain ⟨r,hr,hfamily⟩ := exists_local_actual_damped_whitening hμ
  refine ⟨r,hr,?_⟩
  intro z hz s hs
  obtain ⟨hprob,hsupp,hpos,hadm⟩ := hfamily z hz s hs
  letI : IsProbabilityMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s) := hprob
  have hLC := actualDampedTiltLaw_logConcave hμ z hs
  have hf := polynomialEval_memLp_two hLC (boundedDegreePolynomial c)
  let ν : ProbabilityMeasure (Space n) := ⟨_,hadm.isProb⟩
  have hm := hmax ν hadm
    ((actual_whitening_test_memLp hpos hf).toLp
      (fun y => polynomialEval (boundedDegreePolynomial c)
        ((actualWhiteningEquiv (actualDampedTiltLaw (μ : Measure (Space n)) z s) hpos).symm y)))
  rw [← actual_covariance_quotient_eq_whitened hLC hpos hf] at hm
  exact hm.trans_eq (actual_covariance_polynomial_quotient_isotropic hμ _ h φ).symm

 theorem exists_actual_joint_maximizer_both_optimalities {n k : ℕ}
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n)))
    {h : ℝ} (hh : 0 < h) {φ φ' : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc 0 1))
    (hφpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < φ u)
    (hφanti : AntitoneOn φ (Icc (0 : ℝ) 1))
    (hφderiv : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' u) u)
    (hprevious : ∀ (μ : Measure (Space n)), admissibleMeasure μ → ∀ f : Space n → ℝ,
      MemLp f 2 μ → actualAppellEnergy μ f k ≤ h*(∫ x, (f x)^2 ∂μ)) :
    ∃ (μ : ProbabilityMeasure (Space n)) (hμ : admissibleMeasure (μ : Measure (Space n)))
      (c : DegreeIndex n (k+1) → ℝ),
      let f := polynomialLp hμ.logConcave (boundedDegreePolynomial c)
      ‖f‖ = 1 ∧
      (∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν : Measure (Space n)))
        (g : Lp ℝ 2 (ν : Measure (Space n))),
        coefficientQuotient (fullClassAppellLinearMap hν.logConcave k)
          (fullClassAppellLinearMap hν.logConcave (k+1)) h φ g ≤
        coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
          (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ f) ∧
      (∀ ell : Lp ℝ 2 (μ : Measure (Space n)),
        inner ℝ (fullClassAppellTensor (k+1) f) (fullClassAppellTensor (k+1) ell)+
          ‖fullClassAppellTensor (k+1) f‖^2*
            ((-φ' (‖fullClassAppellTensor k f‖^2/h))/φ (‖fullClassAppellTensor k f‖^2/h))/h*
            inner ℝ (fullClassAppellTensor k f) (fullClassAppellTensor k ell) =
        ‖fullClassAppellTensor (k+1) f‖^2*
          (1+(‖fullClassAppellTensor k f‖^2/h)*
            ((-φ' (‖fullClassAppellTensor k f‖^2/h))/φ (‖fullClassAppellTensor k f‖^2/h)))*
          inner ℝ f ell) ∧
      ∃ r : ℝ, 0 < r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
        actualCovarianceAppellQuotient (actualDampedTiltLaw (μ : Measure (Space n)) z s)
          (polynomialEval (boundedDegreePolynomial c)) k h φ ≤
        actualCovarianceAppellQuotient (μ : Measure (Space n))
          (polynomialEval (boundedDegreePolynomial c)) k h φ := by
  obtain ⟨μ,hμ,c,hunit,hmax,hstat⟩ := exists_actual_joint_maximizer_stationarity
    hμ₀ hh hφ hφpos hφanti hφderiv hprevious
  exact ⟨μ,hμ,c,hunit,hmax,hstat,actual_polynomial_joint_max_tilt_maximum hμ c h φ hmax⟩

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.exists_actual_joint_maximizer_both_optimalities
