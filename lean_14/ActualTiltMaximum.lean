import ActualAppellWhiteningEnergy
import ActualJointMaximizerStationarity

/-! The constructed genuine joint maximum bounds its actual tilted family.
Centering/whitening, covariance energy invariance and L² transport are internal. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration KLSBelow25 KLS.TensorEnergy
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 def actualCovarianceAppellQuotient {n : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) (k : ℕ) (h : ℝ) (φ : ℝ → ℝ) : ℝ :=
  actualCovarianceAppellEnergy μ f (k+1)/
    ((∫ x, (f x)^2 ∂μ)*φ (actualCovarianceAppellEnergy μ f k/(h*(∫ x, (f x)^2 ∂μ))))

 theorem covarianceMatrix_eq_one_of_isotropic {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hiso : IsIsotropic μ) : covarianceMatrix μ = 1 := by
  ext i j
  rw [covarianceMatrix_apply hiso.memLp_id,
    covariance_eq_sub (hiso.memLp_coordinate i) (hiso.memLp_coordinate j),
    hiso.integral_coordinate i,hiso.integral_coordinate j,zero_mul,sub_zero]
  simpa only [Pi.mul_apply,Matrix.one_apply] using hiso.integral_coordinate_mul i j

 theorem actualCovarianceAppellEnergy_isotropic {n r : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hiso : IsIsotropic μ) (f : Space n → ℝ) :
    actualCovarianceAppellEnergy μ f r = actualAppellEnergy μ f r := by
  rw [actualCovarianceAppellEnergy,covarianceMatrix_eq_one_of_isotropic hiso,tensorMetric_one]
  simp only [actualAppellEnergy,dotProduct,pow_two]

 theorem actual_covariance_quotient_eq_whitened {n k : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (hp : (covarianceMatrix μ).PosDef) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (h : ℝ) (φ : ℝ → ℝ) :
    actualCovarianceAppellQuotient μ f k h φ =
      coefficientQuotient (fullClassAppellLinearMap hLC.whitenedMeasure k)
        (fullClassAppellLinearMap hLC.whitenedMeasure (k+1)) h φ
        ((actual_whitening_test_memLp hp hf).toLp (fun y => f ((actualWhiteningEquiv μ hp).symm y))) := by
  let g := (actual_whitening_test_memLp hp hf).toLp
    (fun y => f ((actualWhiteningEquiv μ hp).symm y))
  have hg : (g : Space n → ℝ) =ᵐ[whitenedMeasure μ]
      fun y => f ((actualWhiteningEquiv μ hp).symm y) :=
    (actual_whitening_test_memLp hp hf).coeFn_toLp
  have hn : ‖g‖^2 = ∫ x, (f x)^2 ∂μ := by
    rw [actualLp_norm_sq_eq_integral]
    calc
      _ = ∫ y, (f ((actualWhiteningEquiv μ hp).symm y))^2 ∂whitenedMeasure μ :=
        integral_congr_ae (hg.fun_comp (fun t : ℝ => t^2))
      _ = _ := actual_whitening_test_L2_energy μ hp f
  change _ = ‖fullClassAppellTensor (k+1) g‖^2/
    (‖g‖^2*φ (‖fullClassAppellTensor k g‖^2/(h*‖g‖^2)))
  rw [← actualAppellEnergy_eq_norm_sq,← actualAppellEnergy_eq_norm_sq,
    actualAppellEnergy_congr_ae hg,actualAppellEnergy_congr_ae hg,
    actualAppellEnergy_whitening hLC hp hf,actualAppellEnergy_whitening hLC hp hf,hn]
  rfl

/-- The found joint maximum applies to every genuine local tilted law after
its internally constructed whitening. This is the actual global-family
maximum premise required for the theta/damping differential test. -/
 theorem exists_actual_joint_maximizer_tilt_maximum {n k : ℕ}
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n)))
    {h : ℝ} (hh : 0 < h) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc 0 1))
    (hφpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < φ u)
    (hφanti : AntitoneOn φ (Icc (0 : ℝ) 1))
    (hprevious : ∀ (μ : Measure (Space n)), admissibleMeasure μ → ∀ f : Space n → ℝ,
      MemLp f 2 μ → actualAppellEnergy μ f k ≤ h*(∫ x, (f x)^2 ∂μ)) :
    ∃ (μ : ProbabilityMeasure (Space n)) (hμ : admissibleMeasure (μ : Measure (Space n)))
      (c : DegreeIndex n (k+1) → ℝ),
      (∫ x, (polynomialEval (boundedDegreePolynomial c) x)^2 ∂(μ : Measure (Space n))) = 1 ∧
      ∃ r : ℝ, 0 < r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
        actualCovarianceAppellQuotient (actualDampedTiltLaw (μ : Measure (Space n)) z s)
          (polynomialEval (boundedDegreePolynomial c)) k h φ ≤
        actualCovarianceAppellQuotient (μ : Measure (Space n))
          (polynomialEval (boundedDegreePolynomial c)) k h φ := by
  obtain ⟨z₀,hz₀,hmax⟩ := exists_actual_joint_L2_quotient_maximizer
    hμ₀ hh hφ hφpos hφanti hprevious
  have hn : (∫ x, (polynomialEval (boundedDegreePolynomial z₀.2) x)^2
      ∂(z₀.1 : Measure (Space n))) = 1 := by
    exact (polynomialCoefficientEnergy_eq_integral_sq _ hz₀.1 z₀.2).symm.trans hz₀.2
  obtain ⟨r,hr,hfamily⟩ := exists_local_actual_damped_whitening hz₀.1
  refine ⟨z₀.1,hz₀.1,z₀.2,hn,r,hr,?_⟩
  intro z hz s hs
  obtain ⟨hprob,hsupp,hpos,hadm⟩ := hfamily z hz s hs
  letI : IsProbabilityMeasure (actualDampedTiltLaw (z₀.1 : Measure (Space n)) z s) := hprob
  have hLC := actualDampedTiltLaw_logConcave hz₀.1 z hs
  have hf := polynomialEval_memLp_two hLC (boundedDegreePolynomial z₀.2)
  let ν : ProbabilityMeasure (Space n) := ⟨_,hadm.isProb⟩
  have hm := hmax ν hadm
    ((actual_whitening_test_memLp hpos hf).toLp
      (fun y => polynomialEval (boundedDegreePolynomial z₀.2)
        ((actualWhiteningEquiv (actualDampedTiltLaw (z₀.1 : Measure (Space n)) z s) hpos).symm y)))
  rw [← actual_covariance_quotient_eq_whitened hLC hpos hf] at hm
  have he : actualCovarianceAppellQuotient (z₀.1 : Measure (Space n))
      (polynomialEval (boundedDegreePolynomial z₀.2)) k h φ =
      actualNormalizedAppellQuotient (z₀.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial z₀.2)) k h φ := by
    unfold actualCovarianceAppellQuotient actualNormalizedAppellQuotient
    rw [actualCovarianceAppellEnergy_isotropic hz₀.1.isotropic,
      actualCovarianceAppellEnergy_isotropic hz₀.1.isotropic,hn,mul_one,one_mul]
  exact hm.trans_eq he.symm

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_covariance_quotient_eq_whitened
#print axioms KLS.DeterministicBridgeNext.exists_actual_joint_maximizer_tilt_maximum
