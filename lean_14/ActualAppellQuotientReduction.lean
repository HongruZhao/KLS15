import ActualPolynomialAppellProjection
import ActualPolynomialQuotientMaximizer

/-! Algebra and actual L² normalization for the homogeneous Appell quotient.
The tensor energy here is identified with the literal ordered coordinate sum. -/
noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem actualAppellEnergy_eq_norm_sq {n r : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    actualAppellEnergy μ f r = ‖fullClassAppellTensor r f‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

 theorem actualAppellEnergy_congr_ae {n r : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ]
    {f g : Space n → ℝ} (hfg : f =ᵐ[μ] g) :
    actualAppellEnergy μ f r = actualAppellEnergy μ g r := by
  unfold actualAppellEnergy
  exact Finset.sum_congr rfl fun a _ =>
    congrArg (fun t : ℝ => t^2) (actualAppellCoefficient_congr_ae hfg r a)

 theorem polynomialLp_norm_sq {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (p : MvPolynomial (Fin n) ℝ) :
    ‖polynomialLp hLC p‖^2 = ∫ x, (polynomialEval p x)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,inner_polynomialLp_eq_integral]
  apply integral_congr_ae
  filter_upwards [polynomialLp_coe hLC p] with x hx
  rw [hx,pow_two]

 theorem polynomialLp_combination_smul {n : ℕ} {I : Type*} [Fintype I]
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (e : I → (Fin n →₀ ℕ)) (c : I → ℝ) (a : ℝ) :
    polynomialLp hLC (polynomialCombination e (a • c)) =
      a • polynomialLp hLC (polynomialCombination e c) := by
  rw [← polynomialCoefficientLp_eq,← polynomialCoefficientLp_eq,map_smul]

 theorem polynomialCoefficientEnergy_eq_norm_sq {n : ℕ} {I : Type*} [Fintype I]
    (e : I → (Fin n →₀ ℕ)) {μ : ProbabilityMeasure (Space n)}
    (hμ : admissibleMeasure (μ : Measure (Space n))) (c : I → ℝ) :
    polynomialCoefficientEnergy e μ c =
      ‖polynomialLp hμ.logConcave (polynomialCombination e c)‖^2 := by
  rw [polynomialCoefficientEnergy_eq_integral_sq e hμ,polynomialLp_norm_sq]

 theorem coefficientQuotient_smul {V W Z : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (B : V →ₗ[ℝ] W) (C : V →ₗ[ℝ] Z) (h : ℝ) (φ : ℝ → ℝ)
    (f : V) {a : ℝ} (ha : a ≠ 0) :
    coefficientQuotient B C h φ (a • f) = coefficientQuotient B C h φ f := by
  simp only [coefficientQuotient,map_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have he : a^2*‖B f‖^2/(h*(a^2*‖f‖^2)) = ‖B f‖^2/(h*‖f‖^2) := by
    rw [show h*(a^2*‖f‖^2) = a^2*(h*‖f‖^2) by ring,mul_div_mul_left _ _ (pow_ne_zero 2 ha)]
  rw [he]
  rw [show a^2*‖f‖^2*φ (‖B f‖^2/(h*‖f‖^2)) =
    a^2*(‖f‖^2*φ (‖B f‖^2/(h*‖f‖^2))) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 ha)]

 theorem polynomial_normalized_quotient_eq {n k : ℕ}
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (c : DegreeIndex n (k+1) → ℝ) (hunit : polynomialCoefficientEnergy (degreeExponent n (k+1)) μ c = 1)
    (h : ℝ) (φ : ℝ → ℝ) :
    actualNormalizedAppellQuotient (μ : Measure (Space n))
      (polynomialEval (boundedDegreePolynomial c)) k h φ =
    coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
      (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ
      (polynomialLp hμ.logConcave (boundedDegreePolynomial c)) := by
  have hnorm : ‖polynomialLp hμ.logConcave (boundedDegreePolynomial c)‖^2 = 1 := by
    change ‖polynomialLp hμ.logConcave (polynomialCombination (degreeExponent n (k+1)) c)‖^2 = 1
    rw [← polynomialCoefficientEnergy_eq_norm_sq (degreeExponent n (k+1)) hμ]
    exact hunit
  simp only [coefficientQuotient,fullClassAppellLinearMap,LinearMap.coe_mk,AddHom.coe_mk,
    hnorm,mul_one,one_mul]
  rw [← actualAppellEnergy_eq_norm_sq,← actualAppellEnergy_eq_norm_sq,
    actualAppellEnergy_congr_ae (polynomialLp_coe hμ.logConcave _),
    actualAppellEnergy_congr_ae (polynomialLp_coe hμ.logConcave _)]
  rfl

 theorem normalize_actual_polynomial_pair {n d : ℕ}
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (c : DegreeIndex n d → ℝ)
    (hc : polynomialLp hμ.logConcave (boundedDegreePolynomial c) ≠ 0) :
    ∃ a : ℝ, a ≠ 0 ∧
      (μ,a • c) ∈ normalizedPolynomialPairs (degreeExponent n d) := by
  let a := ‖polynomialLp hμ.logConcave (boundedDegreePolynomial c)‖⁻¹
  have hn := norm_pos_iff.mpr hc
  have ha : a ≠ 0 := inv_ne_zero hn.ne'
  refine ⟨a,ha,hμ,?_⟩
  rw [polynomialCoefficientEnergy_eq_norm_sq _ hμ,polynomialLp_combination_smul]
  change ‖a • polynomialLp hμ.logConcave (boundedDegreePolynomial c)‖^2 = 1
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  rw [inv_mul_cancel₀ hn.ne']
  norm_num

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.polynomial_normalized_quotient_eq
#print axioms KLS.DeterministicBridgeNext.normalize_actual_polynomial_pair
