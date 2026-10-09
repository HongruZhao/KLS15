import ActualAppellJointContinuity

/-! Actual normalized polynomial quotient attainment. The law class and
polynomial space are literal; the only coefficient inequality premise is the
previous-order induction bound needed to keep the barrier argument in [0,1]. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem normalizedPolynomialPairs_nonempty_of_admissible {n d : ℕ}
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n))) :
    (normalizedPolynomialPairs (degreeExponent n d)).Nonempty := by
  let c : DegreeIndex n d → ℝ := fun s => (1 : MvPolynomial (Fin n) ℝ).coeff s.val
  refine ⟨(μ,c),hμ,?_⟩
  rw [polynomialCoefficientEnergy_eq_integral_sq _ hμ]
  change (∫ x, (polynomialEval (boundedDegreePolynomial c) x)^2
    ∂(μ : Measure (Space n))) = 1
  have hc : boundedDegreePolynomial c = 1 :=
    boundedDegreePolynomial_representation 1 (by simp)
  rw [hc]
  simp [polynomialEval]

 def actualNormalizedAppellQuotient {n : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) (k : ℕ) (h : ℝ) (φ : ℝ → ℝ) : ℝ :=
  actualAppellEnergy μ f (k+1)/φ (actualAppellEnergy μ f k/h)

 theorem actualNormalizedAppellQuotient_continuousOn {n k : ℕ} {h : ℝ} (hh : 0 < h)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 1))
    (hφpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < φ u)
    (hprevious : ∀ (μ : Measure (Space n)), admissibleMeasure μ → ∀ f : Space n → ℝ,
      MemLp f 2 μ → actualAppellEnergy μ f k ≤ h*(∫ x, (f x)^2 ∂μ)) :
    ContinuousOn (fun z : ProbabilityMeasure (Space n) × (DegreeIndex n (k+1) → ℝ) =>
      actualNormalizedAppellQuotient (z.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial z.2)) k h φ)
      (normalizedPolynomialPairs (degreeExponent n (k+1))) := by
  let S := normalizedPolynomialPairs (degreeExponent n (k+1))
  have hS : S ⊆ (admissibleProbabilityLaws n) ×ˢ univ := fun z hz => ⟨hz.1,mem_univ _⟩
  have hE (r : ℕ) : ContinuousOn
      (fun z : ProbabilityMeasure (Space n) × (DegreeIndex n (k+1) → ℝ) =>
        actualAppellEnergy (z.1 : Measure (Space n))
          (polynomialEval (boundedDegreePolynomial z.2)) r) S :=
    (actualAppellPolynomial_energy_continuousOn (degreeExponent n (k+1))).mono hS
  have harg (z : ProbabilityMeasure (Space n) × (DegreeIndex n (k+1) → ℝ)) (hz : z ∈ S) :
      actualAppellEnergy (z.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial z.2)) k/h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (actualAppellEnergy_nonneg _ _ _) hh.le
    · have hb := hprevious (z.1 : Measure (Space n)) hz.1
        (polynomialEval (boundedDegreePolynomial z.2))
        (polynomialEval_memLp_two hz.1.logConcave _)
      have hnorm : (∫ x, (polynomialEval (boundedDegreePolynomial z.2) x)^2
          ∂(z.1 : Measure (Space n))) = 1 := by
        change (∫ x, (polynomialEval (polynomialCombination (degreeExponent n (k+1)) z.2) x)^2
          ∂(z.1 : Measure (Space n))) = 1
        rw [← polynomialCoefficientEnergy_eq_integral_sq (degreeExponent n (k+1)) hz.1]
        exact hz.2
      rw [hnorm,mul_one] at hb
      exact (div_le_one hh).mpr hb
  have hden : ContinuousOn (fun z : ProbabilityMeasure (Space n) × (DegreeIndex n (k+1) → ℝ) =>
      φ (actualAppellEnergy (z.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial z.2)) k/h)) S :=
    hφ.comp ((hE k).div_const h) harg
  exact (hE (k+1)).div hden fun z hz => (hφpos _ (harg z hz)).ne'

/-- The genuine quotient attains a joint maximum over all actual admissible
laws and all normalized polynomials of degree at most k+1. No maximizer
property is assumed. -/
 theorem exists_actual_normalized_polynomial_quotient_maximizer
    {n k : ℕ} {μ₀ : ProbabilityMeasure (Space n)}
    (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n)))
    {h : ℝ} (hh : 0 < h) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 1))
    (hφpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < φ u)
    (hprevious : ∀ (μ : Measure (Space n)), admissibleMeasure μ → ∀ f : Space n → ℝ,
      MemLp f 2 μ → actualAppellEnergy μ f k ≤ h*(∫ x, (f x)^2 ∂μ)) :
    ∃ z ∈ normalizedPolynomialPairs (degreeExponent n (k+1)),
      ∀ w ∈ normalizedPolynomialPairs (degreeExponent n (k+1)),
        actualNormalizedAppellQuotient (w.1 : Measure (Space n))
          (polynomialEval (boundedDegreePolynomial w.2)) k h φ ≤
        actualNormalizedAppellQuotient (z.1 : Measure (Space n))
          (polynomialEval (boundedDegreePolynomial z.2)) k h φ := by
  exact (isCompact_boundedDegree_normalizedPolynomialPairs n (k+1)).exists_isMaxOn
    (normalizedPolynomialPairs_nonempty_of_admissible hμ₀)
    (actualNormalizedAppellQuotient_continuousOn hh hφ hφpos hprevious)

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.exists_actual_normalized_polynomial_quotient_maximizer
