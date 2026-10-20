import ContractedAppellPolynomials
import ActualAppellObservationOperators
import KLSConstantImprovement.RawCubicWeightedBudget

/-! Exact polynomial/observation duality on the entire admissible law class.
The only analytic hypothesis is a variance cap for the same actual cubic
polynomial and fully symmetric coefficient tensor. No pilot, compact-law,
field approximation, or orthogonality premise is substituted.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSConstantImprovement.CubicVarianceObservationTransfer
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def cubicPolynomial {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : (Fin 3→Fin n)→ℝ) : Space n→ℝ :=
  letI : IsProbabilityMeasure μ := hμ.isProb
  polynomialEval (contractedAppellPolynomial hμ 3 T)

def UniversalCubicPolynomialVarianceBound (H : ℝ) : Prop :=
  ∀ {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : (Fin 3→Fin n)→ℝ), CoordinateTensorSymmetric T →
      ProbabilityTheory.variance (cubicPolynomial hμ T) μ ≤ H*(∑ a,T a^2)

theorem cubicPolynomial_memLp {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : (Fin 3→Fin n)→ℝ) : MemLp (cubicPolynomial hμ T) 2 μ := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  exact polynomialEval_memLp_two hμ.logConcave _

theorem cubicPolynomial_centered {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : (Fin 3→Fin n)→ℝ) : (∫ x,cubicPolynomial hμ T x ∂μ)=0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  exact contractedAppellPolynomial_integral_zero hμ (by norm_num) T

theorem cubicPolynomial_coefficient_pairing {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    (∫ x,cubicPolynomial hμ (actualAppellCoefficient μ f 3) x*f x ∂μ)=
      actualAppellEnergy μ f 3 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  simpa only [cubicPolynomial,actualAppellEnergy,pow_two] using
    contractedAppellPolynomial_pairing hμ 3 (actualAppellCoefficient μ f 3) hf

theorem cubicPolynomial_coefficient_covariance {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    covariance (cubicPolynomial hμ (actualAppellCoefficient μ f 3)) f μ=
      actualAppellEnergy μ f 3 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  rw [covariance_eq_sub (cubicPolynomial_memLp hμ _) hf,
    cubicPolynomial_centered,zero_mul,sub_zero]
  exact cubicPolynomial_coefficient_pairing hμ hf

theorem rawCubicBound_of_polynomial_variance {H : ℝ} (hH : 0 ≤ H)
    (hcap : UniversalCubicPolynomialVarianceBound H) :
    RawCubicWeightedBudget.UniversalRawCubicBound H := by
  intro n μ hμ f hf
  letI : IsProbabilityMeasure μ := hμ.isProb
  let T := actualAppellCoefficient μ f 3
  let N := actualAppellEnergy μ f 3
  have hN:0 ≤ N := actualAppellEnergy_nonneg _ _ _
  have hV := hcap hμ T (actualAppellCoefficient_symmetric hμ.logConcave hf)
  change ProbabilityTheory.variance (cubicPolynomial hμ T) μ ≤ H*N at hV
  have hCS := covariance_sq_le_variance_mul_variance (cubicPolynomial_memLp hμ T) hf
  rw [cubicPolynomial_coefficient_covariance hμ hf] at hCS
  change N^2 ≤ ProbabilityTheory.variance (cubicPolynomial hμ T) μ*
    ProbabilityTheory.variance f μ at hCS
  have hp := mul_le_mul_of_nonneg_right hV (ProbabilityTheory.variance_nonneg f μ)
  have hVF : ProbabilityTheory.variance f μ ≤ ∫ x,(f x)^2 ∂μ := by
    rw [ProbabilityTheory.variance_eq_sub hf]
    exact sub_le_self _ (sq_nonneg _)
  have hq := mul_le_mul_of_nonneg_left hVF (mul_nonneg hH hN)
  have hsq : N*N ≤ (H*(∫ x,(f x)^2 ∂μ))*N := by
    nlinarith [hCS.trans (hp.trans hq)]
  by_cases hzero:N=0
  · change N ≤ _
    rw [hzero]
    exact mul_nonneg hH (integral_nonneg fun _=>sq_nonneg _)
  · have hpos:0 < N := lt_of_le_of_ne hN (Ne.symm hzero)
    exact (mul_le_mul_iff_of_pos_right hpos).mp hsq

theorem rawCubic336_of_polynomial_variance
    (hcap : UniversalCubicPolynomialVarianceBound 336) :
    RawCubicWeightedBudget.UniversalRawCubicBound 336 :=
  rawCubicBound_of_polynomial_variance (by norm_num) hcap

end KLSConstantImprovement.CubicVarianceObservationTransfer
#print axioms KLSConstantImprovement.CubicVarianceObservationTransfer.cubicPolynomial_memLp
#print axioms KLSConstantImprovement.CubicVarianceObservationTransfer.cubicPolynomial_centered
#print axioms KLSConstantImprovement.CubicVarianceObservationTransfer.cubicPolynomial_coefficient_pairing
#print axioms KLSConstantImprovement.CubicVarianceObservationTransfer.cubicPolynomial_coefficient_covariance
#print axioms KLSConstantImprovement.CubicVarianceObservationTransfer.rawCubicBound_of_polynomial_variance
#print axioms KLSConstantImprovement.CubicVarianceObservationTransfer.rawCubic336_of_polynomial_variance
