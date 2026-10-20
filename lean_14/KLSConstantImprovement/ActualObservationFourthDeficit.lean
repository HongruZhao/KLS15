import KLSConstantImprovement.ActualCubicQuadraticDeficit
import ActualAppellQuadraticSeed

/-! Retain the actual fourth deficit of the same second observation.
Every covariance belongs to the original law and the same unit L2 function.
This supplies a dimension-free observation-gap correlation; it does not
replace a slice deficit or assert the open universal additive gate.
Fresh source only; the sole merger owns all compilation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.OriginalUpperRecovery6ObservationDeficit
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open ActualCubicGradientEnergy ActualCubicQuadraticDeficit
open ActualCubicPoincareFourthSector
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def observationFourthDeficit {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  8*actualAppellEnergy μ f 2-
    ProbabilityTheory.variance (ActualCubicGradientEnergy.centeredQuadratic
      (quadraticCovarianceMatrix μ f)) μ

theorem actual_quadratic_observation_self_covariance {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    covariance (ActualCubicGradientEnergy.centeredQuadratic (quadraticCovarianceMatrix μ f)) f μ =
      actualAppellEnergy μ f 2 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hq := memLp_matrixQuadratic_of_coordinateProducts
    hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul (quadraticCovarianceMatrix μ f)
  rw [covariance_comm]
  unfold ActualCubicGradientEnergy.centeredQuadratic
  rw [covariance_sub_const_right (hq.integrable (by norm_num)),
    covariance_matrixQuadratic_eq_pairing hf hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul,
    actualAppellEnergy_two_eq_frobenius hμ hf]
  simp only [matrixFrobeniusSq,pow_two]

theorem observationFourthDeficit_nonneg {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    0 ≤ observationFourthDeficit μ f := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hb := centeredQuadratic_variance_le_eight hμ (quadraticCovarianceMatrix μ f)
    (quadraticCovarianceMatrix_isSymm μ f)
  rw [←actualAppellEnergy_two_eq_frobenius hμ hf] at hb
  exact sub_nonneg.mpr hb

theorem observationFourthDeficit_le_gap_unit {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x,(f x)^2 ∂μ)=1) :
    observationFourthDeficit μ f ≤ actualAppellEnergy μ f 2*(8-actualAppellEnergy μ f 2) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hq := centeredQuadratic_memLp hμ (quadraticCovarianceMatrix μ f)
  have hcs := covariance_sq_le_variance_mul_variance hq hf
  rw [actual_quadratic_observation_self_covariance hμ hf] at hcs
  have hfvar : ProbabilityTheory.variance f μ ≤ 1 := by
    rw [ProbabilityTheory.variance_eq_sub hf]
    change (∫ x,(f x)^2 ∂μ)-(∫ x,f x ∂μ)^2 ≤ 1
    rw [hunit]
    nlinarith [sq_nonneg (∫ x,f x ∂μ)]
  have hpaid := mul_le_mul_of_nonneg_left hfvar
    (ProbabilityTheory.variance_nonneg
      (ActualCubicGradientEnergy.centeredQuadratic (quadraticCovarianceMatrix μ f)) μ)
  unfold observationFourthDeficit
  nlinarith [hcs,hpaid]

theorem observationFourthDeficit_le_gap_Lp_unit {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) :
    observationFourthDeficit μ f ≤ actualAppellEnergy μ f 2*(8-actualAppellEnergy μ f 2) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  apply observationFourthDeficit_le_gap_unit hμ (Lp.memLp f)
  rw [←actualLp_norm_sq_eq_integral,hunit]
  norm_num

end KLSConstantImprovement.OriginalUpperRecovery6ObservationDeficit
#print axioms KLSConstantImprovement.OriginalUpperRecovery6ObservationDeficit.actual_quadratic_observation_self_covariance
#print axioms KLSConstantImprovement.OriginalUpperRecovery6ObservationDeficit.observationFourthDeficit_nonneg
#print axioms KLSConstantImprovement.OriginalUpperRecovery6ObservationDeficit.observationFourthDeficit_le_gap_unit
#print axioms KLSConstantImprovement.OriginalUpperRecovery6ObservationDeficit.observationFourthDeficit_le_gap_Lp_unit
