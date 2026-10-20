import KLSConstantImprovement.ActualObservationFourthDeficit
import KLSConstantImprovement.ActualAffineSameTestCreationCubicSeed238452Cap
import FullClassAppellStationarity

/-! Exact original L2 residual after the same quadratic observation.
The test, law, quadratic coefficient, and full cubic array are retained.
No spectral gap or positive-deficit curvature estimate is assumed.
Fresh source only; sole merger owns compilation and accepted sources. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.OriginalUpperRecovery6ObservationProjection
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open ActualCubicGradientEnergy ActualCubicAffineRegression ActualCubicPoincareFourthSector
open ActualDeficitTensorBounds OriginalUpperRecovery6ObservationDeficit
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def observationQuadratic {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : Space n → ℝ :=
  ActualCubicGradientEnergy.centeredQuadratic (quadraticCovarianceMatrix μ f)

def observationResidual {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) (x : Space n) : ℝ :=
  f x-(1/8 : ℝ)*observationQuadratic μ f x

theorem observationResidual_memLp {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    MemLp (observationResidual μ f) 2 μ :=
  hf.sub ((centeredQuadratic_memLp hμ (quadraticCovarianceMatrix μ f)).const_mul (1/8 : ℝ))

theorem observationResidual_integral_sq_unit {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x,(f x)^2 ∂μ)=1) :
    (∫ x,(observationResidual μ f x)^2 ∂μ) =
      1-actualAppellEnergy μ f 2/8-observationFourthDeficit μ f/64 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let q := observationQuadratic μ f
  have hq : MemLp q 2 μ := centeredQuadratic_memLp hμ (quadraticCovarianceMatrix μ f)
  have hmean : (∫ x,q x ∂μ)=0 := centeredQuadratic_mean_zero hμ (quadraticCovarianceMatrix μ f)
  have hvariance : ProbabilityTheory.variance q μ=(∫ x,(q x)^2 ∂μ) := by
    rw [ProbabilityTheory.variance_eq_sub hq,hmean]
    simp only [zero_pow (by norm_num : 2≠0),sub_zero,Pi.pow_apply]
  have hpair : (∫ x,f x*q x ∂μ)=actualAppellEnergy μ f 2 := by
    have hc : covariance q f μ=actualAppellEnergy μ f 2 :=
      actual_quadratic_observation_self_covariance hμ hf
    rw [covariance_eq_sub hq hf,hmean,zero_mul,sub_zero] at hc
    calc
      _ = (∫ x,q x*f x ∂μ) := integral_congr_ae (Eventually.of_forall fun x => by ring)
      _ = _ := hc
  have he : (fun x => (observationResidual μ f x)^2)=
      fun x => (f x)^2+(1/64 : ℝ)*(q x)^2-(1/4 : ℝ)*(f x*q x) := by
    funext x
    dsimp only [observationResidual,q]
    ring
  have hsum : Integrable (fun x => (f x)^2+(1/64 : ℝ)*(q x)^2) μ := by
    convert hf.integrable_sq.add (hq.integrable_sq.const_mul (1/64 : ℝ)) using 1
  have hprod : Integrable (fun x => (1/4 : ℝ)*(f x*q x)) μ := by
    simpa only [Pi.mul_apply] using (hf.integrable_mul hq).const_mul (1/4 : ℝ)
  rw [he,integral_sub hsum hprod,
    integral_add (f := fun x => (f x)^2) (g := fun x => (1/64 : ℝ)*(q x)^2)
      hf.integrable_sq (hq.integrable_sq.const_mul (1/64 : ℝ)),
    integral_const_mul,integral_const_mul,hunit,hpair,←hvariance]
  unfold observationFourthDeficit
  change 1+(1/64 : ℝ)*ProbabilityTheory.variance q μ-(1/4 : ℝ)*actualAppellEnergy μ f 2 =
    1-actualAppellEnergy μ f 2/8-(8*actualAppellEnergy μ f 2-ProbabilityTheory.variance q μ)/64
  ring

theorem observationResidual_integral_sq_le_gap_unit {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x,(f x)^2 ∂μ)=1) :
    (∫ x,(observationResidual μ f x)^2 ∂μ) ≤ (8-actualAppellEnergy μ f 2)/8 := by
  rw [observationResidual_integral_sq_unit hμ hf hunit]
  have hd := observationFourthDeficit_nonneg hμ hf
  nlinarith

theorem observation_saturation_eq_quadratic_ae {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x,(f x)^2 ∂μ)=1) (hY : actualAppellEnergy μ f 2=8) :
    f =ᵐ[μ] (fun x => (1/8 : ℝ)*observationQuadratic μ f x) := by
  have hi := observationResidual_integral_sq_le_gap_unit hμ hf hunit
  rw [hY] at hi
  have hz : (∫ x,(observationResidual μ f x)^2 ∂μ)=0 := by
    have hp : (0 : ℝ) ≤ (∫ x,(observationResidual μ f x)^2 ∂μ) :=
      integral_nonneg (μ := μ) fun x => sq_nonneg (observationResidual μ f x)
    norm_num at hi
    exact le_antisymm hi hp
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => sq_nonneg (observationResidual μ f x))
    (observationResidual_memLp hμ hf).integrable_sq).mp hz
  filter_upwards [hae] with x hx
  have he := sq_eq_zero_iff.mp hx
  dsimp only [observationResidual] at he
  linarith

theorem observationResidual_cubic_array {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualCubicNextArray μ (observationResidual μ f) =
      fun i j k => actualCubicNextArray μ f i j k-
        (1/8 : ℝ)*actualCubicNextArray μ (observationQuadratic μ f) i j k := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hq : MemLp (observationQuadratic μ f) 2 μ :=
    centeredQuadratic_memLp hμ (quadraticCovarianceMatrix μ f)
  funext i j k
  unfold actualCubicNextArray observationResidual
  rw [actualAppellCoefficient_sub hμ.logConcave hf (hq.const_mul (1/8 : ℝ)),
    actualAppellCoefficient_const_mul hμ.logConcave hq]

theorem observationResidual_cubic_energy_le_gap_unit {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x,(f x)^2 ∂μ)=1) :
    actualAppellEnergy μ (observationResidual μ f) 3 ≤
      (536517/5000 : ℝ)*(8-actualAppellEnergy μ f 2) := by
  have hcap := actual_appell_energy_three_affine_same_test_creation238452_le_integral
    hμ (observationResidual_memLp hμ hf)
  have hH : (36*AffineSameTestCreationSeed238452.B : ℝ)=536517/625 := by
    norm_num [AffineSameTestCreationSeed238452.B]
  rw [hH] at hcap
  have hgap := observationResidual_integral_sq_le_gap_unit hμ hf hunit
  have hp := mul_le_mul_of_nonneg_left hgap (by norm_num : (0 : ℝ)≤536517/625)
  nlinarith

theorem observation_cubic_array_distance_le_gap_unit {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x,(f x)^2 ∂μ)=1) :
    tensorSquare (fun i j k => actualCubicNextArray μ f i j k-
      (1/8 : ℝ)*actualCubicNextArray μ (observationQuadratic μ f) i j k) ≤
      (536517/5000 : ℝ)*(8-actualAppellEnergy μ f 2) := by
  rw [←observationResidual_cubic_array hμ hf]
  unfold tensorSquare
  rw [actualCubicNextArray_square]
  exact observationResidual_cubic_energy_le_gap_unit hμ hf hunit

end KLSConstantImprovement.OriginalUpperRecovery6ObservationProjection
#print axioms KLSConstantImprovement.OriginalUpperRecovery6ObservationProjection.observationResidual_integral_sq_unit
#print axioms KLSConstantImprovement.OriginalUpperRecovery6ObservationProjection.observationResidual_integral_sq_le_gap_unit
#print axioms KLSConstantImprovement.OriginalUpperRecovery6ObservationProjection.observation_saturation_eq_quadratic_ae
#print axioms KLSConstantImprovement.OriginalUpperRecovery6ObservationProjection.observationResidual_cubic_array
#print axioms KLSConstantImprovement.OriginalUpperRecovery6ObservationProjection.observationResidual_cubic_energy_le_gap_unit
#print axioms KLSConstantImprovement.OriginalUpperRecovery6ObservationProjection.observation_cubic_array_distance_le_gap_unit
