import KLSConstantImprovement.ActualCubicCreationJointBound
import KLSConstantImprovement.ActualCreationCubicSeed2388Cap

/-! A reusable original-law raw-observation-to-variance bridge and its
exact joint creation support. The accepted seed2388 cap sharpens the
previous joint constant while retaining all ordered tensor indices. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators ENNReal ContDiff
namespace KLSConstantImprovement.ActualCubicCreationJointRawSupport
open KLS KLS.DeterministicBridge KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25 KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
open ActualCubicPoincareFourthSector ActualCubicQuadraticRegression ActualCubicQuadraticDeficit
open ActualCubicCreationJointBound
variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem tensorPolynomial_variance_le_of_observation_cap {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (H : ℝ) (hH : 0  ≤  H)
    (hcap : ∀ {f : Space n → ℝ}, MemLp f 2 μ →
      actualAppellEnergy μ f 3  ≤  H*(∫ x,(f x)^2 ∂μ)) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ ≤ H*tensorSquare T := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let P := tensorPolynomial μ T
  let V := ProbabilityTheory.variance P μ
  let W := actualCubicNextArray μ P
  have hp := tensorPolynomial_variance_pairing hμ T
  change V=tripleSum (fun a b c => T a b c*W a b c) at hp
  have hcs := triple_pairing_sq_le T W
  rw [←hp,actualCubicNextArray_square] at hcs
  change V^2 ≤ tensorSquare T*actualAppellEnergy μ P 3 at hcs
  have he := hcap (tensorPolynomial_memLp hμ T)
  have hv : (∫ x,(P x)^2 ∂μ)=V := by
    have heq := ProbabilityTheory.variance_eq_sub (tensorPolynomial_memLp hμ T)
    rw [tensorPolynomial_centered hμ T] at heq
    simpa only [Pi.pow_apply,zero_pow (by norm_num : 2≠0),sub_zero,P,V] using heq.symm
  change actualAppellEnergy μ P 3  ≤  H*(∫ x,(P x)^2 ∂μ) at he
  rw [hv] at he
  have hN := CubicVarianceFourthSector.tensorSquare_nonneg T
  have hpaid := mul_le_mul_of_nonneg_left he hN
  have hV : 0 ≤ V := ProbabilityTheory.variance_nonneg _ _
  change V ≤ H*tensorSquare T
  by_cases hz : V=0
  · rw [hz]
    positivity
  · have hpos : 0<V := lt_of_le_of_ne hV (Ne.symm hz)
    have hsq : V*V ≤ V*(H*tensorSquare T) := by nlinarith [hcs,hpaid]
    exact (mul_le_mul_iff_of_pos_left hpos).mp hsq

theorem tensorPolynomial_variance_le_creation2388 {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n)) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ  ≤  (21492/25 : ℝ)*tensorSquare T := by
  apply tensorPolynomial_variance_le_of_observation_cap hμ T (21492/25) (by norm_num)
  intro f hf
  have he := actual_appell_energy_three_creation2388_le_integral hμ hf
  norm_num [CreationSeed2388.B] at he ⊢
  exact he

theorem tensorPolynomial_variance_add_ninety_creation_le_of_raw {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (H : ℝ) (hraw : ProbabilityTheory.variance (tensorPolynomial μ T) μ  ≤  H*tensorSquare T) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ +
      90*matrixFrobeniusSq (symmetricAnnihilation μ T)  ≤ 
        ((412/441 : ℝ)*1260+(29/441 : ℝ)*H)*tensorSquare T := by
  have hs := tensorPolynomial_rational_creation_support hμ T hT12 hT23
  have hf := (fourthContraction_bounds hμ T hT23).2
  have hp : ProbabilityTheory.variance (tensorPolynomial μ T) μ +
      (19845/206 : ℝ)*matrixFrobeniusSq (symmetricAnnihilation μ T)  ≤  1260*tensorSquare T := by
    nlinarith [hs,hf]
  linear_combination (29/441 : ℝ)*hraw+(412/441 : ℝ)*hp

theorem tensorPolynomial_variance_add_ninety_creation_le_creation2388 {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ +
      90*matrixFrobeniusSq (symmetricAnnihilation μ T)  ≤  (1511252/1225 : ℝ)*tensorSquare T := by
  have hj := tensorPolynomial_variance_add_ninety_creation_le_of_raw hμ T hT12 hT23
    (21492/25) (tensorPolynomial_variance_le_creation2388 hμ T)
  norm_num at hj ⊢
  exact hj

end KLSConstantImprovement.ActualCubicCreationJointRawSupport
#print axioms KLSConstantImprovement.ActualCubicCreationJointRawSupport.tensorPolynomial_variance_le_of_observation_cap
#print axioms KLSConstantImprovement.ActualCubicCreationJointRawSupport.tensorPolynomial_variance_le_creation2388
#print axioms KLSConstantImprovement.ActualCubicCreationJointRawSupport.tensorPolynomial_variance_add_ninety_creation_le_of_raw
#print axioms KLSConstantImprovement.ActualCubicCreationJointRawSupport.tensorPolynomial_variance_add_ninety_creation_le_creation2388
