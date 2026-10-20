import KLSConstantImprovement.ActualCubicQuadraticDeficit
import ActualCreationCubicSeed239Cap

/-! A fifth-free original-law cubic/creation joint bound.
Two rational mixed-polynomial tests give a linear supporting inequality.
Combining it with the retained original-law cubic observation cap proves
V + 90 ||Sym A||² ≤ (302262/245) ||T||², with all ordered indices retained.
The universal Poincare endpoint remains unchanged. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators ENNReal ContDiff
namespace KLSConstantImprovement.ActualCubicCreationJointBound
open KLS KLS.DeterministicBridge KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25 KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
open ActualCubicPoincareFourthSector ActualCubicQuadraticRegression ActualCubicQuadraticDeficit
variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem tensorPolynomial_variance_le_retained_raw {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n)) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ≤(4302/5 : ℝ)*tensorSquare T := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let P := tensorPolynomial μ T
  let V := ProbabilityTheory.variance P μ
  let W := actualCubicNextArray μ P
  have hp := tensorPolynomial_variance_pairing hμ T
  change V=tripleSum (fun a b c => T a b c*W a b c) at hp
  have hcs := triple_pairing_sq_le T W
  rw [←hp,actualCubicNextArray_square] at hcs
  change V^2≤tensorSquare T*actualAppellEnergy μ P 3 at hcs
  have he := actual_appell_energy_three_creation239_le_integral hμ (tensorPolynomial_memLp hμ T)
  have hv : (∫ x,(P x)^2 ∂μ)=V := by
    have heq := ProbabilityTheory.variance_eq_sub (tensorPolynomial_memLp hμ T)
    rw [tensorPolynomial_centered hμ T] at heq
    simpa only [Pi.pow_apply,zero_pow (by norm_num : 2≠0),sub_zero,P,V] using heq.symm
  change actualAppellEnergy μ P 3≤(36*CreationSeed239.B)*(∫ x,(P x)^2 ∂μ) at he
  rw [hv] at he
  norm_num [CreationSeed239.B] at he
  have hN := CubicVarianceFourthSector.tensorSquare_nonneg T
  have hpaid := mul_le_mul_of_nonneg_left he hN
  have hV : 0≤V := ProbabilityTheory.variance_nonneg _ _
  change V≤(4302/5 : ℝ)*tensorSquare T
  by_cases hz : V=0
  · rw [hz]
    positivity
  · have hpos : 0<V := lt_of_le_of_ne hV (Ne.symm hz)
    have hsq : V*V≤V*((4302/5 : ℝ)*tensorSquare T) := by nlinarith [hcs,hpaid]
    exact (mul_le_mul_iff_of_pos_left hpos).mp hsq

theorem rational_mixed_test_support {V Q R g D : ℝ}
    (hp : V+(189/206 : ℝ)^2*g-2*(189/206 : ℝ)*D≤
      (287/20 : ℝ)*(9*Q+4*(189/206 : ℝ)^2*R-12*(189/206 : ℝ)*R))
    (hv : 0≤V+(525/103 : ℝ)^2*g-2*(525/103 : ℝ)*D)
    (hg : g≤8*R) : V+(19845/206 : ℝ)*R≤(315/2 : ℝ)*Q := by
  nlinarith [hp,hv,hg]

theorem tensorPolynomial_rational_creation_support_posDim {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      (19845/206 : ℝ)*matrixFrobeniusSq (symmetricAnnihilation μ T)≤
        (315/2 : ℝ)*(fourthContraction μ T+2*tensorSquare T) := by
  let K := symmetricAnnihilation μ T
  have hK := symmetricAnnihilation_isSymm μ T
  have hC : LongPrefixCubicBellmanEndpoint.bound≤(287/20 : ℝ) := by
    norm_num [LongPrefixCubicBellmanEndpoint.bound]
  have hp := quadraticPerturbation_poincare_of_bound_le hn hμ T hT12 hT23 K hK
    (189/206) (287/20) hC
  rw [quadraticGradientPairing_symmetricAnnihilation] at hp
  have hv := ProbabilityTheory.variance_nonneg (quadraticPerturbation μ T K (525/103)) μ
  rw [quadraticPerturbation_variance hμ T K (525/103)] at hv
  exact rational_mixed_test_support hp hv (centeredQuadratic_variance_le_eight hμ K hK)

theorem tensorPolynomial_rational_creation_support {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      (19845/206 : ℝ)*matrixFrobeniusSq (symmetricAnnihilation μ T)≤
        (315/2 : ℝ)*(fourthContraction μ T+2*tensorSquare T) := by
  cases n with
  | zero =>
      have hz : tensorPolynomial μ T=(fun _ => 0) := by
        funext x
        simp [tensorPolynomial]
      rw [hz]
      change ProbabilityTheory.variance (0 : Space 0→ℝ) μ+_≤_
      rw [ProbabilityTheory.variance_zero]
      simp [matrixFrobeniusSq,fourthContraction,tensorSquare,square,tripleSum]
  | succ n =>
      exact tensorPolynomial_rational_creation_support_posDim (by omega) hμ T hT12 hT23

theorem tensorPolynomial_variance_add_ninety_creation_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      90*matrixFrobeniusSq (symmetricAnnihilation μ T)≤(302262/245 : ℝ)*tensorSquare T := by
  have hs := tensorPolynomial_rational_creation_support hμ T hT12 hT23
  have hf := (fourthContraction_bounds hμ T hT23).2
  have hr := tensorPolynomial_variance_le_retained_raw hμ T
  have hp : ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      (19845/206 : ℝ)*matrixFrobeniusSq (symmetricAnnihilation μ T)≤1260*tensorSquare T := by
    nlinarith [hs,hf]
  linear_combination (29/441 : ℝ)*hr+(412/441 : ℝ)*hp

theorem tensorPolynomial_variance_add_ninety_creation_le_12339over10 {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      90*matrixFrobeniusSq (symmetricAnnihilation μ T)≤(12339/10 : ℝ)*tensorSquare T := by
  exact (tensorPolynomial_variance_add_ninety_creation_le hμ T hT12 hT23).trans
    (mul_le_mul_of_nonneg_right (by norm_num : (302262/245 : ℝ)≤12339/10)
      (CubicVarianceFourthSector.tensorSquare_nonneg T))

end KLSConstantImprovement.ActualCubicCreationJointBound
#print axioms KLSConstantImprovement.ActualCubicCreationJointBound.tensorPolynomial_variance_le_retained_raw
#print axioms KLSConstantImprovement.ActualCubicCreationJointBound.rational_mixed_test_support
#print axioms KLSConstantImprovement.ActualCubicCreationJointBound.tensorPolynomial_rational_creation_support_posDim
#print axioms KLSConstantImprovement.ActualCubicCreationJointBound.tensorPolynomial_rational_creation_support
#print axioms KLSConstantImprovement.ActualCubicCreationJointBound.tensorPolynomial_variance_add_ninety_creation_le
#print axioms KLSConstantImprovement.ActualCubicCreationJointBound.tensorPolynomial_variance_add_ninety_creation_le_12339over10
