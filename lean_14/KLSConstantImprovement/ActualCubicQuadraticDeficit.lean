import KLSConstantImprovement.ActualCubicQuadraticRegression
/-! Literal mixed cubic/quadratic tests on the original admissible law.
The derivative, variance, mixed energy, and Poincare deficit are computed
for the same polynomial P_T - s q_B; no moment identity is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators ENNReal ContDiff
namespace KLSConstantImprovement.ActualCubicQuadraticDeficit
open KLS KLS.DeterministicBridge KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
open ActualCubicPoincareFourthSector ActualCubicAffineRegression QuadraticCovarianceCharge
open ActualCubicQuadraticRegression
variable {n : ℕ}
set_option maxHeartbeats 5500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem centeredQuadratic_variance_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    ProbabilityTheory.variance (ActualCubicGradientEnergy.centeredQuadratic B) μ=
      ProbabilityTheory.variance (matrixQuadratic B) μ := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  unfold ActualCubicGradientEnergy.centeredQuadratic
  exact variance_sub_const (memLp_matrixQuadratic_of_coordinateProducts
    hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul B).aestronglyMeasurable (Matrix.trace B)

theorem centeredQuadratic_variance_le_eight {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    ProbabilityTheory.variance (ActualCubicGradientEnergy.centeredQuadratic B) μ≤8*matrixFrobeniusSq B := by
  rw [centeredQuadratic_variance_eq hμ B]
  exact (hμ.quadraticVarianceEight_unconditional B hB).2

theorem cubic_quadratic_covariance_sq_le {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (B : Matrix (Fin n) (Fin n) ℝ) :
    (covariance (tensorPolynomial μ T) (ActualCubicGradientEnergy.centeredQuadratic B) μ)^2≤
      ProbabilityTheory.variance (tensorPolynomial μ T) μ*
        ProbabilityTheory.variance (ActualCubicGradientEnergy.centeredQuadratic B) μ := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  exact covariance_sq_le_variance_mul_variance (tensorPolynomial_memLp hμ T)
    (centeredQuadratic_memLp hμ B)

theorem quadraticPerturbation_poincare_of_bound_le {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (s C : ℝ)
    (hC : LongPrefixCubicBellmanEndpoint.bound≤C) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      s^2*ProbabilityTheory.variance (ActualCubicGradientEnergy.centeredQuadratic B) μ-
      2*s*covariance (tensorPolynomial μ T) (ActualCubicGradientEnergy.centeredQuadratic B) μ ≤
    C*(9*(fourthContraction μ T+2*tensorSquare T)+
      4*s^2*matrixFrobeniusSq B-12*s*quadraticGradientPairing μ T B) := by
  have henergy := quadraticPerturbation_gradient_energy hμ T hT12 hT23 B hB s
  have hE : 0≤9*(fourthContraction μ T+2*tensorSquare T)+
      4*s^2*matrixFrobeniusSq B-12*s*quadraticGradientPairing μ T B := by
    rw [←henergy.2]
    exact integral_nonneg fun _ => sq_nonneg _
  exact (quadraticPerturbation_poincare hn hμ T hT12 hT23 B hB s).trans
    (mul_le_mul_of_nonneg_right hC hE)

theorem nonnegative_quadratic_discriminant {a b c : ℝ}
    (h : ∀ s : ℝ,0≤a+2*s*b+s^2*c) : b^2≤a*c := by
  have hp : ∀ s : ℝ,0≤c*(s*s)+(2*b)*s+a := by
    intro s
    nlinarith [h s]
  have hd := discrim_le_zero hp
  simp only [discrim] at hd
  nlinarith

theorem cubic_quadratic_deficit_covariance_sq_le {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (C : ℝ)
    (hC : LongPrefixCubicBellmanEndpoint.bound≤C) :
    (6*C*quadraticGradientPairing μ T B-
      covariance (tensorPolynomial μ T) (ActualCubicGradientEnergy.centeredQuadratic B) μ)^2≤
      (9*C*(fourthContraction μ T+2*tensorSquare T)-ProbabilityTheory.variance (tensorPolynomial μ T) μ)*
        (4*C*matrixFrobeniusSq B-ProbabilityTheory.variance (ActualCubicGradientEnergy.centeredQuadratic B) μ) := by
  have hp : ∀ s : ℝ,0≤
      (9*C*(fourthContraction μ T+2*tensorSquare T)-ProbabilityTheory.variance (tensorPolynomial μ T) μ)+
      2*s*(covariance (tensorPolynomial μ T) (ActualCubicGradientEnergy.centeredQuadratic B) μ-
        6*C*quadraticGradientPairing μ T B)+
      s^2*(4*C*matrixFrobeniusSq B-ProbabilityTheory.variance (ActualCubicGradientEnergy.centeredQuadratic B) μ) := by
    intro s
    nlinarith [quadraticPerturbation_poincare_of_bound_le hn hμ T hT12 hT23 B hB s C hC]
  have hd := nonnegative_quadratic_discriminant hp
  nlinarith

theorem quadraticGradientPairing_symmetricAnnihilation (μ : Measure (Space n))
    (T : Array3 (Fin n)) :
    quadraticGradientPairing μ T (symmetricAnnihilation μ T)=
      matrixFrobeniusSq (symmetricAnnihilation μ T) := by
  simp only [quadraticGradientPairing,matrixFrobeniusSq,pow_two]

theorem symmetricAnnihilation_square_le_fourth_add_two {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n)) :
    matrixFrobeniusSq (symmetricAnnihilation μ T)≤fourthContraction μ T+2*tensorSquare T := by
  let A := annihilation (actualThirdCubicArray μ) T
  have hp (i j : Fin n) : ((A i j+A j i)/2)^2≤((A i j)^2+(A j i)^2)/2 := by
    nlinarith [sq_nonneg (A i j-A j i)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
  have ht : (∑ i,∑ j,(A j i)^2)=∑ i,∑ j,(A i j)^2 := Finset.sum_comm
  simp only [Finset.sum_add_distrib,←Finset.sum_div,ht] at hs
  have hb := ActualDeficitBesselBound.annihilationSquare_le_fourth_add_two hμ T
  change (∑ i,∑ j,(A i j)^2)≤fourthContraction μ T+2*tensorSquare T at hb
  change (∑ i,∑ j,((A i j+A j i)/2)^2)≤_
  linarith

theorem original_symmetricAnnihilation_joint_constraints {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (C : ℝ) (hC : LongPrefixCubicBellmanEndpoint.bound≤C) :
    let Q := fourthContraction μ T+2*tensorSquare T
    let V := ProbabilityTheory.variance (tensorPolynomial μ T) μ
    let K := symmetricAnnihilation μ T
    let R := matrixFrobeniusSq K
    let g := ProbabilityTheory.variance (ActualCubicGradientEnergy.centeredQuadratic K) μ
    let D := covariance (tensorPolynomial μ T) (ActualCubicGradientEnergy.centeredQuadratic K) μ
    0≤R ∧ R≤Q ∧ 0≤g ∧ g≤8*R ∧ 0≤V ∧ V≤9*C*Q ∧
      D^2≤V*g ∧ (6*C*R-D)^2≤(9*C*Q-V)*(4*C*R-g) := by
  dsimp only
  let K := symmetricAnnihilation μ T
  have hK := symmetricAnnihilation_isSymm μ T
  have hV := quadraticPerturbation_poincare_of_bound_le hn hμ T hT12 hT23 K hK 0 C hC
  simp only [zero_pow (by norm_num : 2≠0),zero_mul,add_zero,sub_zero] at hV
  have hd := cubic_quadratic_deficit_covariance_sq_le hn hμ T hT12 hT23 K hK C hC
  rw [quadraticGradientPairing_symmetricAnnihilation] at hd
  exact ⟨matrixFrobeniusSq_nonneg _,symmetricAnnihilation_square_le_fourth_add_two hμ T,
    variance_nonneg _ _,centeredQuadratic_variance_le_eight hμ K hK,
    variance_nonneg _ _,by nlinarith [hV],cubic_quadratic_covariance_sq_le hμ T K,hd⟩

end KLSConstantImprovement.ActualCubicQuadraticDeficit
#print axioms KLSConstantImprovement.ActualCubicQuadraticDeficit.centeredQuadratic_variance_eq
#print axioms KLSConstantImprovement.ActualCubicQuadraticDeficit.centeredQuadratic_variance_le_eight
#print axioms KLSConstantImprovement.ActualCubicQuadraticDeficit.cubic_quadratic_covariance_sq_le
#print axioms KLSConstantImprovement.ActualCubicQuadraticDeficit.quadraticPerturbation_poincare_of_bound_le
#print axioms KLSConstantImprovement.ActualCubicQuadraticDeficit.nonnegative_quadratic_discriminant
#print axioms KLSConstantImprovement.ActualCubicQuadraticDeficit.cubic_quadratic_deficit_covariance_sq_le
#print axioms KLSConstantImprovement.ActualCubicQuadraticDeficit.quadraticGradientPairing_symmetricAnnihilation
#print axioms KLSConstantImprovement.ActualCubicQuadraticDeficit.symmetricAnnihilation_square_le_fourth_add_two
#print axioms KLSConstantImprovement.ActualCubicQuadraticDeficit.original_symmetricAnnihilation_joint_constraints
