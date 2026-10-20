import KLSConstantImprovement.ActualCubicAffineQuadraticRegression

/-! Completed same-law affine and one-quadratic regression saving.
The strict denominator is paid by the actual quadratic variance-eight and
coordinate Bessel bounds. All covariance signs and ordered norms remain
literal; no global raw336 or additive saving premise is asserted. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators ENNReal ContDiff
namespace KLSConstantImprovement.ActualCubicAffineQuadraticSaving
open KLS KLS.DeterministicBridge KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
open ActualCubicPoincareFourthSector ActualCubicAffineRegression QuadraticCovarianceCharge
open ActualCubicQuadraticRegression ActualCubicQuadraticDeficit ActualCubicAffineQuadraticRegression
variable {n : ℕ}
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def regressionDenominator (μ : Measure (Space n)) (B : Matrix (Fin n) (Fin n) ℝ) (C : ℝ) : ℝ :=
  4*C*matrixFrobeniusSq B-ProbabilityTheory.variance (ActualCubicGradientEnergy.centeredQuadratic B) μ-
    ‖covarianceVector μ (ActualCubicGradientEnergy.centeredQuadratic B)‖^2/(C-1)

def regressionNumerator (μ : Measure (Space n)) (T : Array3 (Fin n))
    (B : Matrix (Fin n) (Fin n) ℝ) (C : ℝ) : ℝ :=
  covariance (tensorPolynomial μ T) (ActualCubicGradientEnergy.centeredQuadratic B) μ-
    6*C*quadraticGradientPairing μ T B+
      inner ℝ (covarianceVector μ (tensorPolynomial μ T))
        (covarianceVector μ (ActualCubicGradientEnergy.centeredQuadratic B))/(C-1)

theorem scalar_regression_denominator_lower {C N g a : ℝ} (hC : 3<C)
    (hg : g≤8*N) (ha : a≤g) :
    4*C*(C-3)/(C-1)*N≤4*C*N-g-a/(C-1) := by
  have hC1 : 0<C-1 := by linarith
  have hCp : 0≤C := by linarith
  have hp := mul_le_mul_of_nonneg_left hg hCp
  apply (mul_le_mul_iff_of_pos_left hC1).mp
  have heL : (C-1)*(4*C*(C-3)/(C-1)*N)=4*C*(C-3)*N := by
    field_simp [ne_of_gt hC1]
  have heR : (C-1)*(4*C*N-g-a/(C-1))=(C-1)*(4*C*N-g)-a := by
    field_simp [ne_of_gt hC1]
  rw [heL,heR]
  nlinarith [ha,hp]

theorem regressionDenominator_lower {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (C : ℝ)
    (hC : LongPrefixCubicBellmanEndpoint.bound≤C) :
    4*C*(C-3)/(C-1)*matrixFrobeniusSq B≤regressionDenominator μ B C := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hCb : 3<LongPrefixCubicBellmanEndpoint.bound := by norm_num [LongPrefixCubicBellmanEndpoint.bound]
  have hC3 : 3<C := lt_of_lt_of_le hCb hC
  exact scalar_regression_denominator_lower hC3 (centeredQuadratic_variance_le_eight hμ B hB)
    (covarianceVector_norm_sq_le_variance hμ.isotropic (centeredQuadratic_memLp hμ B))

theorem regressionDenominator_pos {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (hN : 0 < matrixFrobeniusSq B)
    (C : ℝ) (hC : LongPrefixCubicBellmanEndpoint.bound≤C) :
    0<regressionDenominator μ B C := by
  have hCb : 3<LongPrefixCubicBellmanEndpoint.bound := by norm_num [LongPrefixCubicBellmanEndpoint.bound]
  have hC3 : 3<C := lt_of_lt_of_le hCb hC
  have hC0 : 0<C := by linarith
  have hCm3 : 0<C-3 := by linarith
  have hCm1 : 0<C-1 := by linarith
  have hp : 0<4*C*(C-3)/(C-1)*matrixFrobeniusSq B := by positivity
  exact lt_of_lt_of_le hp (regressionDenominator_lower hμ B hB C hC)

theorem affine_quadratic_deficit_polynomial {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (C : ℝ)
    (hC : LongPrefixCubicBellmanEndpoint.bound≤C) (s : ℝ) :
    0≤9*C*(fourthContraction μ T+2*tensorSquare T)-ProbabilityTheory.variance (tensorPolynomial μ T) μ-
      ‖covarianceVector μ (tensorPolynomial μ T)‖^2/(C-1)+
      2*s*regressionNumerator μ T B C+s^2*regressionDenominator μ B C := by
  have hp := quadraticPerturbation_affine_charge hn hμ T hT12 hT23 B hB s C hC
  rw [quadraticPerturbation_variance hμ T B s,covarianceVector_quadraticPerturbation hμ T B s,
    norm_sub_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hp
  unfold regressionNumerator regressionDenominator
  linear_combination hp

theorem tensorPolynomial_affine_quadratic_deficit_sq_le {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (C : ℝ)
    (hC : LongPrefixCubicBellmanEndpoint.bound≤C) :
    (regressionNumerator μ T B C)^2≤regressionDenominator μ B C*
      (9*C*(fourthContraction μ T+2*tensorSquare T)-ProbabilityTheory.variance (tensorPolynomial μ T) μ-
        ‖covarianceVector μ (tensorPolynomial μ T)‖^2/(C-1)) := by
  have hd := nonnegative_quadratic_discriminant
    (affine_quadratic_deficit_polynomial hn hμ T hT12 hT23 B hB C hC)
  nlinarith [hd]

theorem tensorPolynomial_affine_quadratic_charge {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (hN : 0 < matrixFrobeniusSq B)
    (C : ℝ) (hC : LongPrefixCubicBellmanEndpoint.bound≤C) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      ‖covarianceVector μ (tensorPolynomial μ T)‖^2/(C-1)+
      (regressionNumerator μ T B C)^2/regressionDenominator μ B C≤
        9*C*(fourthContraction μ T+2*tensorSquare T) := by
  have hd := tensorPolynomial_affine_quadratic_deficit_sq_le hn hμ T hT12 hT23 B hB C hC
  have hh := regressionDenominator_pos hμ B hB hN C hC
  have hp : (regressionNumerator μ T B C)^2/regressionDenominator μ B C≤
      9*C*(fourthContraction μ T+2*tensorSquare T)-ProbabilityTheory.variance (tensorPolynomial μ T) μ-
        ‖covarianceVector μ (tensorPolynomial μ T)‖^2/(C-1) :=
    (div_le_iff₀ hh).mpr (by nlinarith [hd])
  linarith [hp]

theorem tensorPolynomial_affine_charge_of_bound_le {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (C : ℝ) (hC : LongPrefixCubicBellmanEndpoint.bound≤C) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      ‖covarianceVector μ (tensorPolynomial μ T)‖^2/(C-1)≤
        9*C*(fourthContraction μ T+2*tensorSquare T) := by
  have hB : (0 : Matrix (Fin n) (Fin n) ℝ).IsSymm := by ext i j;simp
  have hp := quadraticPerturbation_affine_charge hn hμ T hT12 hT23 0 hB 0 C hC
  have hz : quadraticPerturbation μ T 0 0=tensorPolynomial μ T := by
    funext x
    simp [quadraticPerturbation]
  rw [hz] at hp
  norm_num only [zero_pow (by norm_num : 2≠0),zero_mul,mul_zero,add_zero,sub_zero] at hp
  nlinarith [hp]

theorem tensorPolynomial_variance_le_336_of_regression_saving {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (hN : 0 < matrixFrobeniusSq B)
    (C : ℝ) (hC : LongPrefixCubicBellmanEndpoint.bound≤C)
    (hpaid : 9*C*(fourthContraction μ T+2*tensorSquare T)-336*tensorSquare T≤
      ‖covarianceVector μ (tensorPolynomial μ T)‖^2/(C-1)+
        (regressionNumerator μ T B C)^2/regressionDenominator μ B C) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ≤336*tensorSquare T := by
  linarith [tensorPolynomial_affine_quadratic_charge hn hμ T hT12 hT23 B hB hN C hC]

theorem tensorPolynomial_variance_le_additive_of_regression_saving {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (hN : 0 < matrixFrobeniusSq B)
    (C : ℝ) (hC : LongPrefixCubicBellmanEndpoint.bound≤C)
    (hpaid : 9*C*(fourthContraction μ T+2*tensorSquare T)-224*tensorSquare T-21*signedTraceSquare μ T≤
      ‖covarianceVector μ (tensorPolynomial μ T)‖^2/(C-1)+
        (regressionNumerator μ T B C)^2/regressionDenominator μ B C) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ≤224*tensorSquare T+21*signedTraceSquare μ T := by
  linarith [tensorPolynomial_affine_quadratic_charge hn hμ T hT12 hT23 B hB hN C hC]

end KLSConstantImprovement.ActualCubicAffineQuadraticSaving
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticSaving.scalar_regression_denominator_lower
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticSaving.regressionDenominator_lower
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticSaving.regressionDenominator_pos
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticSaving.affine_quadratic_deficit_polynomial
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticSaving.tensorPolynomial_affine_quadratic_deficit_sq_le
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticSaving.tensorPolynomial_affine_quadratic_charge
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticSaving.tensorPolynomial_affine_charge_of_bound_le
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticSaving.tensorPolynomial_variance_le_336_of_regression_saving
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticSaving.tensorPolynomial_variance_le_additive_of_regression_saving
