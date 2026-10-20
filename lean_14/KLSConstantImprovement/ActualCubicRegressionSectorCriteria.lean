import KLSConstantImprovement.ActualCubicAffineQuadraticSaving
import KLSConstantImprovement.ActualCubicVarianceIdentity

/-! Denominator-free same-law regression budgets for the raw336 and additive
deficit sectors. Positivity of both denominators is paid by the original
regression theorem. The sufficient budget remains an explicit sector input,
and no global deficit estimate is asserted. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators
namespace KLSConstantImprovement.ActualCubicRegressionSectorCriteria
open KLS KLS.DeterministicBridge KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter QuadraticCovarianceCharge
open ActualCubicAffineQuadraticSaving ActualCubicVarianceIdentity ActualFixedTensorDeficit
variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

def regressionSectorBudget (μ : Measure (Space n)) (T : Array3 (Fin n))
    (B : Matrix (Fin n) (Fin n) ℝ) (C target : ℝ) : ℝ :=
  (C-1)*regressionDenominator μ B C*(target-9*C*(fourthContraction μ T+2*tensorSquare T))+
    regressionDenominator μ B C*‖covarianceVector μ (tensorPolynomial μ T)‖^2+
      (C-1)*(regressionNumerator μ T B C)^2

theorem scalar_saving_iff_budget {K h l e A : ℝ} (hK : 0 < K) (hh : 0 < h) :
    A≤l/K+e^2/h ↔ 0≤K*h*(-A)+h*l+K*e^2 := by
  have he : K*h*(l/K+e^2/h-A)=K*h*(-A)+h*l+K*e^2 := by
    field_simp [ne_of_gt hK,ne_of_gt hh] <;> ring
  have hp : 0 < K*h := mul_pos hK hh
  constructor
  · intro hs
    have hb : 0≤K*h*(l/K+e^2/h-A) := mul_nonneg hp.le (sub_nonneg.mpr hs)
    rwa [he] at hb
  · intro hb
    have hs : K*h*0≤K*h*(l/K+e^2/h-A) := by
      rw [he]
      simpa only [mul_zero] using hb
    exact sub_nonneg.mp ((mul_le_mul_iff_of_pos_left hp).mp hs)

theorem regression_saving_iff_budget_nonnegative {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (hN : 0 < matrixFrobeniusSq B)
    (C target : ℝ) (hC : LongPrefixCubicBellmanEndpoint.bound≤C) :
    9*C*(fourthContraction μ T+2*tensorSquare T)-target≤
      ‖covarianceVector μ (tensorPolynomial μ T)‖^2/(C-1)+
        (regressionNumerator μ T B C)^2/regressionDenominator μ B C ↔
      0≤regressionSectorBudget μ T B C target := by
  have hCb : 1 < LongPrefixCubicBellmanEndpoint.bound := by norm_num [LongPrefixCubicBellmanEndpoint.bound]
  have hC1 : 0 < C-1 := by linarith
  have hh := regressionDenominator_pos hμ B hB hN C hC
  have hi := scalar_saving_iff_budget (l := ‖covarianceVector μ (tensorPolynomial μ T)‖^2)
    (e := regressionNumerator μ T B C)
    (A := 9*C*(fourthContraction μ T+2*tensorSquare T)-target) hC1 hh
  rw [neg_sub] at hi
  exact hi

theorem tensorPolynomial_variance_le_target_of_budget {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (hN : 0 < matrixFrobeniusSq B)
    (C target : ℝ) (hC : LongPrefixCubicBellmanEndpoint.bound≤C)
    (hbudget : 0≤regressionSectorBudget μ T B C target) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ≤target := by
  have hs := (regression_saving_iff_budget_nonnegative hμ T B hB hN C target hC).mpr hbudget
  linarith [tensorPolynomial_affine_quadratic_charge hn hμ T hT12 hT23 B hB hN C hC]

theorem tensorPolynomial_variance_le_336_of_budget {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (hN : 0 < matrixFrobeniusSq B)
    (C : ℝ) (hC : LongPrefixCubicBellmanEndpoint.bound≤C)
    (hbudget : 0≤regressionSectorBudget μ T B C (336*tensorSquare T)) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ≤336*tensorSquare T :=
  tensorPolynomial_variance_le_target_of_budget hn hμ T hT12 hT23 B hB hN C _ hC hbudget

theorem tensorPolynomial_variance_le_additive_of_budget {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (hN : 0 < matrixFrobeniusSq B)
    (C : ℝ) (hC : LongPrefixCubicBellmanEndpoint.bound≤C)
    (hbudget : 0≤regressionSectorBudget μ T B C (224*tensorSquare T+21*signedTraceSquare μ T)) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ≤224*tensorSquare T+21*signedTraceSquare μ T :=
  tensorPolynomial_variance_le_target_of_budget hn hμ T hT12 hT23 B hB hN C _ hC hbudget

theorem additive_deficit_balance_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ a b c,T a b c=T b a c)
    (hT23 : ∀ a b c,T a b c=T a c b) :
    contractedDeficitHessian μ T+21*sliceDeficit μ T+92*tensorSquare T=
      224*tensorSquare T+21*signedTraceSquare μ T-ProbabilityTheory.variance (tensorPolynomial μ T) μ := by
  have he := variance_add_deficitHessian_eq hμ T hT12 hT23
  unfold sliceDeficit
  linarith [he]

theorem additive_deficit_balance_nonnegative_of_budget {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (hN : 0 < matrixFrobeniusSq B)
    (C : ℝ) (hC : LongPrefixCubicBellmanEndpoint.bound≤C)
    (hbudget : 0≤regressionSectorBudget μ T B C (224*tensorSquare T+21*signedTraceSquare μ T)) :
    0≤contractedDeficitHessian μ T+21*sliceDeficit μ T+92*tensorSquare T := by
  rw [additive_deficit_balance_eq hμ T hT12 hT23]
  exact sub_nonneg.mpr (tensorPolynomial_variance_le_additive_of_budget hn hμ T hT12 hT23 B hB hN C hC hbudget)

end KLSConstantImprovement.ActualCubicRegressionSectorCriteria
#print axioms KLSConstantImprovement.ActualCubicRegressionSectorCriteria.scalar_saving_iff_budget
#print axioms KLSConstantImprovement.ActualCubicRegressionSectorCriteria.regression_saving_iff_budget_nonnegative
#print axioms KLSConstantImprovement.ActualCubicRegressionSectorCriteria.tensorPolynomial_variance_le_target_of_budget
#print axioms KLSConstantImprovement.ActualCubicRegressionSectorCriteria.tensorPolynomial_variance_le_336_of_budget
#print axioms KLSConstantImprovement.ActualCubicRegressionSectorCriteria.tensorPolynomial_variance_le_additive_of_budget
#print axioms KLSConstantImprovement.ActualCubicRegressionSectorCriteria.additive_deficit_balance_eq
#print axioms KLSConstantImprovement.ActualCubicRegressionSectorCriteria.additive_deficit_balance_nonnegative_of_budget
