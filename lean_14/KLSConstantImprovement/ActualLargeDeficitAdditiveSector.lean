import KLSConstantImprovement.ActualCubicRegressionSectorCriteria

/-! The large-deficit additive sector follows from the retained original-law
Bessel and Poincare inequalities. Its displayed sector condition is the
only additional input; the small and moderate deficit sectors remain open. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualLargeDeficitAdditiveSector
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter ActualFixedTensorDeficit
open ActualCubicPoincareFourthSector ActualDeficitBesselBound
open ActualCubicRegressionSectorCriteria
set_option maxHeartbeats 2000000

theorem large_deficit_scalar_gate {N d F S V : ℝ}
    (hd : d = 6*N-F) (hlarge : (2792/429:ℝ)*N ≤ d)
    (hS : -(F+2*N) ≤ S) (hV : V ≤ (2583/20:ℝ)*(F+2*N)) :
    0 ≤ 224*N+21*S-V := by
  linarith

theorem original_large_deficit_additive_balance {n : ℕ}
    {μ : Measure (Space n)} (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ a b c,T a b c = T b a c)
    (hT23 : ∀ a b c,T a b c = T a c b)
    (hlarge : (2792/429:ℝ)*tensorSquare T ≤ sliceDeficit μ T) :
    0 ≤ contractedDeficitHessian μ T+21*sliceDeficit μ T+92*tensorSquare T := by
  have hQ : 0 ≤ fourthContraction μ T+2*tensorSquare T := by
    linarith [(fourthContraction_bounds hμ T hT23).1]
  have hp := tensorPolynomial_variance_le_current_poincare hn hμ T hT12 hT23
  have hC : 9*LongPrefixCubicBellmanEndpoint.bound ≤ (2583/20:ℝ) := by
    norm_num [LongPrefixCubicBellmanEndpoint.bound]
  have hrounded := hp.trans (mul_le_mul_of_nonneg_right hC hQ)
  have hS := (signedTraceSquare_bounds_by_fourth_add_two hμ T).1
  rw [additive_deficit_balance_eq hμ T hT12 hT23]
  exact large_deficit_scalar_gate (by rfl) hlarge hS hrounded

end KLSConstantImprovement.ActualLargeDeficitAdditiveSector
#print axioms KLSConstantImprovement.ActualLargeDeficitAdditiveSector.large_deficit_scalar_gate
#print axioms KLSConstantImprovement.ActualLargeDeficitAdditiveSector.original_large_deficit_additive_balance
