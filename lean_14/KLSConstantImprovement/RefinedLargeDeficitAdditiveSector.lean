import KLSConstantImprovement.ActualLargeDeficitAdditiveSector

/-! A wider original-law sector for the integrated additive deficit estimate.
The argument reuses the accepted Poincare and Bessel bounds with a tighter
rational upper bound for the Poincare constant. It does not change the
universal endpoint or settle the smaller-deficit sector. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace KLSConstantImprovement.RefinedLargeDeficitAdditiveSector
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter ActualFixedTensorDeficit
open ActualCubicPoincareFourthSector ActualDeficitBesselBound
open ActualCubicRegressionSectorCriteria
set_option maxHeartbeats 2000000

def threshold : ℝ := 4884344/750543

theorem threshold_positive : 0 < threshold := by norm_num [threshold]

theorem threshold_lt_previous : threshold < (2792/429 : ℝ) := by
  norm_num [threshold]

theorem exact_threshold_payment :
    ((645543/5000 : ℝ)+21)*(8-threshold) = 224 := by
  norm_num [threshold]

theorem refined_large_deficit_scalar_gate {N d F S V : ℝ}
    (hd : d = 6*N-F) (hlarge : threshold*N ≤ d)
    (hS : -(F+2*N) ≤ S) (hV : V ≤ (645543/5000 : ℝ)*(F+2*N)) :
    0 ≤ 224*N+21*S-V := by
  norm_num only [threshold] at hlarge
  linarith

theorem original_refined_large_deficit_additive_balance {n : ℕ}
    {μ : Measure (Space n)} (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ a b c,T a b c = T b a c)
    (hT23 : ∀ a b c,T a b c = T a c b)
    (hlarge : threshold*tensorSquare T ≤ sliceDeficit μ T) :
    0 ≤ contractedDeficitHessian μ T+21*sliceDeficit μ T+92*tensorSquare T := by
  have hQ : 0 ≤ fourthContraction μ T+2*tensorSquare T := by
    linarith [(fourthContraction_bounds hμ T hT23).1]
  have hp := tensorPolynomial_variance_le_current_poincare hn hμ T hT12 hT23
  have hC : 9*LongPrefixCubicBellmanEndpoint.bound ≤ (645543/5000 : ℝ) := by
    norm_num [LongPrefixCubicBellmanEndpoint.bound]
  have hrounded := hp.trans (mul_le_mul_of_nonneg_right hC hQ)
  have hS := (signedTraceSquare_bounds_by_fourth_add_two hμ T).1
  rw [additive_deficit_balance_eq hμ T hT12 hT23]
  exact refined_large_deficit_scalar_gate (by rfl) hlarge hS hrounded

end KLSConstantImprovement.RefinedLargeDeficitAdditiveSector
#print axioms KLSConstantImprovement.RefinedLargeDeficitAdditiveSector.threshold_positive
#print axioms KLSConstantImprovement.RefinedLargeDeficitAdditiveSector.threshold_lt_previous
#print axioms KLSConstantImprovement.RefinedLargeDeficitAdditiveSector.exact_threshold_payment
#print axioms KLSConstantImprovement.RefinedLargeDeficitAdditiveSector.refined_large_deficit_scalar_gate
#print axioms KLSConstantImprovement.RefinedLargeDeficitAdditiveSector.original_refined_large_deficit_additive_balance
