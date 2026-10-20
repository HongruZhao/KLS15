import KLSConstantImprovement.PoincareDeficitSectorTransfer
import KLSConstantImprovement.PiecewiseSeed23847BellmanEndpoint
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal
namespace KLSConstantImprovement.PiecewiseDeficitSector
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter ActualFixedTensorDeficit
open PoincareDeficitSectorTransfer

def threshold : ℝ := 95396212757884608629992/14658901594735576078749

theorem threshold_formula :
    8-224/(9*((1400902260526175119861/97656250000000000000 : ℝ≥0):ℝ)+21)=threshold := by
  norm_num [threshold]

theorem threshold_strictly_improves :
    threshold<PoincareDeficitSectorTransfer.threshold := by
  norm_num [threshold,PoincareDeficitSectorTransfer.threshold]

theorem original_large_deficit_additive_balance {n : ℕ}
    {μ : Measure (Space n)} (hn : 1≤n) (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ a b c,T a b c=T b a c)
    (hT23 : ∀ a b c,T a b c=T a c b)
    (hlarge : threshold * tensorSquare T ≤ sliceDeficit μ T) :
    0≤contractedDeficitHessian μ T+21*sliceDeficit μ T+92*tensorSquare T := by
  apply original_additive_balance_of_poincare_and_large_deficit hμ T hT12 hT23
    (PiecewiseSeed23847BellmanEndpoint.original_poincare_mem hn hμ)
  simpa only [threshold_formula] using hlarge

end KLSConstantImprovement.PiecewiseDeficitSector
#print axioms KLSConstantImprovement.PiecewiseDeficitSector.threshold_formula
#print axioms KLSConstantImprovement.PiecewiseDeficitSector.threshold_strictly_improves
#print axioms KLSConstantImprovement.PiecewiseDeficitSector.original_large_deficit_additive_balance
