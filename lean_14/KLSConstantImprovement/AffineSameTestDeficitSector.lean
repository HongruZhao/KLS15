import KLSConstantImprovement.PiecewiseDeficitSector
import KLSConstantImprovement.AffineSameTestSeed238452BellmanEndpoint

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal
namespace KLSConstantImprovement.AffineSameTestDeficitSector
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter ActualFixedTensorDeficit
open PoincareDeficitSectorTransfer

def threshold : ℝ := 476980909947407839787528 / 73294488743425979973441

theorem threshold_formula :
    8 - 224 / (9 * ((7004509165936219997049 / 488281250000000000000 : ℝ≥0) : ℝ) + 21) =
      threshold := by
  norm_num [threshold]

theorem threshold_strictly_improves : threshold < PiecewiseDeficitSector.threshold := by
  norm_num [threshold, PiecewiseDeficitSector.threshold]

theorem original_large_deficit_additive_balance {n : ℕ}
    {μ : Measure (Space n)} (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ a b c, T a b c = T b a c)
    (hT23 : ∀ a b c, T a b c = T a c b)
    (hlarge : threshold * tensorSquare T ≤ sliceDeficit μ T) :
    0 ≤ contractedDeficitHessian μ T + 21 * sliceDeficit μ T + 92 * tensorSquare T := by
  apply original_additive_balance_of_poincare_and_large_deficit hμ T hT12 hT23
    (AffineSameTestSeed238452BellmanEndpoint.original_poincare_mem hn hμ)
  simpa only [threshold_formula] using hlarge

end KLSConstantImprovement.AffineSameTestDeficitSector
#print axioms KLSConstantImprovement.AffineSameTestDeficitSector.threshold_formula
#print axioms KLSConstantImprovement.AffineSameTestDeficitSector.threshold_strictly_improves
#print axioms KLSConstantImprovement.AffineSameTestDeficitSector.original_large_deficit_additive_balance
