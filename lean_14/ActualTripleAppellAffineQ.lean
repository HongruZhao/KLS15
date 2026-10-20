import ActualTripleTensorAffineCreation
import ActualTripleAppellYoung

/-! Unconditional actual triple-insertion square bound and weighted Young
estimate. All fourth-cumulant geometry is discharged internally. -/
noncomputable section
open MeasureTheory
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25.PairTensor KLSBelow25.CoupledEnergy
open KLSBelow25.TripleCreation
variable {n r : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actualAppellTripleContractionSum_square_le_affineQ
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    square (actualAppellTripleContractionSum μ f (r+4)) ≤
      affineQ ((r : ℝ)+4)*actualCanonicalContractionSquare μ f 3 (r+1)+
      affineRest (exactCap (r+2)) ((r : ℝ)+4)*actualAppellEnergy μ f (r+2) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  rw [show r+4=(r+1)+3 by omega,actualAppellTripleContractionSum_eq_creation hμ hf]
  have hb := actual_triple_creation_square_le_affine hμ (r+1)
    (actualAppellCoefficient μ f ((r+1)+1)) (actualAppellCoefficient_pair_symmetric hμ.logConcave hf)
  rw [actual_triple_kernel_square_eq_canonical hμ hf] at hb
  simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+3=4 by norm_num,actualAppellEnergy,square] using hb

theorem actualAppellTripleContractionSum_weighted_young_affineQ
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K v : ℝ} (hK : 0<K) (hv : 0<v) :
    2*factorialWeight K (r+4)*pairing (actualAppellCoefficient μ f (r+4))
      (actualAppellTripleContractionSum μ f (r+4)) ≤
      v*factorialWeight K (r+4)*actualAppellEnergy μ f (r+4)+
      (affineQ ((r : ℝ)+4)/(K^2*((r : ℝ)+4)^2*((r : ℝ)+3)^2*v))*factorialWeight K (r+2)*
        actualCanonicalContractionSquare μ f 3 (r+1)+
      (affineRest (exactCap (r+2)) ((r : ℝ)+4)/(K^2*((r : ℝ)+4)^2*((r : ℝ)+3)^2*v))*
        factorialWeight K (r+2)*actualAppellEnergy μ f (r+2) :=
  actualAppellTripleContractionSum_weighted_young_of_affine_square f hK hv
    (actualAppellTripleContractionSum_square_le_affineQ hμ hf)

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualAppellTripleContractionSum_square_le_affineQ
#print axioms KLS.DeterministicBridgeIntegration.actualAppellTripleContractionSum_weighted_young_affineQ
