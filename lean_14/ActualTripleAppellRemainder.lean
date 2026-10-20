import ActualTripleAppellContraction
import TripleProjectionCounts

/-! The literal size-three part of the actual Appell lower drift is the
unordered-triple fourth-cumulant creation map. The norm convention is unchanged. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
open KLSBelow25.PairTensor KLSBelow25.TripleTensor KLSBelow25.TripleProjection
variable {n r : ℕ}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def actualAppellTripleContractionSum (μ : Measure (Space n)) (f : Space n→ℝ)
    (d : ℕ) : Tensor (ι := Fin n) d :=
  ∑ S : Finset (Fin d), if S.card=3 then actualSubsetAppellContraction μ f d S else 0

theorem actualAppellTripleContractionSum_eq_creation {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    actualAppellTripleContractionSum μ f (r+3) =
      KLSBelow25.TripleTensor.creation (actualFourthCumulantArray μ) (actualAppellCoefficient μ f (r+1)) := by
  funext γ
  have he : (Finset.univ : Finset (Finset (Fin (r+3)))).filter (fun S => S.card=3) = triples (r+3) := by
    ext S
    simp [mem_triples]
  unfold actualAppellTripleContractionSum
  simp only [Finset.sum_apply]
  change (∑ S : Finset (Fin (r+3)), (if S.card=3 then
      actualSubsetAppellContraction μ f (r+3) S else 0) γ)=_
  simp only [ite_apply,Pi.zero_apply]
  rw [←Finset.sum_filter,he,←sum_triple_values]
  simp_rw [actualSubsetAppellContraction_triple_kernel hμ hf]
  rfl

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualAppellTripleContractionSum_eq_creation
