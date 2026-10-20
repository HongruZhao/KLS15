import ActualPairAppellRemainder

/-! Exact separation of the size-two insertion from every higher proper
subset. It retains the actual tensors and makes no numerical substitution. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
open KLSBelow25.PairTensor
variable {n : ℕ}

def actualAppellHigherContractionSum (μ : Measure (Space n)) (f : Space n→ℝ)
    (d : ℕ) : Tensor (ι := Fin n) d :=
  ∑ S : Finset (Fin d), if 3≤S.card ∧ S.card≤d-1 then
    actualSubsetAppellContraction μ f d S else 0

theorem actualAppellProperRemainder_eq_pair_add_higher
    (μ : Measure (Space n)) (f : Space n→ℝ) (d : ℕ) (hd : 3≤d) :
    actualAppellProperRemainder μ f d =
      actualAppellPairContractionSum μ f d + actualAppellHigherContractionSum μ f d := by
  unfold actualAppellProperRemainder actualAppellPairContractionSum actualAppellHigherContractionSum
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases h2 : S.card=2
  · have hc : 2≤S.card ∧ S.card≤d-1 := by omega
    have hn : ¬(3≤S.card ∧ S.card≤d-1) := by omega
    rw [ite_eq_left hc,ite_eq_left h2,ite_eq_right hn,add_zero]
  · have he : (2≤S.card ∧ S.card≤d-1) ↔ (3≤S.card ∧ S.card≤d-1) := by omega
    simp only [h2,ite_false,zero_add,he]

theorem actualAppellProperRemainder_pairing_split
    (μ : Measure (Space n)) (f : Space n→ℝ) (d : ℕ) (hd : 3≤d) :
    pairing (actualAppellCoefficient μ f d) (actualAppellProperRemainder μ f d) =
      pairing (actualAppellCoefficient μ f d) (actualAppellPairContractionSum μ f d)+
      pairing (actualAppellCoefficient μ f d) (actualAppellHigherContractionSum μ f d) := by
  rw [actualAppellProperRemainder_eq_pair_add_higher μ f d hd]
  simp only [pairing,Pi.add_apply,mul_add,Finset.sum_add_distrib]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualAppellProperRemainder_eq_pair_add_higher
#print axioms KLS.DeterministicBridgeIntegration.actualAppellProperRemainder_pairing_split
