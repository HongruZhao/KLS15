import ActualTwoRowsAppellSplit
import ActualTripleTensorExactCreation
import ActualPairAppellRemainder

/-! The proper fourth Appell drift consists exactly of the size-two and
size-three creation terms. These are actual Appell tensors; no fourth
Appell-energy estimate is inferred from a fourth-cumulant estimate. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25.PairTensor
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actualAppellProperRemainder_four_split (μ : Measure (Space n))
    (f : Space n → ℝ) :
    actualAppellProperRemainder μ f 4 =
      actualAppellPairContractionSum μ f 4 + actualAppellTripleContractionSum μ f 4 := by
  classical
  unfold actualAppellProperRemainder actualAppellPairContractionSum
    actualAppellTripleContractionSum
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases h2 : S.card=2
  · have hp : 2 ≤ S.card ∧ S.card ≤ 4-1 := by omega
    have h3 : S.card≠3 := by omega
    simp only [ite_eq_left hp,ite_eq_left h2,ite_eq_right h3,add_zero]
  · by_cases h3 : S.card=3
    · have hp : 2 ≤ S.card ∧ S.card ≤ 4-1 := by omega
      simp only [ite_eq_left hp,ite_eq_right h2,ite_eq_left h3,zero_add]
    · have hp : ¬(2 ≤ S.card ∧ S.card ≤ 4-1) := by omega
      simp only [ite_eq_right hp,ite_eq_right h2,ite_eq_right h3,add_zero]

theorem actualAppellTripleContractionSum_four_square_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    square (actualAppellTripleContractionSum μ f 4) ≤
      13824*actualAppellEnergy μ f 2 := by
  let : IsProbabilityMeasure μ := hμ.isProb
  rw [show (4:ℕ)=1+3 by norm_num,actualAppellTripleContractionSum_eq_creation hμ hf]
  have hb := actual_triple_creation_square_le_exact hμ 1
    (actualAppellCoefficient μ f 2) (actualAppellCoefficient_pair_symmetric hμ.logConcave hf)
  simpa only [Nat.reduceAdd,KLSBelow25.TripleCreation.exactCap_four,actualAppellEnergy,square] using hb

private theorem pairing_le_sqrt_energy_of_square_le
    {μ : Measure (Space n)} (f : Space n → ℝ) (d : ℕ)
    (R : Tensor (ι:=Fin n) d) {c : ℝ} (hc : 0 ≤ c) (hr : square R ≤ c) :
    pairing (actualAppellCoefficient μ f d) R ≤
      Real.sqrt (actualAppellEnergy μ f d)*Real.sqrt c := by
  have hb := (pairing_sq_le (actualAppellCoefficient μ f d) R).trans
    (mul_le_mul_of_nonneg_left hr (actualAppellEnergy_nonneg μ f d))
  have hsE := Real.sq_sqrt (actualAppellEnergy_nonneg μ f d)
  have hsc := Real.sq_sqrt hc
  have hn : 0 ≤ Real.sqrt (actualAppellEnergy μ f d)*Real.sqrt c := by positivity
  change (pairing (actualAppellCoefficient μ f d) R)^2 ≤ actualAppellEnergy μ f d*c at hb
  nlinarith [sq_nonneg (pairing (actualAppellCoefficient μ f d) R+
    Real.sqrt (actualAppellEnergy μ f d)*Real.sqrt c)]

theorem actualAppellTripleContractionSum_four_pairing_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    pairing (actualAppellCoefficient μ f 4) (actualAppellTripleContractionSum μ f 4) ≤
      Real.sqrt (actualAppellEnergy μ f 4)*Real.sqrt (13824*actualAppellEnergy μ f 2) :=
  pairing_le_sqrt_energy_of_square_le f 4 _ (by positivity [actualAppellEnergy_nonneg μ f 2])
    (actualAppellTripleContractionSum_four_square_le hμ hf)

theorem actualAppellProperRemainder_four_pairing_le_creation
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualAppellCoefficient μ f 4 ⬝ᵥ actualAppellProperRemainder μ f 4 ≤
      Real.sqrt (actualAppellEnergy μ f 4)*
        (Real.sqrt (176*actualAppellEnergy μ f 3)+Real.sqrt (13824*actualAppellEnergy μ f 2)) := by
  have hp := actualAppellPairContractionSum_pairing_le (r:=1) hμ hf
  norm_num at hp
  have hp' : pairing (actualAppellCoefficient μ f 4) (actualAppellPairContractionSum μ f 4) ≤
      Real.sqrt (actualAppellEnergy μ f 4)*Real.sqrt (176*actualAppellEnergy μ f 3) := by
    simpa only [Nat.reduceAdd,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 176)] using hp
  have ht := actualAppellTripleContractionSum_four_pairing_le hμ hf
  rw [actualAppellProperRemainder_four_split,dotProduct_add]
  change pairing (actualAppellCoefficient μ f 4) (actualAppellPairContractionSum μ f 4)+
    pairing (actualAppellCoefficient μ f 4) (actualAppellTripleContractionSum μ f 4) ≤ _
  nlinarith

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualAppellProperRemainder_four_split
#print axioms KLS.DeterministicBridgeIntegration.actualAppellTripleContractionSum_four_square_le
#print axioms KLS.DeterministicBridgeIntegration.actualAppellProperRemainder_four_pairing_le_creation
