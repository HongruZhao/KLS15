import ActualSelectedRowsAppellDrift
import ActualTripleAppellRemainder

/-! Exact extraction of the size-two and size-three proper rows together.
The size-three row is zero below degree four; the full-subset terminal
term is never accidentally inserted into the proper remainder. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25.PairTensor
variable {n : ℕ}
set_option maxHeartbeats 1500000

def twoRowsProfile (theta2 theta3 : ℕ → ℝ) (d a : ℕ) : ℝ :=
  if a=2 then 1-theta2 d else if a=3 then 1-theta3 d else 1

def actualAppellProperTripleContractionSum (μ : Measure (Space n))
    (f : Space n → ℝ) (d : ℕ) : Tensor (ι := Fin n) d :=
  if 4 ≤ d then actualAppellTripleContractionSum μ f d else 0

theorem actualAppellProperRemainder_two_rows_split (μ : Measure (Space n))
    (f : Space n → ℝ) (theta2 theta3 : ℕ → ℝ) (d : ℕ) (hd : 3 ≤ d) :
    actualAppellProperRemainder μ f d =
      actualProfileProperRemainder μ f (twoRowsProfile theta2 theta3) d +
      theta2 d • actualAppellPairContractionSum μ f d +
      theta3 d • actualAppellProperTripleContractionSum μ f d := by
  classical
  by_cases hd4 : 4 ≤ d
  · unfold actualAppellProperTripleContractionSum
    rw [ite_eq_left hd4]
    unfold actualAppellProperRemainder actualProfileProperRemainder
      actualAppellPairContractionSum actualAppellTripleContractionSum
    rw [Finset.smul_sum,Finset.smul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    by_cases h2 : S.card=2
    · have hp : 2 ≤ S.card ∧ S.card ≤ d-1 := by omega
      have h3 : S.card≠3 := by omega
      simp only [ite_eq_left hp,ite_eq_left h2,ite_eq_right h3,smul_zero,add_zero,twoRowsProfile]
      ext a
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    · by_cases h3 : S.card=3
      · have hp : 2 ≤ S.card ∧ S.card ≤ d-1 := by omega
        simp only [ite_eq_left hp,ite_eq_right h2,ite_eq_left h3,smul_zero,add_zero,twoRowsProfile]
        ext a
        simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
        ring
      · by_cases hp : 2 ≤ S.card ∧ S.card ≤ d-1
        · simp [hp,h2,h3,twoRowsProfile]
        · simp [hp,h2,h3]
  · unfold actualAppellProperTripleContractionSum
    rw [ite_eq_right hd4,smul_zero,add_zero]
    unfold actualAppellProperRemainder actualProfileProperRemainder actualAppellPairContractionSum
    rw [Finset.smul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    by_cases h2 : S.card=2
    · have hp : 2 ≤ S.card ∧ S.card ≤ d-1 := by omega
      simp only [ite_eq_left hp,ite_eq_left h2,twoRowsProfile]
      ext a
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    · have hp : ¬(2 ≤ S.card ∧ S.card ≤ d-1) := by omega
      simp [hp,h2]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualAppellProperRemainder_two_rows_split
