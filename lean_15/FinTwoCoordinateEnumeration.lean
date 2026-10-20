import AppellTensorTwoSlot

/-! Exact finite coordinate enumeration and two-slot action. -/
noncomputable section
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration

theorem sum_fin_two_coordinates {ι : Type*} [Fintype ι]
    (F : (Fin 2 → ι) → ℝ) :
    (∑ a, F a) = ∑ j, ∑ k, F ![j,k] := by
  rw [← (finTwoArrowEquiv ι).symm.sum_comp F]
  simp only [Fintype.sum_prod_type,finTwoArrowEquiv_symm_apply]

theorem sum_fin_three_coordinates {ι : Type*} [Fintype ι]
    (F : (Fin 3 → ι) → ℝ) :
    (∑ a, F a) = ∑ i, ∑ j, ∑ k, F ![i,j,k] := by
  rw [← (Fin.consEquiv (fun _ : Fin 3 => ι)).sum_comp F]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_fin_two_coordinates]
  rfl

theorem coordinateSlot_zero_pair {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (T : (Fin 2 → Fin n) → ℝ)
    (j k : Fin n) :
    coordinateSlot (0 : Fin 2) H T ![j,k] = ∑ l, H j l*T ![l,k] := by
  classical
  unfold coordinateSlot
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  apply congrArg T
  funext i
  fin_cases i <;> simp

theorem coordinateSlot_one_pair {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (T : (Fin 2 → Fin n) → ℝ)
    (j k : Fin n) :
    coordinateSlot (1 : Fin 2) H T ![j,k] = ∑ l, H k l*T ![j,l] := by
  classical
  unfold coordinateSlot
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  apply congrArg T
  funext i
  fin_cases i <;> simp

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.sum_fin_two_coordinates
#print axioms KLS.DeterministicBridgeNext.sum_fin_three_coordinates
#print axioms KLS.DeterministicBridgeNext.coordinateSlot_zero_pair
#print axioms KLS.DeterministicBridgeNext.coordinateSlot_one_pair
