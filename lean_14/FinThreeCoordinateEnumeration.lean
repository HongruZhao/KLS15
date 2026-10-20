import FinTwoCoordinateEnumeration

/-! Exact rank-three coordinate slot formulas and rank-four enumeration. -/
noncomputable section
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration

theorem sum_fin_four_coordinates {ι : Type*} [Fintype ι]
    (F : (Fin 4 → ι) → ℝ) :
    (∑ a, F a) = ∑ i, ∑ j, ∑ k, ∑ l, F ![i,j,k,l] := by
  rw [← (Fin.consEquiv (fun _ : Fin 4 => ι)).sum_comp F]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_fin_three_coordinates]
  rfl

theorem coordinateSlot_zero_triple {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (T : (Fin 3 → Fin n) → ℝ)
    (j k l : Fin n) :
    coordinateSlot (0 : Fin 3) H T ![j,k,l] = ∑ a, H j a*T ![a,k,l] := by
  classical
  unfold coordinateSlot
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply congrArg T
  funext i
  fin_cases i <;> simp

theorem coordinateSlot_one_triple {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (T : (Fin 3 → Fin n) → ℝ)
    (j k l : Fin n) :
    coordinateSlot (1 : Fin 3) H T ![j,k,l] = ∑ a, H k a*T ![j,a,l] := by
  classical
  unfold coordinateSlot
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply congrArg T
  funext i
  fin_cases i <;> simp

theorem coordinateSlot_two_triple {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (T : (Fin 3 → Fin n) → ℝ)
    (j k l : Fin n) :
    coordinateSlot (2 : Fin 3) H T ![j,k,l] = ∑ a, H l a*T ![j,k,a] := by
  classical
  unfold coordinateSlot
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply congrArg T
  funext i
  fin_cases i <;> simp

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.sum_fin_four_coordinates
#print axioms KLS.DeterministicBridgeNext.coordinateSlot_zero_triple
#print axioms KLS.DeterministicBridgeNext.coordinateSlot_one_triple
#print axioms KLS.DeterministicBridgeNext.coordinateSlot_two_triple
