import PairTensorCoordinateSlots
import PairTensorGram

noncomputable section
open scoped BigOperators
namespace KLSBelow25.PairTensor
open PairProjection

variable {r : ℕ}

def swapPairs (r : ℕ) : Equiv.Perm (Fin (r+4)) :=
  (Equiv.swap 0 2).trans (Equiv.swap 1 3)

def disjointPair (r : ℕ) : Pair (r+4) :=
  mapPair (swapPairs r) (incidentPair (0 : Fin (r+3)))

@[simp] theorem swapPairs_zero : swapPairs r 0 = 2 := by
  simp [swapPairs,Equiv.swap_apply_def,Fin.ext_iff,
    Nat.mod_eq_of_lt (by omega : 2<r+4), Nat.mod_eq_of_lt (by omega : 3<r+4)]
@[simp] theorem swapPairs_one : swapPairs r 1 = 3 := by
  simp [swapPairs,Equiv.swap_apply_def,Fin.ext_iff,
    Nat.mod_eq_of_lt (by omega : 2<r+4)]
@[simp] theorem swapPairs_two : swapPairs r 2 = 0 := by
  simp [swapPairs,Equiv.swap_apply_def,Fin.ext_iff,
    Nat.mod_eq_of_lt (by omega : 3<r+4)]
@[simp] theorem swapPairs_three : swapPairs r 3 = 1 := by
  simp [swapPairs,Equiv.swap_apply_def,Fin.ext_iff,
    Nat.mod_eq_of_lt (by omega : 2<r+4), Nat.mod_eq_of_lt (by omega : 3<r+4)]

@[simp] theorem disjointPair_val : (disjointPair r).val = {2,3} := by
  simp [disjointPair,mapPair,incidentPair]

theorem incident_intersection_card {s : ℕ} (i j : Fin (s+1)) (hij : i≠j) :
    ((incidentPair i).val ∩ (incidentPair j).val).card=1 := by
  have he : (incidentPair i).val ∩ (incidentPair j).val = {0} := by
    ext k
    simp only [incidentPair,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
    have hs : i.succ ≠ j.succ := fun h => hij (Fin.succ_inj.mp h)
    have hi := Fin.succ_ne_zero i
    have hj := Fin.succ_ne_zero j
    constructor
    · rintro ⟨h | h,h' | h'⟩
      · exact h
      · exact h
      · exact h'
      · exact (hs (h.symm.trans h')).elim
    · intro h
      exact ⟨Or.inl h,Or.inl h⟩
  rw [he,Finset.card_singleton]

theorem disjoint_intersection_card :
    ((incidentPair (0 : Fin (r+3))).val ∩ (disjointPair r).val).card=0 := by
  rw [disjointPair_val]
  have he : ({0,1} : Finset (Fin (r+4))) ∩ {2,3} = ∅ := by
    ext i
    simp [Fin.ext_iff,Nat.mod_eq_of_lt (by omega : 2<r+4),
      Nat.mod_eq_of_lt (by omega : 3<r+4)]
  simpa [incidentPair] using congrArg Finset.card he

end KLSBelow25.PairTensor
#print axioms KLSBelow25.PairTensor.disjoint_intersection_card
