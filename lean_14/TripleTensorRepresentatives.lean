import TripleTensorPermutation
import TripleTensorAdjoint
import PairTensorHilbert
import TripleProjectionCounts

noncomputable section
open scoped BigOperators
namespace KLSBelow25.TripleTensor
open PairTensor TripleProjection
variable {r : ℕ} {ι : Type*} [Fintype ι]
set_option maxHeartbeats 1500000

def prefixTriple (r : ℕ) : Triple (r+3) :=
  ⟨{0,1,2},by
    simp [Fin.ext_iff,Nat.mod_eq_of_lt (by omega : 1<r+3),
      Nat.mod_eq_of_lt (by omega : 2<r+3)]⟩

def overlapTwoPerm (r : ℕ) : Equiv.Perm (Fin (r+4)) := Equiv.swap 2 3
def overlapOnePerm (r : ℕ) : Equiv.Perm (Fin (r+5)) :=
  (Equiv.swap 1 3).trans (Equiv.swap 2 4)
def swapTriples (r : ℕ) : Equiv.Perm (Fin (r+6)) :=
  ((Equiv.swap 0 3).trans (Equiv.swap 1 4)).trans (Equiv.swap 2 5)

def overlapTwoTriple (r : ℕ) : Triple (r+4) := mapTriple (overlapTwoPerm r) (prefixTriple (r+1))
def overlapOneTriple (r : ℕ) : Triple (r+5) := mapTriple (overlapOnePerm r) (prefixTriple (r+2))
def disjointTriple (r : ℕ) : Triple (r+6) := mapTriple (swapTriples r) (prefixTriple (r+3))

@[simp] theorem overlapTwoTriple_val : (overlapTwoTriple r).val={0,1,3} := by
  simp [overlapTwoTriple,mapTriple,prefixTriple,overlapTwoPerm,Equiv.swap_apply_def,
    Fin.ext_iff,Nat.mod_eq_of_lt (by omega : 1<r+4),
    Nat.mod_eq_of_lt (by omega : 2<r+4),Nat.mod_eq_of_lt (by omega : 3<r+4)]

@[simp] theorem overlapOneTriple_val : (overlapOneTriple r).val={0,3,4} := by
  simp [overlapOneTriple,mapTriple,prefixTriple,overlapOnePerm,Equiv.swap_apply_def,
    Fin.ext_iff,Nat.mod_eq_of_lt (by omega : 1<r+5),
    Nat.mod_eq_of_lt (by omega : 2<r+5),Nat.mod_eq_of_lt (by omega : 3<r+5),
    Nat.mod_eq_of_lt (by omega : 4<r+5)]

@[simp] theorem disjointTriple_val : (disjointTriple r).val={3,4,5} := by
  simp [disjointTriple,mapTriple,prefixTriple,swapTriples,Equiv.swap_apply_def,
    Fin.ext_iff,Nat.mod_eq_of_lt (by omega : 1<r+6),
    Nat.mod_eq_of_lt (by omega : 2<r+6),Nat.mod_eq_of_lt (by omega : 3<r+6),
    Nat.mod_eq_of_lt (by omega : 4<r+6),Nat.mod_eq_of_lt (by omega : 5<r+6)]

theorem overlapTwo_intersection_card :
    ((prefixTriple (r+1)).val∩(overlapTwoTriple r).val).card=2 := by
  rw [overlapTwoTriple_val]
  simp [prefixTriple,Fin.ext_iff,Nat.mod_eq_of_lt (by omega : 1<r+4),
    Nat.mod_eq_of_lt (by omega : 2<r+4),Nat.mod_eq_of_lt (by omega : 3<r+4)]

theorem overlapOne_intersection_card :
    ((prefixTriple (r+2)).val∩(overlapOneTriple r).val).card=1 := by
  rw [overlapOneTriple_val]
  simp [prefixTriple,Fin.ext_iff,Nat.mod_eq_of_lt (by omega : 1<r+5),
    Nat.mod_eq_of_lt (by omega : 2<r+5),Nat.mod_eq_of_lt (by omega : 3<r+5),
    Nat.mod_eq_of_lt (by omega : 4<r+5)]

theorem disjoint_intersection_card :
    ((prefixTriple (r+3)).val∩(disjointTriple r).val).card=0 := by
  rw [disjointTriple_val]
  simp [prefixTriple,Fin.ext_iff,Nat.mod_eq_of_lt (by omega : 1<r+6),
    Nat.mod_eq_of_lt (by omega : 2<r+6),Nat.mod_eq_of_lt (by omega : 3<r+6),
    Nat.mod_eq_of_lt (by omega : 4<r+6),Nat.mod_eq_of_lt (by omega : 5<r+6)]

theorem kernel_prefix_eq_cons (κ : ι→ι→ι→ι→ℝ)
    (hκ : ∀ m,Symmetric (fun a : Fin 3→ι => κ (a 0) (a 1) (a 2) m))
    (H : Tensor (ι:=ι) (r+1)) (hH : Symmetric H) :
    kernel κ H (prefixTriple r)=kernelInFrame κ H (consFrame r) := by
  funext a
  apply kernelInFrame_eq κ hκ H hH (prefixTriple r)
  · exact tripleFrame_inl_mem _
  · exact tripleFrame_inr_not_mem _
  · intro i
    fin_cases i <;> simp [prefixTriple]
  · intro i
    simp only [consFrame_right,prefixTriple,Finset.mem_insert,Finset.mem_singleton,not_or]
    constructor
    · exact Fin.succ_ne_zero _
    · constructor
      · intro h
        have hh := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt (by omega : 1<r+3)] at hh
      · intro h
        have hh := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt (by omega : 2<r+3)] at hh

theorem triple_sum_toHilbert (κ : ι→ι→ι→ι→ℝ) (H : Tensor (ι:=ι) (r+1)) :
    sumTriples (fun e => toHilbert (kernel κ H e))=toHilbert (creation κ H) := by
  ext a
  simp only [sumTriples,WithLp.ofLp_sum,Finset.sum_apply,toHilbert_apply,creation]

end KLSBelow25.TripleTensor
#print axioms KLSBelow25.TripleTensor.overlapOne_intersection_card
#print axioms KLSBelow25.TripleTensor.disjoint_intersection_card
#print axioms KLSBelow25.TripleTensor.kernel_prefix_eq_cons
