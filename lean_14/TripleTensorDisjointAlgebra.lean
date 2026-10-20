import TripleTensorAdjoint
import PairTensorDisjointAlgebra

/-! Literal six-coordinate disjoint contraction for fourth-cumulant
triple creation. Only symmetry of the input tensor is used. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.TripleTensor
open PairTensor
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {r : ℕ} {ι : Type*} [Fintype ι]

def disjointSwap (r : ℕ) : Equiv.Perm (Fin (r+6)) :=
  (Equiv.swap 0 3).trans (Equiv.swap 1 4) |>.trans (Equiv.swap 2 5)

def disjointInsertion (κ : ι→ι→ι→ι→ℝ) (H : Tensor (ι:=ι) (r+4)) :
    Tensor (ι:=ι) (r+6) := fun a =>
  ∑ m,κ (a 0) (a 1) (a 2) m *
    H (Fin.cons m (Fin.tail (Fin.tail (Fin.tail a))))

@[simp] theorem disjointSwap_0 : disjointSwap r 0 = 3 := by
  simp [disjointSwap, Equiv.swap_apply_def, Fin.ext_iff, Fin.coe_ofNat_eq_mod,
    Nat.mod_eq_of_lt (by omega : 2<r+6),Nat.mod_eq_of_lt (by omega : 3<r+6),
    Nat.mod_eq_of_lt (by omega : 4<r+6),Nat.mod_eq_of_lt (by omega : 5<r+6)]

@[simp] theorem disjointSwap_1 : disjointSwap r 1 = 4 := by
  simp [disjointSwap, Equiv.swap_apply_def, Fin.ext_iff, Fin.coe_ofNat_eq_mod,
    Nat.mod_eq_of_lt (by omega : 2<r+6),Nat.mod_eq_of_lt (by omega : 3<r+6),
    Nat.mod_eq_of_lt (by omega : 4<r+6),Nat.mod_eq_of_lt (by omega : 5<r+6)]

@[simp] theorem disjointSwap_2 : disjointSwap r 2 = 5 := by
  simp [disjointSwap, Equiv.swap_apply_def, Fin.ext_iff, Fin.coe_ofNat_eq_mod,
    Nat.mod_eq_of_lt (by omega : 2<r+6),Nat.mod_eq_of_lt (by omega : 3<r+6),
    Nat.mod_eq_of_lt (by omega : 4<r+6)]

@[simp] theorem disjointSwap_3 : disjointSwap r 3 = 0 := by
  simp [disjointSwap, Equiv.swap_apply_def, Fin.ext_iff, Fin.coe_ofNat_eq_mod,
    Nat.mod_eq_of_lt (by omega : 2<r+6),
    Nat.mod_eq_of_lt (by omega : 4<r+6),Nat.mod_eq_of_lt (by omega : 5<r+6)]

@[simp] theorem disjointSwap_4 : disjointSwap r 4 = 1 := by
  simp [disjointSwap, Equiv.swap_apply_def, Fin.ext_iff, Fin.coe_ofNat_eq_mod,
    Nat.mod_eq_of_lt (by omega : 2<r+6),Nat.mod_eq_of_lt (by omega : 3<r+6),
    Nat.mod_eq_of_lt (by omega : 4<r+6),Nat.mod_eq_of_lt (by omega : 5<r+6)]

@[simp] theorem disjointSwap_5 : disjointSwap r 5 = 2 := by
  simp [disjointSwap, Equiv.swap_apply_def, Fin.ext_iff, Fin.coe_ofNat_eq_mod,
    Nat.mod_eq_of_lt (by omega : 3<r+6),
    Nat.mod_eq_of_lt (by omega : 4<r+6),Nat.mod_eq_of_lt (by omega : 5<r+6)]

theorem fin_4_succ (r : ℕ) : (4 : Fin (r+5)) = (3 : Fin (r+4)).succ := by
  apply Fin.ext
  simp [Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 3<r+4),
    Nat.mod_eq_of_lt (by omega : 4<r+5)]

theorem fin_5_succ (r : ℕ) : (5 : Fin (r+6)) = (4 : Fin (r+5)).succ := by
  apply Fin.ext
  simp [Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 4<r+5),
    Nat.mod_eq_of_lt (by omega : 5<r+6)]

omit [Fintype ι] in theorem cons_4_eval (i j k l : ι) (z : Fin (r+1)→ι) :
    (Fin.cons i (Fin.cons j (Fin.cons k (Fin.cons l (z)))) : Fin (r+5)→ι) 4 = z 0 := by
  rw [fin_4_succ,Fin.cons_succ,PairTensor.cons_three_eval]

omit [Fintype ι] in theorem cons_5_eval (i j k l m : ι) (z : Fin (r+1)→ι) :
    (Fin.cons i (Fin.cons j (Fin.cons k (Fin.cons l (Fin.cons m (z))))) : Fin (r+6)→ι) 5 = z 0 := by
  rw [fin_5_succ,Fin.cons_succ,cons_4_eval]

theorem sum_first_six_coordinates (F : Tensor (ι:=ι) (r+6)) :
    (∑ a,F a)=∑ i,∑ j,∑ k,∑ l,∑ m,∑ n,∑ z,
      F (Fin.cons i (Fin.cons j (Fin.cons k (Fin.cons l (Fin.cons m (Fin.cons n z)))))) := by
  rw [sum_cons_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_cons_coordinates]
  apply Finset.sum_congr rfl
  intro j _
  rw [sum_cons_coordinates]
  apply Finset.sum_congr rfl
  intro k _
  rw [sum_cons_coordinates]
  apply Finset.sum_congr rfl
  intro l _
  rw [sum_cons_coordinates]
  apply Finset.sum_congr rfl
  intro m _
  rw [sum_cons_coordinates]

omit [Fintype ι] in theorem cons_six_disjointSwap (i j k l m n : ι) (z : Fin r→ι) :
    (Fin.cons i (Fin.cons j (Fin.cons k (Fin.cons l (Fin.cons m (Fin.cons n z)))))) ∘
      disjointSwap r =
    Fin.cons l (Fin.cons m (Fin.cons n (Fin.cons i (Fin.cons j (Fin.cons k z))))) := by
  ext x
  refine Fin.cases ?_ (fun x => ?_) x
  · simp only [Function.comp_apply,disjointSwap_0,PairTensor.cons_three_eval,Fin.cons_zero]
  · refine Fin.cases ?_ (fun x => ?_) x
    · simp only [Function.comp_apply,Fin.succ_zero_eq_one,disjointSwap_1,cons_4_eval,
        Fin.cons_one,Fin.cons_zero]
    · refine Fin.cases ?_ (fun x => ?_) x
      · simp only [Function.comp_apply,Fin.succ_zero_eq_one,Fin.succ_one_eq_two',
          disjointSwap_2,cons_5_eval,PairTensor.cons_two_eval,Fin.cons_zero]
      · refine Fin.cases ?_ (fun x => ?_) x
        · simp only [Function.comp_apply,Fin.succ_zero_eq_one,Fin.succ_one_eq_two',
            ←PairTensor.fin_three_succ,disjointSwap_3,Fin.cons_zero,PairTensor.cons_three_eval]
        · refine Fin.cases ?_ (fun x => ?_) x
          · simp only [Function.comp_apply,Fin.succ_zero_eq_one,Fin.succ_one_eq_two',
              ←PairTensor.fin_three_succ,←fin_4_succ,disjointSwap_4,Fin.cons_one,cons_4_eval,
              Fin.cons_zero]
          · refine Fin.cases ?_ (fun x => ?_) x
            · simp only [Function.comp_apply,Fin.succ_zero_eq_one,Fin.succ_one_eq_two',
                ←PairTensor.fin_three_succ,←fin_4_succ,←fin_5_succ,disjointSwap_5,
                PairTensor.cons_two_eval,cons_5_eval,Fin.cons_zero]
            · have h0 : x.succ.succ.succ.succ.succ.succ ≠ (0 : Fin (r+6)) := by
                simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod]
              have h1 : x.succ.succ.succ.succ.succ.succ ≠ (1 : Fin (r+6)) := by
                simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod]
              have h2 : x.succ.succ.succ.succ.succ.succ ≠ (2 : Fin (r+6)) := by
                simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 2<r+6)]
              have h3 : x.succ.succ.succ.succ.succ.succ ≠ (3 : Fin (r+6)) := by
                simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 3<r+6)]
              have h4 : x.succ.succ.succ.succ.succ.succ ≠ (4 : Fin (r+6)) := by
                simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 4<r+6)]
              have h5 : x.succ.succ.succ.succ.succ.succ ≠ (5 : Fin (r+6)) := by
                simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 5<r+6)]
              simp [disjointSwap,Function.comp_def,Equiv.swap_apply_def,h0,h1,h2,h3,h4,h5]

omit [Fintype ι] in theorem cons_four_swap03 (i j k l : ι) (z : Fin r→ι) :
    (Fin.cons i (Fin.cons j (Fin.cons k (Fin.cons l z)))) ∘
      Equiv.swap (0 : Fin (r+4)) 3 =
    Fin.cons l (Fin.cons j (Fin.cons k (Fin.cons i z))) := by
  ext x
  refine Fin.cases ?_ (fun x => ?_) x
  · simp only [Function.comp_apply,Equiv.swap_apply_left,PairTensor.cons_three_eval,Fin.cons_zero]
  · refine Fin.cases ?_ (fun x => ?_) x
    · simp [Equiv.swap_apply_def,Fin.ext_iff,Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt (by omega : 3<r+4)]
    · refine Fin.cases ?_ (fun x => ?_) x
      · simp [Equiv.swap_apply_def,Fin.ext_iff,Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (by omega : 2<r+4),Nat.mod_eq_of_lt (by omega : 3<r+4),
          PairTensor.cons_two_eval]
      · refine Fin.cases ?_ (fun x => ?_) x
        · simp only [Function.comp_apply,Fin.succ_zero_eq_one,Fin.succ_one_eq_two',
            ←PairTensor.fin_three_succ,Equiv.swap_apply_right,Fin.cons_zero,
            PairTensor.cons_three_eval]
        · have h0 : x.succ.succ.succ.succ ≠ (0 : Fin (r+4)) := by
            simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod]
          have h3 : x.succ.succ.succ.succ ≠ (3 : Fin (r+4)) := by
            simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 3<r+4)]
          simp [Equiv.swap_apply_def,h0,h3]

omit [Fintype ι] in theorem symmetric_cons_four_cycle
    (H : Tensor (ι:=ι) (r+4)) (hH : Symmetric H) (i j k l : ι) (z : Fin r→ι) :
    H (Fin.cons i (Fin.cons j (Fin.cons k (Fin.cons l z)))) =
    H (Fin.cons l (Fin.cons i (Fin.cons j (Fin.cons k z)))) := by
  have h₁ := PairTensor.symmetric_cons_cycle H hH i j k (Fin.cons l z)
  have h₂ := hH (Equiv.swap (0 : Fin (r+4)) 3)
    (Fin.cons k (Fin.cons i (Fin.cons j (Fin.cons l z))))
  rw [cons_four_swap03] at h₂
  exact h₁.trans h₂.symm

theorem disjoint_insertion_pairing_eq_exchange (κ : ι→ι→ι→ι→ℝ)
    (H : Tensor (ι:=ι) (r+4)) (hH : Symmetric H) :
    pairing (disjointInsertion κ H)
      (fun a => disjointInsertion κ H (a ∘ disjointSwap r)) =
    exchange (annihilation κ H) := by
  unfold exchange pairing
  conv_lhs => rw [sum_first_six_coordinates]
  conv_rhs =>
    rw [sum_cons_coordinates]
    arg 2;ext p
    rw [sum_cons_coordinates]
  simp only [cons_six_disjointSwap,disjointInsertion,Fin.cons_zero,Fin.cons_one,
    PairTensor.cons_two_eval,Fin.tail_cons,PairTensor.cons_two_exchangeSwap,
    annihilation]
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  conv_lhs =>
    arg 2;ext i
    arg 2;ext j
    arg 2;ext k
    arg 2;ext l
    arg 2;ext m
    arg 2;ext n
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext i
    arg 2;ext j
    arg 2;ext k
    arg 2;ext l
    arg 2;ext m
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext i
    arg 2;ext j
    arg 2;ext k
    arg 2;ext l
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext i
    arg 2;ext j
    arg 2;ext k
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext i
    arg 2;ext j
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext i
    rw [Finset.sum_comm]
  conv_lhs =>
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext p
    arg 2;ext i
    arg 2;ext j
    arg 2;ext k
    arg 2;ext l
    arg 2;ext m
    arg 2;ext n
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext p
    arg 2;ext i
    arg 2;ext j
    arg 2;ext k
    arg 2;ext l
    arg 2;ext m
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext p
    arg 2;ext i
    arg 2;ext j
    arg 2;ext k
    arg 2;ext l
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext p
    arg 2;ext i
    arg 2;ext j
    arg 2;ext k
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext p
    arg 2;ext i
    arg 2;ext j
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext p
    arg 2;ext i
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext p
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext p
    arg 2;ext q
    arg 2;ext i
    arg 2;ext j
    arg 2;ext k
    arg 2;ext l
    arg 2;ext m
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext p
    arg 2;ext q
    arg 2;ext i
    arg 2;ext j
    arg 2;ext k
    arg 2;ext l
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext p
    arg 2;ext q
    arg 2;ext i
    arg 2;ext j
    arg 2;ext k
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext p
    arg 2;ext q
    arg 2;ext i
    arg 2;ext j
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext p
    arg 2;ext q
    arg 2;ext i
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext p
    arg 2;ext q
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  rw [symmetric_cons_four_cycle H hH i j k q z,
    symmetric_cons_four_cycle H hH l m n p z]
  ring

theorem coordinate_disjoint_trace (κ : ι→ι→ι→ι→ℝ)
    (H : Tensor (ι:=ι) (r+4)) (hH : Symmetric H) :
    pairing (kernelInFrame κ H (consFrame (r+3)))
      (fun a => kernelInFrame κ H (consFrame (r+3)) (a ∘ disjointSwap r)) =
    exchange (annihilation κ H) := by
  have hv : kernelInFrame κ H (consFrame (r+3))=disjointInsertion κ H := rfl
  rw [hv]
  exact disjoint_insertion_pairing_eq_exchange κ H hH

end KLSBelow25.TripleTensor
#print axioms KLSBelow25.TripleTensor.disjoint_insertion_pairing_eq_exchange
#print axioms KLSBelow25.TripleTensor.coordinate_disjoint_trace
