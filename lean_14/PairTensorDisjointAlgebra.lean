import PairTensorAdjoint
import FirstSlotSymmetrization
import QuarticDisjointCreationTrace
import PairTensorRepresentatives

/-! Literal all-rank disjoint-pair contraction. Ordered tensor norms and
the annihilation definition are unchanged. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.PairTensor
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {r : ℕ} {ι : Type*} [Fintype ι]

def disjointInsertion (κ : ι → ι → ι → ℝ) (H : Tensor (ι:=ι) (r+3)) :
    Tensor (ι:=ι) (r+4) := fun a =>
  ∑ m,κ (a 0) (a 1) m * H (Fin.cons m (Fin.tail (Fin.tail a)))

def disjointSwap (r : ℕ) : Equiv.Perm (Fin (r+4)) :=
  Equiv.swap 0 2 * Equiv.swap 1 3

theorem fin_two_succ (r : ℕ) : (2 : Fin (r+3)) = (1 : Fin (r+2)).succ := by
  apply Fin.ext
  simp [Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 2<r+3)]

theorem fin_three_succ (r : ℕ) : (3 : Fin (r+4)) = (2 : Fin (r+3)).succ := by
  apply Fin.ext
  simp [Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 2<r+3),
    Nat.mod_eq_of_lt (by omega : 3<r+4)]

@[simp] theorem disjointSwap_zero : disjointSwap r 0 = 2 := by
  simp [disjointSwap,Equiv.swap_apply_def,Fin.ext_iff,Fin.coe_ofNat_eq_mod,
    Nat.mod_eq_of_lt (by omega : 3<r+4)]
@[simp] theorem disjointSwap_one : disjointSwap r 1 = 3 := by
  simp [disjointSwap,Equiv.swap_apply_def,Fin.ext_iff,Fin.coe_ofNat_eq_mod,
    Nat.mod_eq_of_lt (by omega : 2<r+4),Nat.mod_eq_of_lt (by omega : 3<r+4)]
@[simp] theorem disjointSwap_two : disjointSwap r 2 = 0 := by
  simp [disjointSwap,Equiv.swap_apply_def,Fin.ext_iff,Fin.coe_ofNat_eq_mod,
    Nat.mod_eq_of_lt (by omega : 2<r+4),Nat.mod_eq_of_lt (by omega : 3<r+4)]
@[simp] theorem disjointSwap_three : disjointSwap r 3 = 1 := by
  simp [disjointSwap,Equiv.swap_apply_def,Fin.ext_iff,Fin.coe_ofNat_eq_mod,
    Nat.mod_eq_of_lt (by omega : 2<r+4)]

omit [Fintype ι] in theorem cons_two_eval (i j : ι) (z : Fin (r+1) → ι) :
    (Fin.cons i (Fin.cons j z) : Fin (r+3) → ι) 2 = z 0 := by
  rw [fin_two_succ,Fin.cons_succ,Fin.cons_one]

omit [Fintype ι] in theorem cons_three_eval (i j k : ι) (z : Fin (r+1) → ι) :
    (Fin.cons i (Fin.cons j (Fin.cons k z)) : Fin (r+4) → ι) 3 = z 0 := by
  rw [fin_three_succ,Fin.cons_succ,cons_two_eval]

omit [Fintype ι] in theorem cons_four_disjointSwap (i j k l : ι) (z : Fin r → ι) :
    (Fin.cons i (Fin.cons j (Fin.cons k (Fin.cons l z)))) ∘ disjointSwap r =
      Fin.cons k (Fin.cons l (Fin.cons i (Fin.cons j z))) := by
  ext x
  refine Fin.cases ?_ (fun x => ?_) x
  · simp only [Function.comp_apply,disjointSwap_zero,cons_two_eval,Fin.cons_zero]
  · refine Fin.cases ?_ (fun x => ?_) x
    · simp only [Function.comp_apply,Fin.succ_zero_eq_one,disjointSwap_one,
        cons_three_eval,Fin.cons_one,Fin.cons_zero]
    · refine Fin.cases ?_ (fun x => ?_) x
      · simp only [Function.comp_apply,Fin.succ_zero_eq_one,Fin.succ_one_eq_two',
          disjointSwap_two,cons_two_eval,Fin.cons_zero]
      · refine Fin.cases ?_ (fun x => ?_) x
        · simp only [Function.comp_apply,Fin.succ_zero_eq_one,Fin.succ_one_eq_two',
            ←fin_three_succ,disjointSwap_three,cons_three_eval,Fin.cons_one,Fin.cons_zero]
        · have h0 : x.succ.succ.succ.succ ≠ (0 : Fin (r+4)) := by
            simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod]
          have h1 : x.succ.succ.succ.succ ≠ (1 : Fin (r+4)) := by
            simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod]
          have h2 : x.succ.succ.succ.succ ≠ (2 : Fin (r+4)) := by
            simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 2<r+4)]
          have h3 : x.succ.succ.succ.succ ≠ (3 : Fin (r+4)) := by
            simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 3<r+4)]
          simp [disjointSwap,Function.comp_def,Equiv.swap_apply_def,h0,h1,h2,h3]

omit [Fintype ι] in theorem cons_two_exchangeSwap (i j : ι) (z : Fin r → ι) :
    (Fin.cons i (Fin.cons j z)) ∘ Equiv.swap (0 : Fin (r+2)) 1 =
      Fin.cons j (Fin.cons i z) := by
  ext x
  refine Fin.cases ?_ (fun x => ?_) x
  · simp
  · refine Fin.cases ?_ (fun x => ?_) x
    · simp
    · have h0 : x.succ.succ ≠ (0 : Fin (r+2)) := by simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod]
      have h1 : x.succ.succ ≠ (1 : Fin (r+2)) := by
        simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod]
      simp [Equiv.swap_apply_def,h0,h1]

theorem sum_first_four_coordinates (F : Tensor (ι:=ι) (r+4)) :
    (∑ a,F a)=∑ i,∑ j,∑ k,∑ l,∑ z,
      F (Fin.cons i (Fin.cons j (Fin.cons k (Fin.cons l z)))) := by
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

omit [Fintype ι] in theorem symmetric_cons_cycle (H : Tensor (ι:=ι) (r+3)) (hH : Symmetric H)
    (i j k : ι) (z : Fin r → ι) :
    H (Fin.cons i (Fin.cons j (Fin.cons k z)))=
      H (Fin.cons k (Fin.cons i (Fin.cons j z))) := by
  have h01 := hH (Equiv.swap (0 : Fin (r+3)) 1)
    (Fin.cons i (Fin.cons j (Fin.cons k z)))
  have h12 := hH (Equiv.swap (0 : Fin (r+3)) 2)
    (Fin.cons j (Fin.cons i (Fin.cons k z)))
  have he01 : (Fin.cons i (Fin.cons j (Fin.cons k z))) ∘
      Equiv.swap (0 : Fin (r+3)) 1 = Fin.cons j (Fin.cons i (Fin.cons k z)) :=
    cons_two_exchangeSwap i j (Fin.cons k z)
  have he02 : (Fin.cons j (Fin.cons i (Fin.cons k z))) ∘
      Equiv.swap (0 : Fin (r+3)) 2 = Fin.cons k (Fin.cons i (Fin.cons j z)) := by
    ext x
    refine Fin.cases ?_ (fun x => ?_) x
    · simp [fin_two_succ,-Fin.succ_one_eq_two,-Fin.succ_one_eq_two']
    · refine Fin.cases ?_ (fun x => ?_) x
      · simp [Equiv.swap_apply_def,Fin.ext_iff,Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (by omega : 2<r+3)]
      · refine Fin.cases ?_ (fun x => ?_) x
        · simp [fin_two_succ,-Fin.succ_one_eq_two,-Fin.succ_one_eq_two']
        · have h0 : x.succ.succ.succ ≠ (0 : Fin (r+3)) := by
            simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod]
          have h2 : x.succ.succ.succ ≠ (2 : Fin (r+3)) := by
            simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 2<r+3)]
          simp [Equiv.swap_apply_def,h0,h2]

  rw [he01] at h01
  rw [he02] at h12
  exact h01.symm.trans h12.symm

theorem disjoint_insertion_pairing_eq_exchange (κ : ι → ι → ι → ℝ)
    (H : Tensor (ι:=ι) (r+3)) (hH : Symmetric H) :
    pairing (disjointInsertion κ H)
      (fun a => disjointInsertion κ H (a ∘ disjointSwap r)) =
        exchange (annihilation κ H) := by
  have hslice (z : Fin r → ι) (m p : ι) :
      KLSBelow25.CubicCreation.annihilation κ
        (fun i j k => H (Fin.cons i (Fin.cons j (Fin.cons k z)))) m p =
      annihilation κ H (Fin.cons m (Fin.cons p z)) := by
    unfold KLSBelow25.CubicCreation.annihilation annihilation
    simp only [Fin.cons_zero,Fin.tail_cons]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [symmetric_cons_cycle H hH i j p z]
  have hl : pairing (disjointInsertion κ H)
      (fun a => disjointInsertion κ H (a ∘ disjointSwap r)) =
      ∑ z : Fin r → ι,KLSBelow25.QuarticSymmetricNoise.disjoint
        (fun i j k l => ∑ m,κ i j m*H (Fin.cons m (Fin.cons k (Fin.cons l z)))) := by
    unfold pairing
    rw [sum_first_four_coordinates]
    simp only [cons_four_disjointSwap,disjointInsertion,Fin.cons_zero,
      Fin.cons_one,Fin.tail_cons]
    unfold KLSBelow25.QuarticSymmetricNoise.disjoint
      KLSBelow25.QuarticSymmetricNoise.quadSum
    calc
      _=∑ i,∑ j,∑ k,∑ z,∑ l,
          (∑ m,κ i j m*H (Fin.cons m (Fin.cons k (Fin.cons l z))))*
          (∑ m,κ k l m*H (Fin.cons m (Fin.cons i (Fin.cons j z)))) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _=∑ i,∑ j,∑ z,∑ k,∑ l,
          (∑ m,κ i j m*H (Fin.cons m (Fin.cons k (Fin.cons l z))))*
          (∑ m,κ k l m*H (Fin.cons m (Fin.cons i (Fin.cons j z)))) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _=∑ i,∑ z,∑ j,∑ k,∑ l,
          (∑ m,κ i j m*H (Fin.cons m (Fin.cons k (Fin.cons l z))))*
          (∑ m,κ k l m*H (Fin.cons m (Fin.cons i (Fin.cons j z)))) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _=_ := Finset.sum_comm
  rw [hl]
  simp_rw [KLSBelow25.QuarticSymmetricNoise.disjoint_creation_trace,hslice]
  unfold exchange pairing
  conv_rhs =>
    rw [sum_cons_coordinates]
    arg 2
    ext m
    rw [sum_cons_coordinates]
  simp only [cons_two_exchangeSwap]
  calc
    _=∑ m,∑ z,∑ p,annihilation κ H (Fin.cons m (Fin.cons p z))*
        annihilation κ H (Fin.cons p (Fin.cons m z)) := Finset.sum_comm
    _=_ := Finset.sum_congr rfl fun m _ => Finset.sum_comm

theorem swapPairs_eq_disjointSwap : swapPairs r = disjointSwap r := by
  ext i
  by_cases h0 : i=0
  · subst i
    simp
  · by_cases h1 : i=1
    · subst i
      simp
    · by_cases h2 : i=2
      · subst i
        simp
      · by_cases h3 : i=3
        · subst i
          simp
        · simp [swapPairs,disjointSwap,Equiv.swap_apply_def,h0,h1,h2,h3]

theorem coordinate_disjoint_trace (κ : ι → ι → ι → ℝ)
    (H : Tensor (ι:=ι) (r+3)) (hH : Symmetric H) :
    pairing (kernelInFrame κ H (consFrame (r+2)))
      (fun a => kernelInFrame κ H (consFrame (r+2)) (a ∘ swapPairs r)) =
        exchange (annihilation κ H) := by
  have hv : kernelInFrame κ H (consFrame (r+2)) = disjointInsertion κ H := rfl
  rw [hv,swapPairs_eq_disjointSwap]
  exact disjoint_insertion_pairing_eq_exchange κ H hH

end KLSBelow25.PairTensor
#print axioms KLSBelow25.PairTensor.disjoint_insertion_pairing_eq_exchange
#print axioms KLSBelow25.PairTensor.coordinate_disjoint_trace
