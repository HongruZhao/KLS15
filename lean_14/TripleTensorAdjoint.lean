import TripleTensorPermutation
import PairTensorAdjoint

/-! Exact triple-creation pairing with its ordered annihilation map. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.TripleTensor
open TripleProjection PairTensor
variable {r : ℕ} {ι : Type*} [Fintype ι]
set_option maxHeartbeats 1500000

def consFrame (r : ℕ) : Fin 3 ⊕ Fin r ≃ Fin (r+3) where
  toFun := Sum.elim (Fin.cases 0 (Fin.cases 1 (fun _ => 2)))
    (fun j => j.succ.succ.succ)
  invFun := Fin.cases (Sum.inl 0) (Fin.cases (Sum.inl 1) (Fin.cases (Sum.inl 2) Sum.inr))
  left_inv := by
    rintro (i|i)
    · fin_cases i <;> rfl
    · rfl
  right_inv := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun l => ?_) k <;> rfl

@[simp] theorem consFrame_left_zero : consFrame r (Sum.inl 0)=0 := rfl
@[simp] theorem consFrame_left_one : consFrame r (Sum.inl 1)=1 := rfl
@[simp] theorem consFrame_left_two : consFrame r (Sum.inl 2)=2 := rfl
@[simp] theorem consFrame_right (j : Fin r) : consFrame r (Sum.inr j)=j.succ.succ.succ := rfl

theorem kernel_frame_pairing_eq_cons (κ : ι→ι→ι→ι→ℝ)
    (H : Tensor (ι:=ι) (r+1)) (T : Tensor (ι:=ι) (r+3)) (hT : Symmetric T)
    (F : Fin 3 ⊕ Fin r ≃ Fin (r+3)) :
    pairing (kernelInFrame κ H F) T=pairing (kernelInFrame κ H (consFrame r)) T := by
  let π : Equiv.Perm (Fin (r+3)) := F.symm.trans (consFrame r)
  have hframe : F.trans π=consFrame r := by ext i; simp [π]
  calc
    pairing (kernelInFrame κ H F) T =
      ∑ a,kernelInFrame κ H F (a∘π)*T (a∘π) :=
        (Equiv.sum_comp (wordPerm π) (fun a => kernelInFrame κ H F a*T a)).symm
    _ = pairing (kernelInFrame κ H (consFrame r)) T := by
      simp only [kernelInFrame_comp,hframe,pairing]
      simp_rw [hT π]

theorem kernel_pairing_annihilation (κ : ι→ι→ι→ι→ℝ)
    (H : Tensor (ι:=ι) (r+1)) (T : Tensor (ι:=ι) (r+3)) (hT : Symmetric T)
    (e : Triple (r+3)) :
    pairing (kernel κ H e) T=pairing H (annihilation κ T) := by
  rw [kernel,kernel_frame_pairing_eq_cons κ H T hT]
  unfold pairing kernelInFrame annihilation
  conv_lhs =>
    rw [sum_cons_coordinates]
    arg 2;ext i
    rw [sum_cons_coordinates]
    arg 2;ext j
    rw [sum_cons_coordinates]
  conv_rhs => rw [sum_cons_coordinates]
  simp only [consFrame_left_zero,consFrame_left_one,consFrame_left_two,consFrame_right,
    Fin.cons_zero,Fin.cons_one,Fin.cons_succ,Fin.tail_cons]
  simp_rw [Finset.sum_mul,Finset.mul_sum]
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
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext m
    arg 2;ext i
    arg 2;ext j
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext m
    arg 2;ext i
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext m
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have htwo : (2 : Fin (r+3))=(0 : Fin (r+1)).succ.succ := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2<r+3)]
  rw [htwo]
  simp only [Fin.cons_succ,Fin.cons_zero]
  ring

theorem creation_pairing (κ : ι→ι→ι→ι→ℝ)
    (H : Tensor (ι:=ι) (r+1)) (T : Tensor (ι:=ι) (r+3)) (hT : Symmetric T) :
    pairing (creation κ H) T=
      (Fintype.card (Triple (r+3)) : ℝ)*pairing H (annihilation κ T) := by
  change (∑ a,(∑ e,kernel κ H e a)*T a)=_
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  change (∑ e,pairing (kernel κ H e) T)=_
  simp_rw [kernel_pairing_annihilation κ H T hT]
  simp

end KLSBelow25.TripleTensor
#print axioms KLSBelow25.TripleTensor.creation_pairing
