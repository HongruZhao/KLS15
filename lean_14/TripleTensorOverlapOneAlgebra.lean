import TripleTensorAdjoint
import PairTensorDisjointAlgebra

/-! Exact one-overlap contraction of literal triple insertion, expressed as
an exchange pairing of two-slot contractions. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.TripleTensor
open PairTensor
variable {r : ℕ} {ι : Type*} [Fintype ι]
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def overlapOneSwap (r : ℕ) : Equiv.Perm (Fin (r+5)) :=
  fixHeadPerm (disjointSwap r)

omit [Fintype ι] in theorem cons_five_overlapOneSwap (i j k l m : ι) (z : Fin r→ι) :
    (Fin.cons i (Fin.cons j (Fin.cons k (Fin.cons l (Fin.cons m z)))))∘overlapOneSwap r=
    Fin.cons i (Fin.cons l (Fin.cons m (Fin.cons j (Fin.cons k z)))) := by
  have hh : (Fin.cons i (Fin.cons j (Fin.cons k (Fin.cons l (Fin.cons m z)))))∘
      overlapOneSwap r = Fin.cons i ((Fin.cons j (Fin.cons k (Fin.cons l (Fin.cons m z))))∘
        disjointSwap r) := by
    funext a
    refine Fin.cases ?_ (fun b=>?_) a <;>
      simp [overlapOneSwap,Function.comp_def]
  rw [hh,cons_four_disjointSwap]

theorem kernel_cons_eval (κ : ι→ι→ι→ι→ℝ) (H : Tensor (ι:=ι) (r+1))
    (i j k : ι) (z : Fin r→ι) :
    kernelInFrame κ H (consFrame r) (Fin.cons i (Fin.cons j (Fin.cons k z)))=
      ∑ a,κ i j k a*H (Fin.cons a z) := by
  simp only [kernelInFrame,consFrame_left_zero,consFrame_left_one,consFrame_left_two,
    consFrame_right,Fin.cons_zero,Fin.cons_one,cons_two_eval,Fin.cons_succ]

theorem sum_first_five_coordinates (F : Tensor (ι:=ι) (r+5)) :
    (∑ a,F a)=∑ i,∑ j,∑ k,∑ l,∑ m,∑ z,
      F (Fin.cons i (Fin.cons j (Fin.cons k (Fin.cons l (Fin.cons m z))))) := by
  rw [sum_cons_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_first_four_coordinates]

theorem finite_one_overlap_reorder (κ : ι→ι→ι→ι→ℝ) (T : ι→ι→ι→ℝ) (i : ι) :
    (∑ j,∑ k,∑ l,∑ m,(∑ a,κ i j k a*T a l m)*(∑ b,κ i l m b*T b j k)) =
      ∑ a,∑ b,(∑ j,∑ k,κ i j k a*T b j k)*(∑ l,∑ m,κ i l m b*T a l m) := by
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  conv_lhs =>
    arg 2;ext j
    arg 2;ext k
    arg 2;ext l
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext j
    arg 2;ext k
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext a
    arg 2;ext j
    arg 2;ext k
    arg 2;ext l
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext a
    arg 2;ext j
    arg 2;ext k
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext a
    arg 2;ext j
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2;ext a
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- Literal coordinate expansion of the overlap-one kernel pairing. -/
theorem overlap_one_pairing_eq_exchange (κ : ι→ι→ι→ι→ℝ)
    (H : Tensor (ι:=ι) (r+3)) :
    pairing (kernelInFrame κ H (consFrame (r+2)))
      (fun a=>kernelInFrame κ H (consFrame (r+2)) (a∘overlapOneSwap r))=
    ∑ i,∑ z : Fin r→ι,∑ a,∑ b,
      (∑ j,∑ k,κ i j k a*H (Fin.cons b (Fin.cons j (Fin.cons k z))))*
      (∑ l,∑ m,κ i l m b*H (Fin.cons a (Fin.cons l (Fin.cons m z)))) := by
  unfold pairing
  rw [sum_first_five_coordinates]
  simp only [cons_five_overlapOneSwap,kernel_cons_eval]
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
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro z _
  exact finite_one_overlap_reorder κ (fun a b c=>H (Fin.cons a (Fin.cons b (Fin.cons c z)))) i

theorem matrix_exchange_le_square (M : ι→ι→ℝ) :
    (∑ a,∑ b,M a b*M b a) ≤ ∑ a,∑ b,(M a b)^2 := by
  have hh : (∑ a,∑ b,2*(M a b*M b a)) ≤
      ∑ a,∑ b,((M a b)^2+(M b a)^2) := by
    exact Finset.sum_le_sum fun a _=>Finset.sum_le_sum fun b _=>
      by nlinarith [sq_nonneg (M a b-M b a)]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have he : (∑ a,∑ b,(M b a)^2)=(∑ a,∑ b,(M a b)^2) := Finset.sum_comm
  rw [he] at hh
  linarith

end KLSBelow25.TripleTensor
#print axioms KLSBelow25.TripleTensor.finite_one_overlap_reorder

#print axioms KLSBelow25.TripleTensor.overlap_one_pairing_eq_exchange
