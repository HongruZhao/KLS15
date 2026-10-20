import TripleTensorAdjoint
import ActualPairAppellYoung

noncomputable section
open scoped BigOperators
namespace KLSBelow25.TripleTensor
open PairTensor TripleProjection
variable {r : ℕ} {ι : Type*} [Fintype ι]

def frameCoordinateEquiv (F : Fin 3 ⊕ Fin r ≃ Fin (r+3)) :
    ((Fin 3→ι)×(Fin r→ι)) ≃ (Fin (r+3)→ι) :=
  (Equiv.sumArrowEquivProdArrow (Fin 3) (Fin r) ι).symm.trans
    (Equiv.arrowCongr F (Equiv.refl ι))

omit [Fintype ι] in
@[simp] theorem frameCoordinateEquiv_left (F : Fin 3 ⊕ Fin r ≃ Fin (r+3))
    (α : Fin 3→ι) (β : Fin r→ι) (i : Fin 3) :
    frameCoordinateEquiv F (α,β) (F (Sum.inl i))=α i := by
  change Sum.elim α β (F.symm (F (Sum.inl i)))=α i
  rw [Equiv.symm_apply_apply]
  rfl

omit [Fintype ι] in
@[simp] theorem frameCoordinateEquiv_right (F : Fin 3 ⊕ Fin r ≃ Fin (r+3))
    (α : Fin 3→ι) (β : Fin r→ι) (i : Fin r) :
    frameCoordinateEquiv F (α,β) (F (Sum.inr i))=β i := by
  change Sum.elim α β (F.symm (F (Sum.inr i)))=β i
  rw [Equiv.symm_apply_apply]
  rfl

theorem kernel_frame_square_le (κ : ι→ι→ι→ι→ℝ)
    (H : Tensor (ι:=ι) (r+1)) (F : Fin 3 ⊕ Fin r ≃ Fin (r+3)) {L : ℝ}
    (hκ : ∀ v : ι→ℝ,
      (∑ α : Fin 3→ι,(∑ m,κ (α 0) (α 1) (α 2) m*v m)^2) ≤ L*(∑ m,(v m)^2)) :
    square (kernelInFrame κ H F) ≤ L*square H := by
  unfold square
  rw [←(frameCoordinateEquiv F).sum_comp]
  simp only [Fintype.sum_prod_type,kernelInFrame,frameCoordinateEquiv_left,
    frameCoordinateEquiv_right]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ β : Fin r→ι,L*(∑ m,(H (Fin.cons m β))^2) :=
      Finset.sum_le_sum fun β _ => hκ (fun m => H (Fin.cons m β))
    _ = L*(∑ a : Fin (r+1)→ι,(H a)^2) := by
      rw [←Finset.mul_sum,Finset.sum_comm]
      congr 1
      exact (sum_cons_coordinates (fun a => H a^2)).symm

theorem kernel_square_le (κ : ι→ι→ι→ι→ℝ)
    (H : Tensor (ι:=ι) (r+1)) (e : Triple (r+3)) {L : ℝ}
    (hκ : ∀ v : ι→ℝ,
      (∑ α : Fin 3→ι,(∑ m,κ (α 0) (α 1) (α 2) m*v m)^2) ≤ L*(∑ m,(v m)^2)) :
    square (kernel κ H e) ≤ L*square H :=
  kernel_frame_square_le κ H (tripleFrame e) hκ

theorem kernel_pairing_le (κ : ι→ι→ι→ι→ℝ)
    (H : Tensor (ι:=ι) (r+1)) (e f : Triple (r+3)) {L : ℝ}
    (hκ : ∀ v : ι→ℝ,
      (∑ α : Fin 3→ι,(∑ m,κ (α 0) (α 1) (α 2) m*v m)^2) ≤ L*(∑ m,(v m)^2)) :
    pairing (kernel κ H e) (kernel κ H f) ≤ L*square H := by
  have h := pairing_young (by norm_num : (0:ℝ)<1) (kernel κ H e) (kernel κ H f)
  have he := kernel_square_le κ H e hκ
  have hf := kernel_square_le κ H f hκ
  norm_num at h
  linarith

end KLSBelow25.TripleTensor
#print axioms KLSBelow25.TripleTensor.kernel_frame_square_le
#print axioms KLSBelow25.TripleTensor.kernel_pairing_le
