import TripleTensorRepresentatives

/-! The literal triple insertion family has four Gram classes, determined
solely by intersection cardinality. Empty classes are assigned zero. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.TripleTensor
open PairTensor TripleProjection
variable {r : ℕ} {ι : Type*} [Fintype ι]
set_option maxHeartbeats 1500000

def gramValue (κ : ι→ι→ι→ι→ℝ) (H : Tensor (ι:=ι) (r+1)) (k : ℕ) : ℝ :=
  if h : ∃ e f : Triple (r+3),(e.val∩f.val).card=k then
    pairing (kernel κ H h.choose) (kernel κ H h.choose_spec.choose)
  else 0

theorem gramValue_eq (κ : ι→ι→ι→ι→ℝ)
    (hκ : ∀ m,Symmetric (fun a : Fin 3→ι => κ (a 0) (a 1) (a 2) m))
    (H : Tensor (ι:=ι) (r+1)) (hH : Symmetric H) (e f : Triple (r+3))
    (k : ℕ) (hk : (e.val∩f.val).card=k) :
    gramValue κ H k=pairing (kernel κ H e) (kernel κ H f) := by
  classical
  have he : ∃ e f : Triple (r+3),(e.val∩f.val).card=k := ⟨e,f,hk⟩
  unfold gramValue
  rw [dite_eq_left he]
  apply kernel_pairing_eq_of_intersection_card κ hκ H hH
  exact he.choose_spec.choose_spec.trans hk.symm

theorem kernel_gram (κ : ι→ι→ι→ι→ℝ)
    (hκ : ∀ m,Symmetric (fun a : Fin 3→ι => κ (a 0) (a 1) (a 2) m))
    (H : Tensor (ι:=ι) (r+1)) (hH : Symmetric H) :
    Gram (fun e => toHilbert (kernel κ H e))
      (gramValue κ H 3) (gramValue κ H 2) (gramValue κ H 1) (gramValue κ H 0) := by
  intro e f
  rw [toHilbert_inner]
  have hc := triple_intersection_card_le_three e f
  split_ifs with h3 h2 h1
  · exact (gramValue_eq κ hκ H hH e f 3 h3).symm
  · exact (gramValue_eq κ hκ H hH e f 2 h2).symm
  · exact (gramValue_eq κ hκ H hH e f 1 h1).symm
  · exact (gramValue_eq κ hκ H hH e f 0 (by omega)).symm

theorem gramValue_le_of_pairing_le (κ : ι→ι→ι→ι→ℝ)
    (H : Tensor (ι:=ι) (r+1)) (k : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ e f : Triple (r+3),pairing (kernel κ H e) (kernel κ H f) ≤ B) :
    gramValue κ H k ≤ B := by
  classical
  unfold gramValue
  split_ifs
  · exact h _ _
  · exact hB

theorem creation_square_le_card (κ : ι→ι→ι→ι→ℝ)
    (H : Tensor (ι:=ι) (r+1)) {L : ℝ}
    (h : ∀ e : Triple (r+3),square (kernel κ H e) ≤ L*square H) :
    square (creation κ H) ≤ (Fintype.card (Triple (r+3)) : ℝ)^2*L*square H := by
  have hn : 0 ≤ (Fintype.card (Triple (r+3)) : ℝ) := Nat.cast_nonneg _
  have hc (a : Fin (r+3)→ι) :
      (∑ e,kernel κ H e a)^2 ≤
        (Fintype.card (Triple (r+3)) : ℝ)*(∑ e,(kernel κ H e a)^2) := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Triple (r+3)))
      (fun _ => (1:ℝ)) (fun e => kernel κ H e a)
  calc
    square (creation κ H) ≤
      ∑ a,(Fintype.card (Triple (r+3)) : ℝ)*(∑ e,(kernel κ H e a)^2) :=
        Finset.sum_le_sum fun a _ => hc a
    _ = (Fintype.card (Triple (r+3)) : ℝ)*(∑ e,square (kernel κ H e)) := by
      rw [←Finset.mul_sum,Finset.sum_comm]
      rfl
    _ ≤ (Fintype.card (Triple (r+3)) : ℝ)*(∑ _e : Triple (r+3),L*square H) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => h e) hn
    _ = (Fintype.card (Triple (r+3)) : ℝ)^2*L*square H := by simp;ring

end KLSBelow25.TripleTensor
#print axioms KLSBelow25.TripleTensor.kernel_gram
#print axioms KLSBelow25.TripleTensor.creation_square_le_card
