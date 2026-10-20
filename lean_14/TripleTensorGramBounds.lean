import TripleTensorGram

noncomputable section
open scoped BigOperators
namespace KLSBelow25.TripleTensor
open PairTensor TripleProjection
variable {r : ℕ} {ι : Type*} [Fintype ι]
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem gramValue_three_eq_square (κ : ι→ι→ι→ι→ℝ)
    (hκ : ∀ m,Symmetric (fun a : Fin 3→ι => κ (a 0) (a 1) (a 2) m))
    (H : Tensor (ι:=ι) (r+1)) (hH : Symmetric H) (e : Triple (r+3)) :
    gramValue κ H 3=square (kernel κ H e) := by
  rw [gramValue_eq κ hκ H hH e e 3 (by simp [e.property])]
  simp only [pairing,square,pow_two]

theorem kernel_pairing_le_diagonal (κ : ι→ι→ι→ι→ℝ)
    (hκ : ∀ m,Symmetric (fun a : Fin 3→ι => κ (a 0) (a 1) (a 2) m))
    (H : Tensor (ι:=ι) (r+1)) (hH : Symmetric H) (e f : Triple (r+3)) :
    pairing (kernel κ H e) (kernel κ H f) ≤ gramValue κ H 3 := by
  have he := gramValue_three_eq_square κ hκ H hH e
  have hf := gramValue_three_eq_square κ hκ H hH f
  have hp : 2*pairing (kernel κ H e) (kernel κ H f) ≤
      square (kernel κ H e)+square (kernel κ H f) := by
    have hh := Finset.sum_le_sum (s:=Finset.univ) (fun a _ =>
      (show 2*kernel κ H e a*kernel κ H f a ≤
        (kernel κ H e a)^2+(kernel κ H f a)^2 by
        nlinarith [sq_nonneg (kernel κ H e a-kernel κ H f a)]))
    simpa only [←Finset.mul_sum,Finset.sum_add_distrib,pairing,square,mul_assoc] using hh
  linarith

theorem gramValue_two_le_three (κ : ι→ι→ι→ι→ℝ)
    (hκ : ∀ m,Symmetric (fun a : Fin 3→ι => κ (a 0) (a 1) (a 2) m))
    (H : Tensor (ι:=ι) (r+1)) (hH : Symmetric H) :
    gramValue κ H 2≤gramValue κ H 3 := by
  exact gramValue_le_of_pairing_le κ H 2
    (by rw [gramValue_three_eq_square κ hκ H hH (prefixTriple r)];exact square_nonneg _)
    (kernel_pairing_le_diagonal κ hκ H hH)

theorem gramValue_zero_of_lt_six (κ : ι→ι→ι→ι→ℝ)
    (H : Tensor (ι:=ι) (r+1)) (hr : r+3<6) : gramValue κ H 0=0 := by
  classical
  have hn : ¬∃ e f : Triple (r+3),(e.val∩f.val).card=0 := by
    rintro ⟨e,f,hef⟩
    have hcard := Finset.card_union_add_card_inter e.val f.val
    have hbound : (e.val∪f.val).card≤r+3 := by
      simpa using (Finset.card_le_univ (s:=e.val∪f.val))
    rw [e.property,f.property,hef] at hcard
    omega
  simp only [gramValue,dite_eq_right hn]

end KLSBelow25.TripleTensor
#print axioms KLSBelow25.TripleTensor.gramValue_two_le_three
#print axioms KLSBelow25.TripleTensor.gramValue_zero_of_lt_six
