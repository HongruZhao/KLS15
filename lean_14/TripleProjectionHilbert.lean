import TripleProjectionCounts
import PairProjectionCreationBound

/-! Exact squared norm of a triple insertion sum, including the distinct
one-overlap and two-overlap terms. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace KLSBelow25.TripleProjection
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem gram_linear (U : Triple N → H) {Q₃ Q₂ Q₁ Q₀ : ℝ}
    (h : Gram U Q₃ Q₂ Q₁ Q₀) (e f : Triple N) :
    inner ℝ (U e) (U f) =
      (if e=f then Q₃-3*Q₂+3*Q₁-Q₀ else 0) +
      (Q₂-2*Q₁+Q₀)*(((e.val ∩ f.val).card).choose 2 : ℝ) +
      (Q₁-Q₀)*((e.val ∩ f.val).card : ℝ)+Q₀ := by
  have hl := triple_intersection_card_le_three e f
  have he := triple_intersection_card_eq_three_iff e f
  rw [h e f]
  interval_cases hc : (e.val ∩ f.val).card <;>
    norm_num at he ⊢ <;> simp_all <;> ring

def row (N : ℕ) (Q₃ Q₂ Q₁ Q₀ : ℝ) : ℝ :=
  Q₃-3*Q₂+3*Q₁-Q₀ +
  (Q₂-2*Q₁+Q₀)*(3*(N-2 : ℕ)) +
  (Q₁-Q₀)*(3*((N-1).choose 2 : ℝ)) + Q₀*(N.choose 3 : ℝ)

theorem gram_row_sum (U : Triple N → H) {Q₃ Q₂ Q₁ Q₀ : ℝ}
    (h : Gram U Q₃ Q₂ Q₁ Q₀) (e : Triple N) :
    (∑ f,inner ℝ (U e) (U f))=row N Q₃ Q₂ Q₁ Q₀ := by
  have h₁ : (∑ f : Triple N, ((e.val ∩ f.val).card : ℝ)) =
      3*((N-1).choose 2 : ℝ) := by
    exact_mod_cast (by simpa using triple_intersection_moment e 1 (by omega))
  have h₂ : (∑ f : Triple N, (((e.val ∩ f.val).card).choose 2 : ℝ)) =
      3*(N-2 : ℕ) := by
    exact_mod_cast (by simpa using triple_intersection_moment e 2 (by omega))
  simp_rw [gram_linear U h e]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ←Finset.mul_sum, ←Finset.mul_sum, h₁, h₂]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, card_triple]
  unfold row
  ring

theorem sumTriples_sq (U : Triple N → H) {Q₃ Q₂ Q₁ Q₀ : ℝ}
    (h : Gram U Q₃ Q₂ Q₁ Q₀) :
    ‖sumTriples U‖^2 = (N.choose 3 : ℝ)*row N Q₃ Q₂ Q₁ Q₀ := by
  rw [←real_inner_self_eq_norm_sq]
  unfold sumTriples
  simp_rw [sum_inner, inner_sum, gram_row_sum U h]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_triple]

theorem sumTriples_sq_expanded (U : Triple N → H) {Q₃ Q₂ Q₁ Q₀ : ℝ}
    (h : Gram U Q₃ Q₂ Q₁ Q₀) (hN : 3≤N) :
    ‖sumTriples U‖^2 =
      ((N : ℝ)*(N-1)*(N-2)/6)*Q₃ +
      ((N : ℝ)*(N-1)*(N-2)*(N-3)/2)*Q₂ +
      ((N : ℝ)*(N-1)*(N-2)*(N-3)*(N-4)/4)*Q₁ +
      ((N : ℝ)*(N-1)*(N-2)*(N-3)*(N-4)*(N-5)/36)*Q₀ := by
  rw [sumTriples_sq U h]
  unfold row
  rw [KLSBelow25.PairProjection.cast_choose_three (by omega), Nat.cast_choose_two,
    Nat.cast_sub (by omega : 2≤N), Nat.cast_sub (by omega : 1≤N)]
  norm_num only [Nat.cast_ofNat]
  ring

theorem cast_choose_five (hN : 4≤N) :
    (N.choose 5 : ℝ)=(N : ℝ)*(N-1)*(N-2)*(N-3)*(N-4)/120 := by
  have hh := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq N 4)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hh
  rw [KLSBelow25.PairProjection.cast_choose_four (by omega), Nat.cast_sub hN] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem cast_choose_six (hN : 5≤N) :
    (N.choose 6 : ℝ)=(N : ℝ)*(N-1)*(N-2)*(N-3)*(N-4)*(N-5)/720 := by
  have hh := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq N 5)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hh
  rw [cast_choose_five (by omega), Nat.cast_sub hN] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem sumTriples_sq_choose (U : Triple N → H) {Q₃ Q₂ Q₁ Q₀ : ℝ}
    (h : Gram U Q₃ Q₂ Q₁ Q₀) (hN : 5≤N) :
    ‖sumTriples U‖^2 = (N.choose 3 : ℝ)*Q₃ +
      12*(N.choose 4 : ℝ)*Q₂ + 30*(N.choose 5 : ℝ)*Q₁ +
      20*(N.choose 6 : ℝ)*Q₀ := by
  rw [sumTriples_sq_expanded U h (by omega),
    KLSBelow25.PairProjection.cast_choose_three (by omega),
    KLSBelow25.PairProjection.cast_choose_four (by omega),
    cast_choose_five (by omega), cast_choose_six hN]
  ring

end KLSBelow25.TripleProjection
#print axioms KLSBelow25.TripleProjection.gram_row_sum
#print axioms KLSBelow25.TripleProjection.sumTriples_sq_expanded
#print axioms KLSBelow25.TripleProjection.sumTriples_sq_choose
