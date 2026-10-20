import PairTensorAdjoint
import FirstSlotSymmetrization
import PairProjectionCounts

noncomputable section
open scoped BigOperators
namespace KLSBelow25.PairTensor
open PairProjection
variable {r : ℕ} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem cons_tail_eq_of_ne_zero (a : Fin (r+1) → ι) (j : ι)
    (k : Fin (r+1)) (hk : k ≠ 0) : Fin.cons j (Fin.tail a) k = a k := by
  exact Fin.cases (fun h => (h rfl).elim) (fun _ _ => rfl) k hk

omit [Fintype ι] in
theorem cons_tail_comp_of_fix_zero (a : Fin (r+1) → ι) (j : ι)
    (π : Equiv.Perm (Fin (r+1))) (hπ : π 0=0) :
    Fin.cons j (Fin.tail (a ∘ π)) = Fin.cons j (Fin.tail a) ∘ π := by
  funext k
  refine Fin.cases ?_ (fun l => ?_) k
  · simp [Function.comp_def,hπ]
  · have hn : π l.succ≠0 := by
      intro he
      have hh := π.injective (he.trans hπ.symm)
      exact Fin.succ_ne_zero l hh
    simp only [Fin.cons_succ,Fin.tail,Function.comp_def]
    exact (cons_tail_eq_of_ne_zero a j (π l.succ) hn).symm

theorem annihilation_tail_symmetric (κ : ι → ι → ι → ℝ)
    (T : Tensor (ι := ι) (r+3)) (hT : Symmetric T) :
    TailSymmetric (annihilation κ T) := by
  intro π hπ a
  unfold annihilation
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp_def,hπ]
  congr 1
  have hw : Fin.cons i (Fin.cons j (Fin.tail (a ∘ π))) =
      Fin.cons i (Fin.cons j (Fin.tail a)) ∘ fixHeadPerm π := by
    rw [cons_tail_comp_of_fix_zero a j π hπ]
    funext k
    refine Fin.cases ?_ (fun l => ?_) k <;> simp [Function.comp_def]
  change T (Fin.cons i (Fin.cons j (Fin.tail (a ∘ π)))) = _
  rw [hw]
  exact hT (fixHeadPerm π) _

theorem pairing_sq_le {d : ℕ} (S T : Tensor (ι := ι) d) :
    (pairing S T)^2 ≤ square S*square T := by
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ S T

theorem symmetric_annihilation_square_le (κ : ι → ι → ι → ℝ)
    (T : Tensor (ι := ι) (r+3)) (hT : Symmetric T) (B : ℝ) (hB : 0≤B)
    (hC : ∀ H : Tensor (ι := ι) (r+2), Symmetric H →
      square (creation κ H) ≤ B*square H) :
    square (firstSym (annihilation κ T)) ≤
      (B/(Nat.choose (r+3) 2 : ℝ)^2)*square T := by
  let H := firstSym (annihilation κ T)
  have hH : Symmetric H := firstSym_symmetric _ (annihilation_tail_symmetric κ T hT)
  have hp := creation_pairing κ H T hT
  rw [card_pair] at hp
  have hp' : pairing H (annihilation κ T) = square H := by
    rw [←pairing_firstSym H (annihilation κ T) hH]
    simp only [H,pairing,square,pow_two]
  rw [hp'] at hp
  have hc := pairing_sq_le (creation κ H) T
  have hb := mul_le_mul_of_nonneg_right (hC H hH) (square_nonneg T)
  rw [hp] at hc
  have hn : 0 < (Nat.choose (r+3) 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2≤r+3)
  have hh := square_nonneg H
  by_cases hz : square H=0
  · change square H≤_
    rw [hz]
    exact mul_nonneg (div_nonneg hB (sq_nonneg _)) (square_nonneg T)
  · have hpos : 0<square H := lt_of_le_of_ne hh (Ne.symm hz)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
    change square H * (Nat.choose (r+3) 2 : ℝ)^2 ≤ B*square T
    nlinarith

theorem annihilation_exchange_le (κ : ι → ι → ι → ℝ)
    (T : Tensor (ι := ι) (r+3)) (hT : Symmetric T) (B : ℝ) (hB : 0≤B)
    (hC : ∀ H : Tensor (ι := ι) (r+2), Symmetric H →
      square (creation κ H) ≤ B*square H) :
    exchange (annihilation κ T) ≤
      (B/(Nat.choose (r+3) 2 : ℝ)^2)*square T := by
  exact (exchange_le_firstSym_square _ (annihilation_tail_symmetric κ T hT)).trans
    (symmetric_annihilation_square_le κ T hT B hB hC)

end KLSBelow25.PairTensor
#print axioms KLSBelow25.PairTensor.annihilation_exchange_le
