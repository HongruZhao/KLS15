import TripleTensorAdjoint
import PairTensorAnnihilation
import TripleProjectionCounts

/-! Actual first-slot symmetrization and the exact binomial adjoint factor
for the literal fourth-cumulant triple insertion map. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.TripleTensor
open TripleProjection PairTensor
variable {r : ℕ} {ι : Type*} [Fintype ι]
set_option maxHeartbeats 1500000

theorem annihilation_tail_symmetric (κ : ι→ι→ι→ι→ℝ)
    (T : Tensor (ι:=ι) (r+4)) (hT : Symmetric T) :
    TailSymmetric (annihilation κ T) := by
  intro π hπ a
  unfold annihilation
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [Function.comp_def,hπ]
  congr 1
  have hfix1 : fixHeadPerm (fixHeadPerm π) (1 : Fin (r+4))=1 := by
    have h1 : (1 : Fin (r+4))=(0 : Fin (r+3)).succ := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt (by omega : 1<r+4)]
    rw [h1,fixHeadPerm_succ,fixHeadPerm_zero]
  have hw : Fin.cons i (Fin.cons j (Fin.cons k (Fin.tail (a∘π)))) =
      Fin.cons i (Fin.cons j (Fin.cons k (Fin.tail a))) ∘
        fixHeadPerm (fixHeadPerm π) := by
    rw [cons_tail_comp_of_fix_zero a k π hπ]
    funext l
    refine Fin.cases ?_ (fun m => ?_) l
    · simp [Function.comp_def]
    · refine Fin.cases ?_ (fun p => ?_) m <;> simp [Function.comp_def,hfix1]
  change T (Fin.cons i (Fin.cons j (Fin.cons k (Fin.tail (a∘π)))))=_
  rw [hw]
  exact hT (fixHeadPerm (fixHeadPerm π)) _

theorem symmetric_annihilation_square_le (κ : ι→ι→ι→ι→ℝ)
    (T : Tensor (ι:=ι) (r+4)) (hT : Symmetric T) (B : ℝ) (hB : 0 ≤ B)
    (hC : ∀ H : Tensor (ι:=ι) (r+2),Symmetric H → square (creation κ H) ≤ B*square H) :
    square (firstSym (annihilation κ T)) ≤
      (B/(Nat.choose (r+4) 3 : ℝ)^2)*square T := by
  let H := firstSym (annihilation κ T)
  have hH : Symmetric H := firstSym_symmetric _ (annihilation_tail_symmetric κ T hT)
  have hp := creation_pairing κ H T hT
  rw [card_triple] at hp
  have hp' : pairing H (annihilation κ T)=square H := by
    rw [←pairing_firstSym H (annihilation κ T) hH]
    simp only [H,pairing,square,pow_two]
  rw [hp'] at hp
  have hc := pairing_sq_le (creation κ H) T
  have hb := mul_le_mul_of_nonneg_right (hC H hH) (square_nonneg T)
  rw [hp] at hc
  have hn : 0 < (Nat.choose (r+4) 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 3 ≤ r+4)
  have hh := square_nonneg H
  by_cases hz : square H=0
  · change square H ≤ _
    rw [hz]
    exact mul_nonneg (div_nonneg hB (sq_nonneg _)) (square_nonneg T)
  · have hpos : 0 < square H := lt_of_le_of_ne hh (Ne.symm hz)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
    change square H*(Nat.choose (r+4) 3 : ℝ)^2 ≤ B*square T
    nlinarith

theorem annihilation_exchange_le (κ : ι→ι→ι→ι→ℝ)
    (T : Tensor (ι:=ι) (r+4)) (hT : Symmetric T) (B : ℝ) (hB : 0 ≤ B)
    (hC : ∀ H : Tensor (ι:=ι) (r+2),Symmetric H → square (creation κ H) ≤ B*square H) :
    exchange (annihilation κ T) ≤ (B/(Nat.choose (r+4) 3 : ℝ)^2)*square T := by
  exact (exchange_le_firstSym_square _ (annihilation_tail_symmetric κ T hT)).trans
    (symmetric_annihilation_square_le κ T hT B hB hC)

end KLSBelow25.TripleTensor
#print axioms KLSBelow25.TripleTensor.annihilation_exchange_le
