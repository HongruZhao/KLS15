import PairTensorPermutation
import PairTensorHilbert
import PairProjectionCounts

/-! The genuine pair insertion kernels have a three-class Gram matrix.
This is a consequence of literal coordinate permutation invariance, not an
assumed orthogonality or a bound on a surrogate tensor. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.PairTensor
open PairProjection
variable {r : ℕ} {ι : Type*} [Fintype ι]

theorem kernel_gram_of_representatives (κ : ι → ι → ι → ℝ)
    (hκ : ∀ i j m,κ i j m=κ j i m) (H : Tensor (ι := ι) (r+1)) (hH : Symmetric H)
    (e₀ e₁ e₂ : Pair (r+2))
    (h01 : (e₀.val ∩ e₁.val).card=1) (h02 : (e₀.val ∩ e₂.val).card=0) :
    Gram (fun e => toHilbert (kernel κ H e))
      (pairing (kernel κ H e₀) (kernel κ H e₀))
      (pairing (kernel κ H e₀) (kernel κ H e₁))
      (pairing (kernel κ H e₀) (kernel κ H e₂)) := by
  intro e f
  rw [toHilbert_inner]
  split_ifs with hef hint
  · subst f
    apply kernel_pairing_eq_of_intersection_card κ hκ H hH
    simp [e.property,e₀.property]
  · apply kernel_pairing_eq_of_intersection_card κ hκ H hH
    rw [pair_intersection_card_of_ne hef hint,h01]
  · apply kernel_pairing_eq_of_intersection_card κ hκ H hH
    rw [Finset.not_nonempty_iff_eq_empty.mp hint,Finset.card_empty,h02]

theorem kernel_gram_of_no_disjoint (κ : ι → ι → ι → ℝ)
    (hκ : ∀ i j m,κ i j m=κ j i m) (H : Tensor (ι := ι) (r+1)) (hH : Symmetric H)
    (e₀ e₁ : Pair (r+2)) (h01 : (e₀.val ∩ e₁.val).card=1)
    (hn : ∀e f : Pair (r+2),(e.val ∩ f.val).Nonempty) :
    Gram (fun e => toHilbert (kernel κ H e))
      (pairing (kernel κ H e₀) (kernel κ H e₀))
      (pairing (kernel κ H e₀) (kernel κ H e₁)) 0 := by
  intro e f
  rw [toHilbert_inner]
  split_ifs with hef hint
  · subst f
    apply kernel_pairing_eq_of_intersection_card κ hκ H hH
    simp [e.property,e₀.property]
  · apply kernel_pairing_eq_of_intersection_card κ hκ H hH
    rw [pair_intersection_card_of_ne hef hint,h01]
  · exact (hint (hn e f)).elim

theorem pairs_three_intersect (e f : Pair 3) : (e.val ∩ f.val).Nonempty := by
  have hu := Finset.card_le_card (Finset.subset_univ (e.val ∪ f.val))
  have hc := Finset.card_union_add_card_inter e.val f.val
  have hp : 0 < (e.val ∩ f.val).card := by
    simp only [Finset.card_univ,Fintype.card_fin] at hu
    rw [e.property,f.property] at hc
    omega
  exact Finset.card_pos.mp hp

theorem kernel_pairing_symmetric (κ : ι → ι → ι → ℝ)
    (H : Tensor (ι := ι) (r+1)) (e f : Pair (r+2)) :
    pairing (kernel κ H e) (kernel κ H f) = pairing (kernel κ H f) (kernel κ H e) := by
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

end KLSBelow25.PairTensor
#print axioms KLSBelow25.PairTensor.kernel_gram_of_representatives
