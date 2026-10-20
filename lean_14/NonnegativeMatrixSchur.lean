import Mathlib

/-! The finite row/column Schur estimate used by the critical weighted
exponential observation model. No Appell correspondence is assumed here. -/
noncomputable section
open scoped BigOperators
namespace KLSImprovement.NonnegativeSchur

theorem weighted_sum_square_le {κ : Type*} [Fintype κ]
    (a c : κ → ℝ) (ha : ∀ k, 0 ≤ a k) :
    (∑ k, a k*c k)^2 ≤ (∑ k, a k)*(∑ k, a k*(c k)^2) := by
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun k _ => ha k) (fun k _ => mul_nonneg (ha k) (sq_nonneg _))
    (fun k _ => by ring_nf; exact le_rfl)

theorem finite_row_column_square_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) {R C : ℝ} (hR : 0 ≤ R)
    (hA : ∀ i k, 0 ≤ A i k)
    (hrow : ∀ i, ∑ k, A i k ≤ R)
    (hcolumn : ∀ k, ∑ i, A i k ≤ C) (c : κ → ℝ) :
    (∑ i, (∑ k, A i k*c k)^2) ≤ R*C*(∑ k, (c k)^2) := by
  calc
    _ ≤ ∑ i, R*(∑ k, A i k*(c k)^2) := by
      apply Finset.sum_le_sum
      intro i _
      exact (weighted_sum_square_le (A i) c (hA i)).trans
        (mul_le_mul_of_nonneg_right (hrow i)
          (Finset.sum_nonneg (fun k _ => mul_nonneg (hA i k) (sq_nonneg _))))
    _ = R*(∑ k, (∑ i, A i k)*(c k)^2) := by
      simp_rw [←Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
    _ ≤ R*(∑ k, C*(c k)^2) := by
      apply mul_le_mul_of_nonneg_left _ hR
      exact Finset.sum_le_sum (fun k _ =>
        mul_le_mul_of_nonneg_right (hcolumn k) (sq_nonneg _))
    _ = _ := by rw [←Finset.mul_sum]; ring

end KLSImprovement.NonnegativeSchur
#print axioms KLSImprovement.NonnegativeSchur.weighted_sum_square_le
#print axioms KLSImprovement.NonnegativeSchur.finite_row_column_square_bound
