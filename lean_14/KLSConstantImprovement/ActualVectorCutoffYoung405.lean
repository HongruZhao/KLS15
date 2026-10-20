import KLSConstantImprovement.ActualVectorCutoffAlgebra405
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The finite Young estimate used only to establish the fixed-parameter
global Jacobian domain. Its ellipticity parameter is not the final
Gaffney constant. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualVectorCutoffYoung405
variable {n : ℕ}

theorem vector_cutoff_signed_error_young (D : Matrix (Fin n) (Fin n) ℝ)
    (u z : Fin n → ℝ) (c g : ℝ) {ell : ℝ} (hell : 0 ≤ ell) :
    ell * (-2 * c * g * (∑ i, z i * u i) -
      2 * c * (∑ i, ∑ j, z j * u i * D j i)) ≤
      ell * c ^ 2 * g ^ 2 + (ell + 2) * (∑ j, z j ^ 2) * (∑ i, u i ^ 2) +
        (ell ^ 2 / 2) * c ^ 2 * (∑ i, ∑ j, D i j ^ 2) := by
  have hdot : (∑ i, z i * u i) ^ 2 ≤ (∑ i, z i ^ 2) * (∑ i, u i ^ 2) := by
    simpa only [← pow_two] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ z u
  have hforce : -2 * c * g * (∑ i, z i * u i) ≤
      c ^ 2 * g ^ 2 + (∑ j, z j ^ 2) * (∑ i, u i ^ 2) := by
    nlinarith [sq_nonneg (c * g + ∑ i, z i * u i)]
  have hpoint (i j : Fin n) : -2 * ell * c * (z j * u i * D j i) ≤
      (ell ^ 2 / 2) * c ^ 2 * D j i ^ 2 + 2 * z j ^ 2 * u i ^ 2 := by
    nlinarith [sq_nonneg (ell * c * D j i + 2 * z j * u i)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpoint i j))
  have hleft : (∑ i : Fin n, ∑ j : Fin n, -2 * ell * c * (z j * u i * D j i)) =
      -2 * ell * c * (∑ i, ∑ j, z j * u i * D j i) := by
    simp only [← Finset.mul_sum]
  have hright : (∑ i : Fin n, ∑ j : Fin n,
      ((ell ^ 2 / 2) * c ^ 2 * D j i ^ 2 + 2 * z j ^ 2 * u i ^ 2)) =
      (ell ^ 2 / 2) * c ^ 2 * (∑ i, ∑ j, D i j ^ 2) +
        2 * (∑ j, z j ^ 2) * (∑ i, u i ^ 2) := by
    simp only [Finset.sum_add_distrib]
    congr 1
    · simp only [← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
    · calc
        _ = ∑ i : Fin n, ∑ j : Fin n, 2 * u i ^ 2 * z j ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = 2 * (∑ j, z j ^ 2) * (∑ i, u i ^ 2) := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
          ring
  rw [hleft, hright] at hsum
  have hf := mul_le_mul_of_nonneg_left hforce hell
  nlinarith only [hf, hsum]

end KLSConstantImprovement.ActualVectorCutoffYoung405
#print axioms KLSConstantImprovement.ActualVectorCutoffYoung405.vector_cutoff_signed_error_young
