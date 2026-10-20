import KLS.MatrixTracePositive

/-! Exact ordered-entry cutoff algebra for the same vector Bochner test.
No Jacobian symmetry or differential identity is assumed by the finite
expansion. The adjoint-square cancellation retains both signed errors. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualVectorCutoffAlgebra405
variable {n : ℕ}

theorem vector_cutoff_bochner_expansion
    (H D : Matrix (Fin n) (Fin n) ℝ) (u z : Fin n → ℝ) (c : ℝ) :
    (∑ i, ∑ j, (H i j * (c * u i) * (c * u j) +
      (c * D i j + z j * u i) * (c * D j i + z i * u j))) =
      c ^ 2 * ((∑ i, ∑ j, H i j * u i * u j) + (∑ i, ∑ j, D i j * D j i)) +
      2 * c * (∑ i, ∑ j, z j * u i * D j i) + (∑ i, z i * u i) ^ 2 := by
  have hp (i j : Fin n) : H i j * (c * u i) * (c * u j) +
      (c * D i j + z j * u i) * (c * D j i + z i * u j) =
      c ^ 2 * (H i j * u i * u j + D i j * D j i) +
      c * (z i * u j * D i j) + c * (z j * u i * D j i) +
      (z i * u i) * (z j * u j) := by ring
  have hs : (∑ i, ∑ j, z i * u j * D i j) = ∑ i, ∑ j, z j * u i * D j i :=
    Finset.sum_comm
  have hq : (∑ i, ∑ j, (z i * u i) * (z j * u j)) = (∑ i, z i * u i) ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact (Finset.mul_sum _ _ _).symm
  simp_rw [hp]
  simp only [Finset.sum_add_distrib]
  rw [hq]
  simp only [← Finset.mul_sum]
  rw [hs]
  simp only [Finset.sum_add_distrib]
  ring

theorem vector_cutoff_adjoint_square_cancellation
    {c g e cross dot : ℝ}
    (hbochner : (c * g - dot) ^ 2 = c ^ 2 * e + 2 * c * cross + dot ^ 2) :
    c ^ 2 * e = c ^ 2 * g ^ 2 - 2 * c * g * dot - 2 * c * cross := by
  nlinarith

end KLSConstantImprovement.ActualVectorCutoffAlgebra405
#print axioms KLSConstantImprovement.ActualVectorCutoffAlgebra405.vector_cutoff_bochner_expansion
#print axioms KLSConstantImprovement.ActualVectorCutoffAlgebra405.vector_cutoff_adjoint_square_cancellation
