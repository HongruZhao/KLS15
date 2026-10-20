import KLSConstantImprovement.ActualSourceCurvatureDomains405

/-! Literal row metric-Gram bounds. No symmetry of the row matrix is
assumed. Positivity belongs to its actual Gram F H F^T. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualResponseGramBound405
open KLS ActualSourceCurvatureDomains405
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

def metricRowMass (H : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) : ℝ :=
  u ⬝ᵥ (H *ᵥ u)

theorem metric_row_mass_two_sub (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosSemidef)
    (u z : Fin n → ℝ) :
    metricRowMass H (fun i => 2 * u i - z i) ≤ 8 * metricRowMass H u + 2 * metricRowMass H z := by
  have hp : 0 ≤ metricRowMass H (fun i => 2 * u i + z i) := hH.dotProduct_mulVec_nonneg _
  have he : metricRowMass H (fun i => 2 * u i - z i) +
      metricRowMass H (fun i => 2 * u i + z i) = 8 * metricRowMass H u + 2 * metricRowMass H z := by
    simp only [metricRowMass, dotProduct, Matrix.mulVec, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  linarith

theorem row_metric_gram_diagonal (H F : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (F * H * F.transpose) i i = metricRowMass H (F i) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, metricRowMass,
    dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem row_metric_gram_posSemidef (H F : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosSemidef) :
    (F * H * F.transpose).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using
    hH.conjTranspose_mul_mul_same F.transpose

theorem row_metric_gram_entry_bound (H F : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosSemidef)
    (C : ℝ) (hdiag : ∀ i, metricRowMass H (F i) ≤ C) (i j : Fin n) :
    ‖(F * H * F.transpose) i j‖ ≤ 2 * C := by
  have hp := posSemidef_abs_entry_le_diagonal_sum _ (row_metric_gram_posSemidef H F hH) i j
  rw [row_metric_gram_diagonal, row_metric_gram_diagonal] at hp
  rw [Real.norm_eq_abs]
  linarith [hdiag i, hdiag j]

end KLSConstantImprovement.ActualResponseGramBound405

#print axioms KLSConstantImprovement.ActualResponseGramBound405.metric_row_mass_two_sub
#print axioms KLSConstantImprovement.ActualResponseGramBound405.row_metric_gram_posSemidef
#print axioms KLSConstantImprovement.ActualResponseGramBound405.row_metric_gram_entry_bound
