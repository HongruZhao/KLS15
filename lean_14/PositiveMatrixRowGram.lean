import TensorRankOneCurvature
import Mathlib.Analysis.Matrix.Order

/-! A finite positive-semidefinite real matrix is an actual sum of
physical row-square rank-one matrices. The square root comes from
Mathlib's proved continuous functional calculus. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology MatrixOrder
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ}

lemma positiveMatrix_row_gram (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.PosSemidef) :
    ∃ v : Fin n → Fin n → ℝ, ∀ i j, K i j = ∑ s, v s i * v s j := by
  obtain ⟨B, hB, _, hBB⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
    hK.isHermitian (QuasispectrumRestricts.nnreal_of_nonneg hK.nonneg)
  refine ⟨B, ?_⟩
  intro i j
  have hs : B.IsSymm := (show B.IsHermitian from hB).isSymm
  calc
    K i j = (B * B) i j := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hBB.symm
    _ = ∑ s, B s i * B s j := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro s _
      rw [hs.apply i s]

lemma matrix_sub_scalar_identity_posSemidef (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : K.IsSymm) {a : ℝ}
    (hlower : ∀ v : Fin n → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (K *ᵥ v)) :
    (K - a • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · exact (Matrix.isHermitian_iff_isSymm.mpr hK).sub
      (Matrix.isHermitian_one.smul (show IsSelfAdjoint a from by simp [IsSelfAdjoint]))
  · intro v
    have h := hlower v
    simpa only [Pi.star_apply, star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_nonneg] using h

/-- Literal lower-bound-plus-rank-one decomposition of a real symmetric
matrix, derived from its actual quadratic lower bound. -/
theorem matrix_lower_row_gram (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : K.IsSymm) {a : ℝ}
    (hlower : ∀ v : Fin n → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (K *ᵥ v)) :
    ∃ v : Fin n → Fin n → ℝ, ∀ i j,
      K i j = (if i = j then a else 0) + ∑ s, v s i * v s j := by
  obtain ⟨v, hv⟩ := positiveMatrix_row_gram _ (matrix_sub_scalar_identity_posSemidef K hK hlower)
  refine ⟨v, ?_⟩
  intro i j
  have h := hv i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero] at h
  linarith

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.matrix_lower_row_gram
