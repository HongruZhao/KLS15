import TensorHodgeProjectedAdjoint

/-! The physical creation row on ordered symmetric tensor coordinates.
A rank-(q+1) symmetric tensor is represented by its q auxiliary slots and
one distinguished slot. The annihilation row is the actual first-slot
contraction multiplied by √(q+1); its adjoint is creation. The estimate is
proved from the literal ordered Euclidean norm, without a basis assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n q : ℕ}

/-- The annihilation row in the physical ordered-coordinate realization.
Its target includes all auxiliary tensors; on symmetric input its auxiliary
slices are symmetric automatically. -/
def tensorAnnihilationRow (n q : ℕ) :
    ↥(tensorOneFormSymmetricFiber n q) →L[ℝ]
      EuclideanSpace ℝ (TensorOneFormIndex n q) :=
  Real.sqrt (q + 1 : ℕ) • (tensorOneFormSymmetricFiber n q).subtypeL

/-- Creation is the genuine Hilbert adjoint of the physical contraction row. -/
def tensorCreationRow (n q : ℕ) :
    EuclideanSpace ℝ (TensorOneFormIndex n q) →L[ℝ]
      ↥(tensorOneFormSymmetricFiber n q) :=
  (tensorAnnihilationRow n q).adjoint

@[simp] lemma tensorAnnihilationRow_apply
    (v : ↥(tensorOneFormSymmetricFiber n q)) :
    tensorAnnihilationRow n q v = Real.sqrt (q + 1 : ℕ) • (v : EuclideanSpace ℝ _) := rfl

lemma tensorAnnihilationRow_norm
    (v : ↥(tensorOneFormSymmetricFiber n q)) :
    ‖tensorAnnihilationRow n q v‖ = Real.sqrt (q + 1 : ℕ) * ‖v‖ := by
  rw [tensorAnnihilationRow_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rfl

lemma tensorAnnihilationRow_opNorm_le :
    ‖tensorAnnihilationRow n q‖ ≤ Real.sqrt (q + 1 : ℕ) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v =>
    le_of_eq (tensorAnnihilationRow_norm v)

lemma tensorCreationRow_pairing
    (v : ↥(tensorOneFormSymmetricFiber n q))
    (w : EuclideanSpace ℝ (TensorOneFormIndex n q)) :
    inner ℝ v (tensorCreationRow n q w) =
      Real.sqrt (q + 1 : ℕ) * inner ℝ (v : EuclideanSpace ℝ _) w := by
  rw [tensorCreationRow, ContinuousLinearMap.adjoint_inner_right,
    tensorAnnihilationRow_apply, real_inner_smul_left]

/-- In ordered coordinates the physical creation row is √(q+1) times
literal full symmetrization. -/
theorem tensorCreationRow_coe
    (w : EuclideanSpace ℝ (TensorOneFormIndex n q)) :
    ((tensorCreationRow n q w : ↥(tensorOneFormSymmetricFiber n q)) :
      EuclideanSpace ℝ (TensorOneFormIndex n q)) =
        Real.sqrt (q + 1 : ℕ) • tensorOneFormProjection n q w := by
  change ((tensorOneFormSymmetricFiber n q).subtypeL.comp
    ((Real.sqrt (q + 1 : ℕ) • (tensorOneFormSymmetricFiber n q).subtypeL).adjoint)) w = _
  rw [map_smul]
  simp only [conj_trivial, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul]
  rw [← ContinuousLinearMap.comp_apply]
  change Real.sqrt (q + 1 : ℕ) •
    (((tensorOneFormSymmetricFiber n q).subtypeL.comp
      (tensorOneFormSymmetricFiber n q).subtypeL.adjoint) w) = _
  rw [Submodule.adjoint_subtypeL]
  rfl

lemma tensorCreationRow_opNorm_le :
    ‖tensorCreationRow n q‖ ≤ Real.sqrt (q + 1 : ℕ) := by
  rw [tensorCreationRow, ContinuousLinearMap.adjoint.norm_map]
  exact tensorAnnihilationRow_opNorm_le

/-- Dimension-free, physically normalized creation-row estimate. -/
theorem tensorCreationRow_norm_sq_le
    (w : EuclideanSpace ℝ (TensorOneFormIndex n q)) :
    ‖tensorCreationRow n q w‖ ^ 2 ≤ (q + 1 : ℕ) * ‖w‖ ^ 2 := by
  have h := (tensorCreationRow n q).le_opNorm w
  have hb := tensorCreationRow_opNorm_le (n := n) (q := q)
  have h1 : ‖tensorCreationRow n q w‖ ≤ Real.sqrt (q + 1 : ℕ) * ‖w‖ :=
    h.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have hs : (Real.sqrt (q + 1 : ℕ)) ^ 2 = (q + 1 : ℕ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  nlinarith [norm_nonneg (tensorCreationRow n q w), Real.sqrt_nonneg (q + 1 : ℕ),
    norm_nonneg w]

/-- The estimate used for c*: apply the actual creation row to the literal
array of spatial derivatives. Other exterior/finite indices sum without
changing its constant. -/
theorem tensorCreationRow_family_norm_sq_le {τ : Type*} [Fintype τ]
    (w : τ → EuclideanSpace ℝ (TensorOneFormIndex n q)) :
    (∑ a, ‖tensorCreationRow n q (w a)‖ ^ 2) ≤
      (q + 1 : ℕ) * ∑ a, ‖w a‖ ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => tensorCreationRow_norm_sq_le (w a)

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorCreationRow_coe
#print axioms KLS.DeterministicBridgeIntegration.tensorCreationRow_norm_sq_le
#print axioms KLS.DeterministicBridgeIntegration.tensorCreationRow_family_norm_sq_le
