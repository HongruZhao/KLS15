import TensorExteriorHilbertOperators

/-! Matrix algebra for the actual finite one-form orthogonal projection.
These are consequences of the literal Euclidean projection, with no
assumed symmetry or idempotence premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n q : ℕ}

lemma tensorOneFormProjectionMatrix_symm (a b : TensorOneFormIndex n q) :
    tensorOneFormProjectionMatrix a b = tensorOneFormProjectionMatrix b a := by
  have he := (tensorOneFormSymmetricFiber n q).inner_starProjection_left_eq_right
    (EuclideanSpace.single b 1) (EuclideanSpace.single a 1)
  simpa only [tensorOneFormProjection, EuclideanSpace.inner_single_right,
    EuclideanSpace.inner_single_left, conj_trivial, one_mul, mul_one,
    tensorOneFormProjectionMatrix] using he

lemma tensorOneFormProjectionMatrix_column_mem (b : TensorOneFormIndex n q) :
    WithLp.toLp 2 (fun a => tensorOneFormProjectionMatrix a b) ∈ tensorOneFormSymmetricFiber n q := by
  change tensorOneFormProjection n q (EuclideanSpace.single b 1) ∈ tensorOneFormSymmetricFiber n q
  exact (tensorOneFormSymmetricFiber n q).starProjection_apply_mem _

lemma tensorOneFormProjectionMatrix_row_mem (a : TensorOneFormIndex n q) :
    WithLp.toLp 2 (fun b => tensorOneFormProjectionMatrix a b) ∈ tensorOneFormSymmetricFiber n q := by
  have he : (fun b => tensorOneFormProjectionMatrix a b) =
      (fun b => tensorOneFormProjectionMatrix b a) := funext (fun b => tensorOneFormProjectionMatrix_symm a b)
  rw [he]
  exact tensorOneFormProjectionMatrix_column_mem a

lemma tensorOneFormProjectionMatrix_idempotent (a b : TensorOneFormIndex n q) :
    (∑ c, tensorOneFormProjectionMatrix a c * tensorOneFormProjectionMatrix c b) =
      tensorOneFormProjectionMatrix a b := by
  have he : tensorOneFormProjection n q
      (WithLp.toLp 2 (fun c => tensorOneFormProjectionMatrix c b)) =
      WithLp.toLp 2 (fun c => tensorOneFormProjectionMatrix c b) :=
    Submodule.starProjection_eq_self_iff.mpr (tensorOneFormProjectionMatrix_column_mem b)
  have hc := congrArg (fun v : EuclideanSpace ℝ (TensorOneFormIndex n q) => v a) he
  simpa only [tensorOneFormProjection_matrix_apply, PiLp.toLp_apply] using hc

lemma tensorOneFormConstraintMatrix_column_zero (a b : TensorOneFormIndex n q) :
    (∑ c, tensorOneFormConstraintMatrix n q a c * tensorOneFormProjectionMatrix c b) = 0 := by
  change (∑ c, tensorOneFormConstraintMatrix n q a c *
    (WithLp.toLp 2 (fun d => tensorOneFormProjectionMatrix d b)) c) = 0
  rw [tensorOneFormConstraintMatrix_apply]
  have he : tensorOneFormProjection n q
      (WithLp.toLp 2 (fun c => tensorOneFormProjectionMatrix c b)) =
      WithLp.toLp 2 (fun c => tensorOneFormProjectionMatrix c b) :=
    Submodule.starProjection_eq_self_iff.mpr (tensorOneFormProjectionMatrix_column_mem b)
  rw [he]
  exact sub_self _

end KLS.DeterministicBridgeIntegration
end
#print axioms KLS.DeterministicBridgeIntegration.tensorOneFormProjectionMatrix_symm
#print axioms KLS.DeterministicBridgeIntegration.tensorOneFormProjectionMatrix_idempotent
#print axioms KLS.DeterministicBridgeIntegration.tensorOneFormConstraintMatrix_column_zero
