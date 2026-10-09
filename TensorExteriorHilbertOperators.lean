import WeightedMatrixConstraintSpace
import TensorExteriorDifferential

/-! Genuine weighted L² constrained exterior operators. The domains are
literal full ordinary distributional matrix domains, and the operators are
closed LinearPMaps, ready for Hilbert-complex variational calculus. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology LinearPMap
namespace KLS.DeterministicBridgeIntegration
variable {n q : ℕ} {φ : Space n → ℝ}

def tensorOneFormConstraintMatrix (n q : ℕ) : TensorOneFormIndex n q → TensorOneFormIndex n q → ℝ :=
  fun a b => (if a = b then 1 else 0) - tensorOneFormProjectionMatrix a b

lemma tensorOneFormConstraintMatrix_apply (v : EuclideanSpace ℝ (TensorOneFormIndex n q))
    (a : TensorOneFormIndex n q) :
    (∑ b, tensorOneFormConstraintMatrix n q a b * v b) = v a - tensorOneFormProjection n q v a := by
  classical
  simp only [tensorOneFormConstraintMatrix, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    tensorOneFormProjection_matrix_apply]

def tensorOneFormL2Subspace (φ : Space n → ℝ) (q : ℕ) :
    Submodule ℝ (CenteredL2.Family (potentialMeasure φ) (TensorOneFormIndex n q)) :=
  weightedMatrixConstraintSpace φ (tensorOneFormConstraintMatrix n q)

def tensorTwoFormL2Subspace (φ : Space n → ℝ) (q : ℕ) :
    Submodule ℝ (CenteredL2.Family (potentialMeasure φ) (TensorTwoFormIndex n q)) :=
  weightedMatrixConstraintSpace φ (tensorTwoFormConstraintMatrix n q)

abbrev TensorOneFormL2 (φ : Space n → ℝ) (q : ℕ) := ↥(tensorOneFormL2Subspace φ q)
abbrev TensorTwoFormL2 (φ : Space n → ℝ) (q : ℕ) := ↥(tensorTwoFormL2Subspace φ q)
abbrev TensorThreeFormL2 (φ : Space n → ℝ) (q : ℕ) :=
  ↥(⊤ : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) (TensorThreeFormIndex n q)))

instance tensorOneFormL2_complete : CompleteSpace (TensorOneFormL2 φ q) :=
  weightedMatrixConstraintSpace_complete _
instance tensorTwoFormL2_complete : CompleteSpace (TensorTwoFormL2 φ q) :=
  weightedMatrixConstraintSpace_complete _

lemma tensorOneFormL2Subspace_isClosed :
    IsClosed (tensorOneFormL2Subspace φ q :
      Set (CenteredL2.Family (potentialMeasure φ) (TensorOneFormIndex n q))) :=
  weightedMatrixConstraintSpace_isClosed _
lemma tensorTwoFormL2Subspace_isClosed :
    IsClosed (tensorTwoFormL2Subspace φ q :
      Set (CenteredL2.Family (potentialMeasure φ) (TensorTwoFormIndex n q))) :=
  weightedMatrixConstraintSpace_isClosed _

lemma finiteMatrixLp_mem_oneForm_iff {f : TensorOneFormIndex n q → Space n → ℝ}
    (hf : ∀ a, MemLp (f a) 2 (potentialMeasure φ)) :
    finiteMatrixLp f hf ∈ tensorOneFormL2Subspace φ q ↔
      ∀ᵐ x ∂potentialMeasure φ,
        WithLp.toLp 2 (fun a => f a x) ∈ tensorOneFormSymmetricFiber n q := by
  rw [tensorOneFormL2Subspace, finiteMatrixLp_mem_constraint_iff]
  simp only [Filter.EventuallyEq, Pi.zero_apply]
  rw [← Filter.eventually_all]
  apply Filter.eventually_congr
  exact Eventually.of_forall fun x => by
    have hrow (a : TensorOneFormIndex n q) :
        (∑ b, tensorOneFormConstraintMatrix n q a b * f b x) =
          f a x - tensorOneFormProjection n q (WithLp.toLp 2 (fun b => f b x)) a :=
      tensorOneFormConstraintMatrix_apply (WithLp.toLp 2 (fun b => f b x)) a
    simp only [hrow]
    constructor
    · intro h
      exact Submodule.starProjection_eq_self_iff.mp (PiLp.ext fun a => (sub_eq_zero.mp (h a)).symm)
    · intro h a
      exact sub_eq_zero.mpr (congrArg (fun v : EuclideanSpace ℝ (TensorOneFormIndex n q) => v a)
        (Submodule.starProjection_eq_self_iff.mpr h)).symm

lemma finiteMatrixLp_mem_twoForm_iff {f : TensorTwoFormIndex n q → Space n → ℝ}
    (hf : ∀ z, MemLp (f z) 2 (potentialMeasure φ)) :
    finiteMatrixLp f hf ∈ tensorTwoFormL2Subspace φ q ↔
      ∀ᵐ x ∂potentialMeasure φ, TensorTwoFormCompatible (fun z => f z x) := by
  rw [tensorTwoFormL2Subspace, finiteMatrixLp_mem_constraint_iff]
  simp only [Filter.EventuallyEq, Pi.zero_apply]
  rw [← Filter.eventually_all]
  apply Filter.eventually_congr
  exact Eventually.of_forall fun x => by
    exact (mem_tensorTwoFormFiber_iff (WithLp.toLp 2 (fun z => f z x))).symm.trans
      (mem_tensorTwoFormFiber_iff_compatible _)

def tensorExteriorTwoDerivativeMatrix (n q : ℕ) :
    TensorThreeFormIndex n q → Fin n → TensorTwoFormIndex n q → ℝ :=
  fun a i z => tensorHodgeDerivativeMatrix n q (Sum.inl a) i z

/-- Actual maximal d₁ between the literal constrained weighted Hilbert spaces. -/
def tensorExteriorOneOperator (hφ : ContDiff ℝ 1 φ) (q : ℕ) :
    TensorOneFormL2 φ q →ₗ.[ℝ] TensorTwoFormL2 φ q :=
  weightedMatrixFiberOperator hφ (tensorExteriorOneDerivativeMatrix n q)
    (tensorOneFormL2Subspace φ q) (tensorTwoFormL2Subspace φ q)

/-- Actual maximal d₂ from the literal constrained two-form weighted space. -/
def tensorExteriorTwoOperator (hφ : ContDiff ℝ 1 φ) (q : ℕ) :
    TensorTwoFormL2 φ q →ₗ.[ℝ] TensorThreeFormL2 φ q :=
  weightedMatrixFiberOperator hφ (tensorExteriorTwoDerivativeMatrix n q)
    (tensorTwoFormL2Subspace φ q) ⊤

theorem tensorExteriorOneOperator_isClosed (hφ : ContDiff ℝ 1 φ) (q : ℕ) :
    (tensorExteriorOneOperator hφ q).IsClosed := weightedMatrixFiberOperator_isClosed _ _ _ _
theorem tensorExteriorTwoOperator_isClosed (hφ : ContDiff ℝ 1 φ) (q : ℕ) :
    (tensorExteriorTwoOperator hφ q).IsClosed := weightedMatrixFiberOperator_isClosed _ _ _ _

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorExteriorOneOperator_isClosed
#print axioms KLS.DeterministicBridgeIntegration.tensorExteriorTwoOperator_isClosed
