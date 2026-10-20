import TensorExteriorAdjointCompactPairing
import TensorProjectionMatrixAlgebra

/-! Actual projected compact tests for identifying the weighted Hilbert
adjoint of the constrained exterior differential. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology LinearPMap
namespace KLS.DeterministicBridgeIntegration
variable {n q : ℕ} {φ ψ : Space n → ℝ}

lemma tensorOneFormL2_projection_rows (v : TensorOneFormL2 φ q) (a : TensorOneFormIndex n q) :
    (∑ b, tensorOneFormProjectionMatrix a b • v.val b) = v.val a := by
  classical
  have he := (mem_weightedMatrixConstraintSpace_iff (tensorOneFormConstraintMatrix n q) v.val).mp v.property a
  simp only [tensorOneFormConstraintMatrix, sub_smul, ite_smul, one_smul, zero_smul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at he
  exact (sub_eq_zero.mp he).symm

def tensorProjectedCompactTest (a : TensorOneFormIndex n q) (ψ φ : Space n → ℝ)
    (b : TensorOneFormIndex n q) (x : Space n) : ℝ :=
  tensorOneFormProjectionMatrix b a * (ψ x * Real.exp (φ x))

lemma tensorProjectedCompactTest_contDiff (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (a b : TensorOneFormIndex n q) :
    ContDiff ℝ (⊤ : ℕ∞) (tensorProjectedCompactTest a ψ φ b) :=
  contDiff_const.mul (hψ.mul hφ.exp)

lemma tensorProjectedCompactTest_compact (hc : HasCompactSupport ψ) (a b : TensorOneFormIndex n q) :
    HasCompactSupport (tensorProjectedCompactTest a ψ φ b) := hc.mul_right.mul_left

lemma tensorProjectedCompactTest_fiber (a : TensorOneFormIndex n q) (x : Space n) :
    WithLp.toLp 2 (fun b => tensorProjectedCompactTest a ψ φ b x) ∈ tensorOneFormSymmetricFiber n q := by
  have hm := (tensorOneFormSymmetricFiber n q).smul_mem (ψ x * Real.exp (φ x))
    (tensorOneFormProjectionMatrix_column_mem a)
  convert hm using 1
  apply PiLp.ext
  intro b
  simp only [tensorProjectedCompactTest, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma tensorProjectedCompactTest_inner (hφ : Continuous φ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (a : TensorOneFormIndex n q) (v : TensorOneFormL2 φ q) :
    inner ℝ v.val (finiteMatrixLp (tensorProjectedCompactTest a ψ φ)
      (fun b => memLp_of_continuous_hasCompactSupport hφ
        ((hψ.mul (Real.continuous_exp.comp hφ)).const_mul _) (tensorProjectedCompactTest_compact hc a b))) =
      ∫ x, v.val a x * ψ x := by
  let t := weightedCompactTestLp hφ hψ hc
  have he (b : TensorOneFormIndex n q) :
      finiteMatrixLp (tensorProjectedCompactTest a ψ φ)
        (fun b => memLp_of_continuous_hasCompactSupport hφ
          ((hψ.mul (Real.continuous_exp.comp hφ)).const_mul _) (tensorProjectedCompactTest_compact hc a b)) b =
      tensorOneFormProjectionMatrix b a • t := by
    apply Lp.ext
    filter_upwards [(memLp_of_continuous_hasCompactSupport hφ
      ((hψ.mul (Real.continuous_exp.comp hφ)).const_mul (tensorOneFormProjectionMatrix b a))
        (tensorProjectedCompactTest_compact hc a b)).coeFn_toLp,
      Lp.coeFn_smul (tensorOneFormProjectionMatrix b a) t,
      (memLp_of_continuous_hasCompactSupport hφ
        (hψ.mul (Real.continuous_exp.comp hφ)) hc.mul_right).coeFn_toLp] with x hx hy hz
    exact hx.trans (hy.trans (congrArg (fun z : ℝ => tensorOneFormProjectionMatrix b a * z) hz)).symm
  simp only [PiLp.inner_apply, he, real_inner_smul_right]
  simp_rw [tensorOneFormProjectionMatrix_symm _ a]
  calc
    _ = inner ℝ (∑ b, tensorOneFormProjectionMatrix a b • v.val b) t := by
      rw [sum_inner]
      simp only [real_inner_smul_left]
    _ = inner ℝ (v.val a) t := by rw [tensorOneFormL2_projection_rows]
    _ = _ := by rw [real_inner_comm]; exact weightedCompactTestLp_inner hφ hψ hc _

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorProjectedCompactTest_inner
