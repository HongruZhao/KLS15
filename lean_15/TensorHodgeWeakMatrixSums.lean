import TensorHodgeProjectedAdjoint

/-! Literal finite matrix sums for the projected-adjoint weak Hodge block.
No skew symmetry, differential equation, or domain premise is required. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n q : ℕ} {φ : Space n → ℝ}

lemma tensorHodgeDerivativeMatrix_inr_sum
    (a : TensorOneFormIndex n q) (t : TensorTwoFormIndex n q → Fin n → ℝ) :
    (∑ i, ∑ z, tensorHodgeDerivativeMatrix n q (Sum.inr a) i z * t z i) =
      -Real.sqrt 2 * ∑ I : OrderedTensorIndex n q, ∑ i : Fin n, ∑ j : Fin n,
        tensorOneFormProjectionMatrix a (I,j) * t (I,i,j) i := by
  classical
  rw [Finset.sum_comm]
  simp only [tensorHodgeDerivativeMatrix, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp [Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

lemma tensorHodgeDriftMatrix_inr_sum
    (a : TensorOneFormIndex n q) (x : Space n) (f : TensorTwoFormIndex n q → ℝ) :
    (∑ z, tensorHodgeDriftMatrix φ q (Sum.inr a) z x * f z) =
      Real.sqrt 2 * ∑ I : OrderedTensorIndex n q, ∑ i : Fin n, ∑ j : Fin n,
        tensorOneFormProjectionMatrix a (I,j) * coordinateDerivative φ i x * f (I,i,j) := by
  simp only [tensorHodgeDriftMatrix, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

end KLS.DeterministicBridgeIntegration
end
#print axioms KLS.DeterministicBridgeIntegration.tensorHodgeDerivativeMatrix_inr_sum
#print axioms KLS.DeterministicBridgeIntegration.tensorHodgeDriftMatrix_inr_sum
