import TensorHodgeCoordinates

/-! Literal identification of the projected-adjoint block of the concrete
constrained Hodge matrices. The projection is the actual finite Euclidean
orthogonal projection onto the fully symmetric one-form fiber. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n q : ℕ} {φ : Space n → ℝ}

lemma tensorHodge_matrix_principal_adjoint (f : TensorTwoFormIndex n q → Space n → ℝ)
    (a : TensorOneFormIndex n q) (x : Space n) :
    matrixDifferential (tensorHodgeDerivativeMatrix n q) f (Sum.inr a) x =
      ∑ z : TensorTwoFormIndex n q,
        (-(Real.sqrt 2) * tensorOneFormProjectionMatrix a (z.1, z.2.2)) *
          coordinateDerivative (f z) z.2.1 x := by
  unfold matrixDifferential
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp only [tensorHodgeDerivativeMatrix, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp

def tensorTwoFormWeightedAdjoint (φ : Space n → ℝ)
    (f : TensorTwoFormIndex n q → Space n → ℝ) (x : Space n) :
    EuclideanSpace ℝ (TensorOneFormIndex n q) :=
  WithLp.toLp 2 (fun a => Real.sqrt 2 * ∑ i : Fin n,
    (-coordinateDerivative (f (a.1, i, a.2)) i x +
      coordinateDerivative φ i x * f (a.1, i, a.2) x))

/-- Exact d₁* coordinate formula with the physical √2 contraction, followed
by the genuine P₁ orthogonal projection. This is a classical expression;
the identification of its maximal weak domain with a Hilbert adjoint graph
is not asserted by this theorem. -/
theorem tensorHodge_firstOrder_projectedAdjoint
    (f : TensorTwoFormIndex n q → Space n → ℝ)
    (a : TensorOneFormIndex n q) (x : Space n) :
    matrixFirstOrder (tensorHodgeDerivativeMatrix n q) (tensorHodgeDriftMatrix φ q) f
      (Sum.inr a) x =
        tensorOneFormProjection n q (tensorTwoFormWeightedAdjoint φ f x) a := by
  rw [matrixFirstOrder, tensorHodge_matrix_principal_adjoint, tensorOneFormProjection_matrix_apply]
  simp only [matrixZeroth, tensorHodgeDriftMatrix]
  rw [← Finset.sum_add_distrib]
  simp only [tensorTwoFormWeightedAdjoint, PiLp.toLp_apply]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorHodge_matrix_principal_adjoint
#print axioms KLS.DeterministicBridgeIntegration.tensorHodge_firstOrder_projectedAdjoint
