import TensorProjectionMatrixAlgebra

/-! Exact finite normalized exterior-adjoint pairing algebra. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n q : ℕ}

lemma tensorExterior_adjoint_pair_sum
    (t : TensorTwoFormIndex n q → Fin n → ℝ)
    (ht : ∀ I i j k, t (I,j,i) k = -t (I,i,j) k)
    (a : TensorOneFormIndex n q) :
    (∑ I, ∑ i, ∑ j, (1 / Real.sqrt 2) *
      (tensorOneFormProjectionMatrix (I,j) a * t (I,i,j) i -
       tensorOneFormProjectionMatrix (I,i) a * t (I,i,j) j)) =
      Real.sqrt 2 * ∑ I, ∑ i, ∑ j,
        tensorOneFormProjectionMatrix a (I,j) * t (I,i,j) i := by
  have he (I : OrderedTensorIndex n q) :
      (∑ i, ∑ j, tensorOneFormProjectionMatrix (I,i) a * t (I,i,j) j) =
      -(∑ i, ∑ j, tensorOneFormProjectionMatrix (I,j) a * t (I,i,j) i) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [ht I i j i]
    ring
  have heall : (∑ I, ∑ i, ∑ j, tensorOneFormProjectionMatrix (I,i) a * t (I,i,j) j) =
      -(∑ I, ∑ i, ∑ j, tensorOneFormProjectionMatrix (I,j) a * t (I,i,j) i) := by
    simp only [he, Finset.sum_neg_distrib]
  have hfactor : (∑ I, ∑ i, ∑ j, (1 / Real.sqrt 2) *
      (tensorOneFormProjectionMatrix (I,j) a * t (I,i,j) i -
       tensorOneFormProjectionMatrix (I,i) a * t (I,i,j) j)) =
      (1 / Real.sqrt 2) * ((∑ I, ∑ i, ∑ j, tensorOneFormProjectionMatrix (I,j) a * t (I,i,j) i) -
      (∑ I, ∑ i, ∑ j, tensorOneFormProjectionMatrix (I,i) a * t (I,i,j) j)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  have hroot : 2 * (1 / Real.sqrt 2) = Real.sqrt 2 := by
    have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    apply (mul_right_cancel₀ (ne_of_gt hp))
    field_simp
    nlinarith
  rw [hfactor, heall, sub_neg_eq_add]
  simp_rw [tensorOneFormProjectionMatrix_symm _ a]
  rw [← two_mul]
  have hm := congrArg (fun z : ℝ => z *
    (∑ I, ∑ i, ∑ j, tensorOneFormProjectionMatrix a (I,j) * t (I,i,j) i)) hroot
  nlinarith

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorExterior_adjoint_pair_sum
