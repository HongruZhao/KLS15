import TensorHodgeFiniteFiber

/-! Exact coordinate meanings of the constrained fibers and their actual
first-order matrices. These calculations fix the physical normalizations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n q : ℕ} {φ : Space n → ℝ}

lemma tensorTwoFormConstraintMatrix_symmetry (I J : OrderedTensorIndex n q)
    (i j : Fin n) (v : TensorTwoFormIndex n q → ℝ) :
    (∑ z, tensorTwoFormConstraintMatrix n q (Sum.inl (I, J, i, j)) z * v z) =
      if List.Perm (List.ofFn I) (List.ofFn J) then v (I, i, j) - v (J, i, j) else 0 := by
  by_cases h : List.Perm (List.ofFn I) (List.ofFn J)
  · simp [tensorTwoFormConstraintMatrix, h, sub_mul, Finset.sum_sub_distrib]
  · simp [tensorTwoFormConstraintMatrix, h]

lemma tensorTwoFormConstraintMatrix_skew (I : OrderedTensorIndex n q)
    (i j : Fin n) (v : TensorTwoFormIndex n q → ℝ) :
    (∑ z, tensorTwoFormConstraintMatrix n q (Sum.inr (Sum.inl (I, i, j))) z * v z) =
      v (I, i, j) + v (I, j, i) := by
  simp [tensorTwoFormConstraintMatrix, add_mul, Finset.sum_add_distrib]

lemma tensorTwoFormConstraintMatrix_koszul (I : OrderedTensorIndex n q)
    (i j k : Fin n) (v : TensorTwoFormIndex n q → ℝ) :
    (∑ z, tensorTwoFormConstraintMatrix n q (Sum.inr (Sum.inr (I, i, j, k))) z * v z) =
      Real.sqrt q * (v (tensorAuxReplaceFirst I i, j, k) -
        v (tensorAuxReplaceFirst I j, i, k) + v (tensorAuxReplaceFirst I k, i, j)) := by
  simp [tensorTwoFormConstraintMatrix, mul_add, mul_sub, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

def TensorTwoFormCompatible (v : TensorTwoFormIndex n q → ℝ) : Prop :=
  (∀ I J, List.Perm (List.ofFn I) (List.ofFn J) → ∀ i j, v (I, i, j) = v (J, i, j)) ∧
    (∀ I i j, v (I, i, j) = -v (I, j, i)) ∧
      (∀ I i j k, Real.sqrt q * (v (tensorAuxReplaceFirst I i, j, k) -
        v (tensorAuxReplaceFirst I j, i, k) + v (tensorAuxReplaceFirst I k, i, j)) = 0)

theorem mem_tensorTwoFormFiber_iff_compatible
    (v : EuclideanSpace ℝ (TensorTwoFormIndex n q)) :
    v ∈ tensorTwoFormFiber n q ↔ TensorTwoFormCompatible (fun z => v z) := by
  rw [mem_tensorTwoFormFiber_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro I J hp i j
      have he := h (Sum.inl (I, J, i, j))
      rw [tensorTwoFormConstraintMatrix_symmetry, if_pos hp] at he
      exact sub_eq_zero.mp he
    · intro I i j
      have he := h (Sum.inr (Sum.inl (I, i, j)))
      rw [tensorTwoFormConstraintMatrix_skew] at he
      exact eq_neg_of_add_eq_zero_left he
    · intro I i j k
      simpa only [tensorTwoFormConstraintMatrix_koszul] using h (Sum.inr (Sum.inr (I, i, j, k)))
  · rintro ⟨hs, ha, hb⟩ a
    rcases a with ⟨I, J, i, j⟩ | a
    · rw [tensorTwoFormConstraintMatrix_symmetry]
      split_ifs with hp
      · exact sub_eq_zero.mpr (hs I J hp i j)
      · rfl
    · rcases a with ⟨I, i, j⟩ | ⟨I, i, j, k⟩
      · rw [tensorTwoFormConstraintMatrix_skew]
        have he : v (I, i, j) = -v (I, j, i) := ha I i j
        rw [he, neg_add_cancel]
      · exact (tensorTwoFormConstraintMatrix_koszul I i j k _).trans (hb I i j k)

/-- The actual exterior differential on normalized two-form coefficients. -/
theorem tensorHodge_firstOrder_curl (f : TensorTwoFormIndex n q → Space n → ℝ)
    (I : OrderedTensorIndex n q) (i j k : Fin n) (x : Space n) :
    matrixFirstOrder (tensorHodgeDerivativeMatrix n q) (tensorHodgeDriftMatrix φ q) f
      (Sum.inl (I, i, j, k)) x =
        (1 / Real.sqrt 3) * (coordinateDerivative (f (I, j, k)) i x -
          coordinateDerivative (f (I, i, k)) j x + coordinateDerivative (f (I, i, j)) k x) := by
  simp [matrixFirstOrder, matrixDifferential, matrixZeroth, tensorHodgeDerivativeMatrix,
    tensorHodgeDriftMatrix, mul_add, mul_sub, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_irrel, and_comm]
  simp [ite_and]

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.mem_tensorTwoFormFiber_iff_compatible
#print axioms KLS.DeterministicBridgeIntegration.tensorHodge_firstOrder_curl
