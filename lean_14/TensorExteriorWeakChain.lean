import TensorExteriorHilbertOperators

/-! The exterior differential squares to zero on the full ordinary
weak distributional domain, with actual physical normalization factors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology LinearPMap
namespace KLS.DeterministicBridgeIntegration
variable {n q : ℕ}

lemma tensorExteriorOne_matrix_sum (h : TensorOneFormIndex n q → Fin n → ℝ)
    (I : OrderedTensorIndex n q) (i j : Fin n) :
    (∑ k, ∑ a, tensorExteriorOneDerivativeMatrix n q (I, i, j) k a * h a k) =
      (1 / Real.sqrt 2) * (h (I, j) i - h (I, i) j) := by
  classical
  simp [tensorExteriorOneDerivativeMatrix, mul_sub, sub_mul,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Fintype.sum_prod_type, and_comm]
  simp [ite_and]

lemma tensorExteriorTwo_matrix_sum (h : TensorTwoFormIndex n q → Fin n → ℝ)
    (I : OrderedTensorIndex n q) (i j k : Fin n) :
    (∑ l, ∑ z, tensorExteriorTwoDerivativeMatrix n q (I, i, j, k) l z * h z l) =
      (1 / Real.sqrt 3) * (h (I, j, k) i - h (I, i, k) j + h (I, i, j) k) := by
  classical
  simp [tensorExteriorTwoDerivativeMatrix, tensorHodgeDerivativeMatrix,
    mul_add, mul_sub, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, and_comm]
  simp [ite_and]

lemma hasWeakMatrixDerivative_exteriorOne_iff
    {f : TensorOneFormIndex n q → Space n → ℝ} {g : TensorTwoFormIndex n q → Space n → ℝ} :
    HasWeakMatrixDerivative (tensorExteriorOneDerivativeMatrix n q) f g ↔
      ∀ (ψ : Space n → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        ∀ I i j, (∫ x, g (I, i, j) x * ψ x) =
          -(1 / Real.sqrt 2) * ((∫ x, f (I, j) x * coordinateDerivative ψ i x) -
            ∫ x, f (I, i) x * coordinateDerivative ψ j x) := by
  constructor
  · intro h ψ hψ hc I i j
    have he := h ψ hψ hc (I, i, j)
    rw [tensorExteriorOne_matrix_sum] at he
    simpa only [neg_mul] using he
  · intro h ψ hψ hc z
    rcases z with ⟨I, i, j⟩
    rw [tensorExteriorOne_matrix_sum]
    simpa only [neg_mul] using h ψ hψ hc I i j

lemma hasWeakMatrixDerivative_exteriorTwo_iff
    {f : TensorTwoFormIndex n q → Space n → ℝ} {g : TensorThreeFormIndex n q → Space n → ℝ} :
    HasWeakMatrixDerivative (tensorExteriorTwoDerivativeMatrix n q) f g ↔
      ∀ (ψ : Space n → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        ∀ I i j k, (∫ x, g (I, i, j, k) x * ψ x) =
          -(1 / Real.sqrt 3) * ((∫ x, f (I, j, k) x * coordinateDerivative ψ i x) -
            (∫ x, f (I, i, k) x * coordinateDerivative ψ j x) +
            ∫ x, f (I, i, j) x * coordinateDerivative ψ k x) := by
  constructor
  · intro h ψ hψ hc I i j k
    have he := h ψ hψ hc (I, i, j, k)
    rw [tensorExteriorTwo_matrix_sum] at he
    simpa only [neg_mul] using he
  · intro h ψ hψ hc z
    rcases z with ⟨I, i, j, k⟩
    rw [tensorExteriorTwo_matrix_sum]
    simpa only [neg_mul] using h ψ hψ hc I i j k

/-- This is a genuine distributional chain identity: no individual weak
first derivatives of f or g and no compact approximation are assumed. -/
theorem HasWeakMatrixDerivative.exterior_chain
    {f : TensorOneFormIndex n q → Space n → ℝ} {g : TensorTwoFormIndex n q → Space n → ℝ}
    (h : HasWeakMatrixDerivative (tensorExteriorOneDerivativeMatrix n q) f g) :
    HasWeakMatrixDerivative (tensorExteriorTwoDerivativeMatrix n q) g 0 := by
  rw [hasWeakMatrixDerivative_exteriorTwo_iff]
  intro ψ hψ hc I i j k
  have hA := hasWeakMatrixDerivative_exteriorOne_iff.mp h
  have hd (l : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative ψ l) :=
    contDiff_coordinateDerivative hψ (m := (⊤ : ℕ∞)) (by simp) l
  have hm (i j : Fin n) : coordinateDerivative (coordinateDerivative ψ i) j =
      coordinateDerivative (coordinateDerivative ψ j) i := by
    funext x
    change coordinateHessian ψ x j i = coordinateHessian ψ x i j
    exact (coordinateHessian_symmetric (hψ.of_le (by simp)) x).apply i j
  rw [hA (coordinateDerivative ψ i) (hd i) (hasCompactSupport_coordinateDerivative hc i),
    hA (coordinateDerivative ψ j) (hd j) (hasCompactSupport_coordinateDerivative hc j),
    hA (coordinateDerivative ψ k) (hd k) (hasCompactSupport_coordinateDerivative hc k),
    hm i j, hm i k, hm j k]
  simp only [Pi.zero_apply, zero_mul, integral_zero]
  ring

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.HasWeakMatrixDerivative.exterior_chain
