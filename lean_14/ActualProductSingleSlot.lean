import ActualProductCumulants
import KLS.TensorSlotSumBound

/-! The actual centered product exponential has matrix single-slot cap four.
All identities use the concrete mapped product measure; no cumulant premise
or admissibility hypothesis is supplied. The tensor lifting is exact. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLSImprovement.ActualProductSingleSlot
open KLS KLS.TensorEnergy KLS.DeterministicBridgeIntegration
open KLSImprovement.ActualProductCumulants
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def productCumulantMatrix (n : ℕ) (k : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  thirdCumulantMatrix (centeredProductMeasure n) (MomentMap.coordinateVector k)

theorem productCumulantMatrix_apply {n : ℕ} (k i j : Fin n) :
    productCumulantMatrix n k i j = if k=i ∧ i=j then 2 else 0 :=
  centeredProduct_third_cumulants n k i j

theorem productCumulantMatrix_transpose {n : ℕ} (k : Fin n) :
    (productCumulantMatrix n k).transpose=productCumulantMatrix n k :=
  (thirdCumulantMatrix_isSymm _ _).eq

theorem productCumulantMatrix_square {n : ℕ} (k : Fin n) :
    productCumulantMatrix n k*productCumulantMatrix n k =
      2 • productCumulantMatrix n k := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply]
  rw [Finset.sum_eq_single k]
  · by_cases hki : k=i <;> by_cases hkj : k=j <;>
      simp_all [productCumulantMatrix_apply]
  · intro l _ hlk
    have hkl : k ≠ l := Ne.symm hlk
    by_cases hki : k=i <;> simp_all [productCumulantMatrix_apply]
  · simp

/-- Exact actual matrix seed; universal eight is loose by a factor two here. -/
theorem productCumulantMatrix_square_sum (n : ℕ) :
    (∑ k : Fin n, productCumulantMatrix n k*productCumulantMatrix n k) =
      (4 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  simp_rw [productCumulantMatrix_square]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, productCumulantMatrix_apply]
  by_cases hij : i=j
  · subst j
    norm_num
  · simp [hij]

theorem product_single_slot_seed (n : ℕ) :
    ((4 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)-
      ∑ k : Fin n, productCumulantMatrix n k*productCumulantMatrix n k).PosSemidef := by
  rw [productCumulantMatrix_square_sum, sub_self]
  exact Matrix.PosSemidef.zero

/-- Equality for each tensor slot in every rank. -/
theorem product_tensor_single_slot_exact {n r : ℕ} (s : Fin r)
    (T : (Fin r → Fin n) → ℝ) :
    (∑ k : Fin n,
      (tensorSlot s (productCumulantMatrix n k) *ᵥ T) ⬝ᵥ
        (tensorSlot s (productCumulantMatrix n k) *ᵥ T)) = 4*(T ⬝ᵥ T) := by
  classical
  calc
    _ = T ⬝ᵥ ((∑ k : Fin n,
        tensorSlot s (productCumulantMatrix n k*productCumulantMatrix n k)) *ᵥ T) := by
      rw [Matrix.sum_mulVec, dotProduct_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [tensorSlot_mul, dotProduct_matrix_square _
        (by rw [tensorSlot_transpose, productCumulantMatrix_transpose])]
    _ = 4*(T ⬝ᵥ T) := by
      rw [← tensorSlot_sum, productCumulantMatrix_square_sum, tensorSlot_smul,
        tensorSlot_one, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
      rfl

/-- Summing the individual slot energies has exact constant four times rank. -/
theorem product_tensor_all_single_slots_exact {n r : ℕ}
    (T : (Fin r → Fin n) → ℝ) :
    (∑ s : Fin r, ∑ k : Fin n,
      (tensorSlot s (productCumulantMatrix n k) *ᵥ T) ⬝ᵥ
        (tensorSlot s (productCumulantMatrix n k) *ᵥ T)) =
      4*(r : ℝ)*(T ⬝ᵥ T) := by
  simp_rw [product_tensor_single_slot_exact]
  simp
  ring

/-- The original generic matrix-order lift already permits law-dependent
caps. Applying cap four gives the corresponding all-slot-sum upper bound. -/
theorem product_tensor_slot_sum_bound {n r : ℕ} (T : (Fin r → Fin n) → ℝ) :
    (∑ k : Fin n,
      (tensorSlotSum (productCumulantMatrix n k) *ᵥ T) ⬝ᵥ
        (tensorSlotSum (productCumulantMatrix n k) *ᵥ T)) ≤
      4*(r : ℝ)^2*(T ⬝ᵥ T) :=
  tensorSlotSum_noise_sum_le (productCumulantMatrix n)
    productCumulantMatrix_transpose 4 (product_single_slot_seed n) T

end KLSImprovement.ActualProductSingleSlot

#print axioms KLSImprovement.ActualProductSingleSlot.productCumulantMatrix_square_sum
#print axioms KLSImprovement.ActualProductSingleSlot.product_single_slot_seed
#print axioms KLSImprovement.ActualProductSingleSlot.product_tensor_single_slot_exact
#print axioms KLSImprovement.ActualProductSingleSlot.product_tensor_all_single_slots_exact
#print axioms KLSImprovement.ActualProductSingleSlot.product_tensor_slot_sum_bound
