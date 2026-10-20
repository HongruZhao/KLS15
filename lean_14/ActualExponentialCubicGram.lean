import ActualCubicHigherDefect

/-! Exact benchmark specialization. The coordinate third-cumulant premise is
stated explicitly: this file does not assume or certify a construction of an
independent exponential product measure. The general replacement needs no such
premise. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25.CubicSymmetricNoise
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def centeredExponentialThirdCumulants (μ : Measure (Space n)) : Prop :=
  ∀ i j k : Fin n, thirdCumulantMatrix μ (MomentMap.coordinateVector i) j k =
    if i = j ∧ j = k then 2 else 0

def actualAppellDiagonalEnergyTwo (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  ∑ i : Fin n, (actualAppellCoefficient μ f 2 ![i,i])^2

theorem actualCubicSlotArray_of_exponential_third
    (hκ : centeredExponentialThirdCumulants μ) (f : Space n → ℝ) (i j k : Fin n) :
    actualCubicSlotArray μ f i j k =
      if i = j then 2*actualAppellCoefficient μ f 2 ![i,k] else 0 := by
  classical
  change ∀ i j k : Fin n,
    thirdCumulantMatrix μ (MomentMap.coordinateVector i) j k =
      if i = j ∧ j = k then 2 else 0 at hκ
  unfold actualCubicSlotArray
  by_cases hij : i = j
  · subst j
    simp [hκ]
  · simp [hκ, hij]

theorem actualCubicSlotArray_square_of_exponential_third
    (hκ : centeredExponentialThirdCumulants μ) (f : Space n → ℝ) :
    square (actualCubicSlotArray μ f) = 4*actualAppellEnergy μ f 2 := by
  classical
  unfold square tripleSum
  simp_rw [actualCubicSlotArray_of_exponential_third hκ]
  simp only [ite_pow, zero_pow (by decide : (2 : ℕ) ≠ 0),
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [actualAppellEnergy, sum_fin_two_coordinates, mul_pow]
  norm_num only [show (2 : ℝ)^2 = 4 by norm_num]
  simp only [Finset.mul_sum]

theorem actualCubicSlotArray_cross_of_exponential_third
    (hκ : centeredExponentialThirdCumulants μ) (f : Space n → ℝ) :
    cross (actualCubicSlotArray μ f) = 4*actualAppellDiagonalEnergyTwo μ f := by
  classical
  unfold cross tripleSum
  simp_rw [actualCubicSlotArray_of_exponential_third hκ]
  have hmul (i j k : Fin n) :
      (if i = j then 2*actualAppellCoefficient μ f 2 ![i,k] else 0)*
        (if i = k then 2*actualAppellCoefficient μ f 2 ![i,j] else 0) =
      if i = j then (if i = k then 4*(actualAppellCoefficient μ f 2 ![i,i])^2 else 0)
        else 0 := by
    by_cases hij : i = j <;> by_cases hik : i = k
    · subst j; subst k; simp; ring
    · subst j; simp [hik]
    · subst k; simp [hij]
    · simp [hij, hik]
  simp_rw [hmul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp only [actualAppellDiagonalEnergyTwo, Finset.mul_sum]

theorem actualAppellDiagonalEnergyTwo_le (f : Space n → ℝ) :
    actualAppellDiagonalEnergyTwo μ f ≤ actualAppellEnergy μ f 2 := by
  classical
  unfold actualAppellDiagonalEnergyTwo actualAppellEnergy
  rw [sum_fin_two_coordinates]
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum
    (fun (j : Fin n) _ => sq_nonneg (actualAppellCoefficient μ f 2 ![i,j]))
    (Finset.mem_univ i)

theorem actualCubicRemainderGram_of_exponential_third
    (hκ : centeredExponentialThirdCumulants μ) (f : Space n → ℝ) :
    actualCubicRemainderGram μ f =
      12*actualAppellEnergy μ f 2+24*actualAppellDiagonalEnergyTwo μ f := by
  unfold actualCubicRemainderGram
  rw [actualCubicSlotArray_square_of_exponential_third hκ,
    actualCubicSlotArray_cross_of_exponential_third hκ]
  ring

theorem actualCubicRemainderGram_le_thirtysix_of_exponential_third
    (hκ : centeredExponentialThirdCumulants μ) (f : Space n → ℝ) :
    actualCubicRemainderGram μ f ≤ 36*actualAppellEnergy μ f 2 := by
  rw [actualCubicRemainderGram_of_exponential_third hκ]
  linarith [actualAppellDiagonalEnergyTwo_le (μ := μ) f]

theorem actualAppellDiagonalEnergyTwo_eq_of_diagonal (f : Space n → ℝ)
    (hdiag : ∀ i j : Fin n, i ≠ j → actualAppellCoefficient μ f 2 ![i,j] = 0) :
    actualAppellDiagonalEnergyTwo μ f = actualAppellEnergy μ f 2 := by
  classical
  unfold actualAppellDiagonalEnergyTwo actualAppellEnergy
  rw [sum_fin_two_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  symm
  apply Finset.sum_eq_single i
  · intro j _ hji
    rw [hdiag i j (Ne.symm hji)]
    norm_num
  · simp

theorem actualCubicRemainderGram_eq_thirtysix_of_exponential_diagonal
    (hκ : centeredExponentialThirdCumulants μ) (f : Space n → ℝ)
    (hdiag : ∀ i j : Fin n, i ≠ j → actualAppellCoefficient μ f 2 ![i,j] = 0) :
    actualCubicRemainderGram μ f = 36*actualAppellEnergy μ f 2 := by
  rw [actualCubicRemainderGram_of_exponential_third hκ,
    actualAppellDiagonalEnergyTwo_eq_of_diagonal f hdiag]
  ring

theorem actualCubicRemainderGram_sharp_diagonal_ratio
    (hκ : centeredExponentialThirdCumulants μ) (f : Space n → ℝ)
    (hdiag : ∀ i j : Fin n, i ≠ j → actualAppellCoefficient μ f 2 ![i,j] = 0)
    (hne : actualAppellEnergy μ f 2 ≠ 0) :
    actualCubicRemainderGram μ f/actualAppellEnergy μ f 2 = 36 := by
  rw [actualCubicRemainderGram_eq_thirtysix_of_exponential_diagonal hκ f hdiag]
  field_simp

theorem actualAppellProperRemainder_three_norm_le_of_exponential_third
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hκ : centeredExponentialThirdCumulants μ) :
    ‖(WithLp.toLp 2 (actualAppellProperRemainder μ f 3) :
      EuclideanSpace ℝ (Fin 3 → Fin n))‖ ≤ 6*Real.sqrt (actualAppellEnergy μ f 2) := by
  rw [actualAppellProperRemainder_three_norm_eq_gram hμ hf]
  have hg := actualCubicRemainderGram_le_thirtysix_of_exponential_third hκ f
  have hgs := Real.sq_sqrt (actualCubicRemainderGram_nonneg hμ hf)
  have hys := Real.sq_sqrt (actualAppellEnergy_nonneg μ f 2)
  have hgn := Real.sqrt_nonneg (actualCubicRemainderGram μ f)
  have hyn := Real.sqrt_nonneg (actualAppellEnergy μ f 2)
  nlinarith

theorem actualAppellProperRemainder_three_norm_eq_of_exponential_diagonal
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hκ : centeredExponentialThirdCumulants μ)
    (hdiag : ∀ i j : Fin n, i ≠ j → actualAppellCoefficient μ f 2 ![i,j] = 0) :
    ‖(WithLp.toLp 2 (actualAppellProperRemainder μ f 3) :
      EuclideanSpace ℝ (Fin 3 → Fin n))‖ = 6*Real.sqrt (actualAppellEnergy μ f 2) := by
  rw [actualAppellProperRemainder_three_norm_eq_gram hμ hf,
    actualCubicRemainderGram_eq_thirtysix_of_exponential_diagonal hκ f hdiag]
  have hys := Real.sq_sqrt (actualAppellEnergy_nonneg μ f 2)
  have hgs := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 36)
    (actualAppellEnergy_nonneg μ f 2))
  have hgn := Real.sqrt_nonneg (36*actualAppellEnergy μ f 2)
  have hyn := Real.sqrt_nonneg (actualAppellEnergy μ f 2)
  nlinarith

end KLS.DeterministicBridgeIntegration

#print axioms KLS.DeterministicBridgeIntegration.actualCubicRemainderGram_of_exponential_third
#print axioms KLS.DeterministicBridgeIntegration.actualCubicRemainderGram_le_thirtysix_of_exponential_third
#print axioms KLS.DeterministicBridgeIntegration.actualCubicRemainderGram_eq_thirtysix_of_exponential_diagonal
#print axioms KLS.DeterministicBridgeIntegration.actualCubicRemainderGram_sharp_diagonal_ratio
#print axioms KLS.DeterministicBridgeIntegration.actualAppellProperRemainder_three_norm_eq_of_exponential_diagonal
