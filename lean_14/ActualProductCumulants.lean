import ExponentialMoments
import ActualExponentialCubicGram

/-!
The concrete product of independent rate-one exponentials, centered coordinate
by coordinate. The third-cumulant diagonal premise used by the retained cubic
Gram is proved here for the actual mapped product measure. This construction
and the Gram specialization require no assumed log-concavity premise.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace KLSImprovement.ActualProductCumulants
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSImprovement.ExponentialMoments
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

def centeredProductMap (n : ℕ) (y : Fin n → ℝ) : Space n :=
  WithLp.toLp 2 (fun i => y i - 1)

theorem measurable_centeredProductMap (n : ℕ) : Measurable (centeredProductMap n) := by
  unfold centeredProductMap
  fun_prop

/-- Actual centered product exponential law in Euclidean dimension `n`. -/
def centeredProductMeasure (n : ℕ) : Measure (Space n) :=
  (Measure.pi (fun _ : Fin n => expMeasure 1)).map (centeredProductMap n)

private def tripleCoordinateFactor {n : ℕ} (i j k l : Fin n) (y : ℝ) : ℝ :=
  (if l = i then y - 1 else 1) *
    (if l = j then y - 1 else 1) *
    (if l = k then y - 1 else 1)

private theorem tripleCoordinateFactor_product {n : ℕ} (i j k : Fin n) (y : Fin n → ℝ) :
    (∏ l, tripleCoordinateFactor i j k l (y l)) = (y i - 1)*(y j - 1)*(y k - 1) := by
  classical
  simp only [tripleCoordinateFactor, Finset.prod_mul_distrib]
  simp

theorem centeredProduct_triple_moment {n : ℕ} (i j k : Fin n) :
    (∫ x : Space n, x i*x j*x k ∂centeredProductMeasure n) =
      if i = j ∧ j = k then 2 else 0 := by
  classical
  unfold centeredProductMeasure
  rw [integral_map (measurable_centeredProductMap n).aemeasurable (by fun_prop)]
  change (∫ y : Fin n → ℝ, (y i - 1)*(y j - 1)*(y k - 1)
    ∂Measure.pi (fun _ : Fin n => expMeasure 1)) = _
  simp_rw [← tripleCoordinateFactor_product i j k]
  rw [integral_fintype_prod_eq_prod]
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      have hf (l : Fin n) :
          (∫ y : ℝ, tripleCoordinateFactor i i i l y ∂expMeasure 1) =
            if l = i then 2 else 1 := by
        by_cases hli : l = i
        · subst l
          simp only [tripleCoordinateFactor, ite_true]
          simpa only [pow_succ, pow_zero, one_mul] using expMeasure_one_integral_centered_cube
        · simp [tripleCoordinateFactor, hli]
      simp_rw [hf]
      simp
    · simp only [hik, and_false, ite_false]
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      have hki : k ≠ i := Ne.symm hik
      simpa [tripleCoordinateFactor, hki] using expMeasure_one_integral_centered
  · simp only [hij, false_and, ite_false]
    by_cases hik : i = k
    · subst k
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      have hji : j ≠ i := Ne.symm hij
      simpa [tripleCoordinateFactor, hji] using expMeasure_one_integral_centered
    · apply Finset.prod_eq_zero (Finset.mem_univ i)
      simpa [tripleCoordinateFactor, hij, hik] using expMeasure_one_integral_centered

/-- The formerly explicit third-cumulant premise is certified for the actual
centered independent exponential product law. -/
theorem centeredProduct_third_cumulants (n : ℕ) :
    centeredExponentialThirdCumulants (centeredProductMeasure n) := by
  intro i j k
  rw [thirdCumulantMatrix_coordinate_eq_cubic, centeredProduct_triple_moment]
  by_cases hij : i = j <;> by_cases hjk : j = k <;> by_cases hik : i = k <;> simp_all
  all_goals aesop

theorem centeredProduct_cubic_gram {n : ℕ} (f : Space n → ℝ) :
    actualCubicRemainderGram (centeredProductMeasure n) f =
      12*actualAppellEnergy (centeredProductMeasure n) f 2+
        24*actualAppellDiagonalEnergyTwo (centeredProductMeasure n) f :=
  actualCubicRemainderGram_of_exponential_third (centeredProduct_third_cumulants n) f

theorem centeredProduct_cubic_gram_le_thirtysix {n : ℕ} (f : Space n → ℝ) :
    actualCubicRemainderGram (centeredProductMeasure n) f ≤
      36*actualAppellEnergy (centeredProductMeasure n) f 2 :=
  actualCubicRemainderGram_le_thirtysix_of_exponential_third
    (centeredProduct_third_cumulants n) f

theorem centeredProduct_cubic_gram_eq_thirtysix_of_diagonal {n : ℕ}
    (f : Space n → ℝ)
    (hdiag : ∀ i j : Fin n, i ≠ j →
      actualAppellCoefficient (centeredProductMeasure n) f 2 ![i,j] = 0) :
    actualCubicRemainderGram (centeredProductMeasure n) f =
      36*actualAppellEnergy (centeredProductMeasure n) f 2 :=
  actualCubicRemainderGram_eq_thirtysix_of_exponential_diagonal
    (centeredProduct_third_cumulants n) f hdiag

/-- The proper-remainder application still lists the original admissibility
and test-integrability hypotheses; only the cumulant premise is discharged. -/
theorem centeredProduct_proper_remainder_bound {n : ℕ}
    (hμ : admissibleMeasure (centeredProductMeasure n))
    {f : Space n → ℝ} (hf : MemLp f 2 (centeredProductMeasure n)) :
    ‖(WithLp.toLp 2 (actualAppellProperRemainder (centeredProductMeasure n) f 3) :
      EuclideanSpace ℝ (Fin 3 → Fin n))‖ ≤
        6*Real.sqrt (actualAppellEnergy (centeredProductMeasure n) f 2) := by
  let : IsProbabilityMeasure (centeredProductMeasure n) := hμ.isProb
  exact actualAppellProperRemainder_three_norm_le_of_exponential_third hμ hf
    (centeredProduct_third_cumulants n)

end KLSImprovement.ActualProductCumulants

#print axioms KLSImprovement.ActualProductCumulants.centeredProduct_triple_moment
#print axioms KLSImprovement.ActualProductCumulants.centeredProduct_third_cumulants
#print axioms KLSImprovement.ActualProductCumulants.centeredProduct_cubic_gram
#print axioms KLSImprovement.ActualProductCumulants.centeredProduct_cubic_gram_le_thirtysix

#print axioms KLSImprovement.ActualProductCumulants.centeredProduct_cubic_gram_eq_thirtysix_of_diagonal
#print axioms KLSImprovement.ActualProductCumulants.centeredProduct_proper_remainder_bound
