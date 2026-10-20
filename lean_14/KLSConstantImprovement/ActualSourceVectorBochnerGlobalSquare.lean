import KLSConstantImprovement.ActualSourceVectorBochnerFirstOrderDomain

/-! Actual global vector square under first-order L2 and bounded Hessian.
No compact support, derivative-N domain, optimizer or operator-core premise.
The actual source/pushforward literal-polynomial domain application stays
separate; this module proves the density identity and finite summation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory KLS Filter
open scoped BigOperators ContDiff
namespace KLSConstantImprovement.ActualSourceVectorBochnerGlobalSquare
open ActualCompactSourceVectorBochner ActualSourceVectorBochnerFirstOrderDomain
variable {n : ℕ}

theorem bounded_hessian_product_integrable {φ a b : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (ha2 : MemLp a 2 (potentialMeasure φ)) (hb2 : MemLp b 2 (potentialMeasure φ))
    {M : ℝ} (hM : 0 ≤ M) (hH : ∀ x i j, |coordinateHessian φ x i j| ≤ M)
    (i j : Fin n) :
    Integrable (fun x => coordinateHessian φ x i j*a x*b x) (potentialMeasure φ) := by
  have hh := (contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous
  apply ((ha2.integrable_mul hb2).norm.const_mul M).mono'
    ((hh.mul ha.continuous).mul hb.continuous).aestronglyMeasurable
  filter_upwards [] with x
  change ‖coordinateHessian φ x i j*a x*b x‖ ≤ M*‖a x*b x‖
  simp only [Real.norm_eq_abs]
  calc
    _ = |coordinateHessian φ x i j| * |a x*b x| := by rw [abs_mul, abs_mul, abs_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hH x i j) (abs_nonneg _)

theorem integral_source_vector_adjoint_square_of_L2_first_order {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (a : Fin n → Space n → ℝ)
    (ha : ∀ i, ContDiff ℝ 2 (a i))
    (ha2 : ∀ i, MemLp (a i) 2 (potentialMeasure φ))
    (hδa : ∀ i, MemLp (coordinateSourceAdjoint φ (a i) i) 2 (potentialMeasure φ))
    (hDa : ∀ i j, MemLp (coordinateDerivative (a i) j) 2 (potentialMeasure φ))
    {M : ℝ} (hM : 0 ≤ M) (hH : ∀ x i j, |coordinateHessian φ x i j| ≤ M) :
    (∫ x, (sourceVectorAdjoint φ a x)^2 ∂potentialMeasure φ) =
      ∫ x, ∑ i : Fin n, ∑ j : Fin n,
        (coordinateHessian φ x i j*a i x*a j x+
          coordinateDerivative (a i) j x*coordinateDerivative (a j) i x)
        ∂potentialMeasure φ := by
  have hcurv (i j : Fin n) := bounded_hessian_product_integrable hφ (ha i) (ha j)
    (ha2 i) (ha2 j) hM hH i j
  have hderiv (i j : Fin n) : Integrable (fun x =>
      coordinateDerivative (a i) j x*coordinateDerivative (a j) i x)
      (potentialMeasure φ) := (hDa i j).integrable_mul (hDa j i)
  have hi (i j : Fin n) : Integrable (fun x =>
      coordinateSourceAdjoint φ (a i) i x*coordinateSourceAdjoint φ (a j) j x)
      (potentialMeasure φ) := (hδa i).integrable_mul (hδa j)
  have hj (i j : Fin n) : Integrable (fun x =>
      coordinateHessian φ x i j*a i x*a j x+
        coordinateDerivative (a i) j x*coordinateDerivative (a j) i x)
      (potentialMeasure φ) := (hcurv i j).add (hderiv i j)
  calc
    _ = ∫ x, ∑ i : Fin n, ∑ j : Fin n,
        coordinateSourceAdjoint φ (a i) i x*coordinateSourceAdjoint φ (a j) j x
        ∂potentialMeasure φ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [sourceVectorAdjoint, pow_two, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ∫ x, coordinateSourceAdjoint φ (a i) i x*coordinateSourceAdjoint φ (a j) j x
          ∂potentialMeasure φ := by
      rw [integral_finsetSum Finset.univ
        (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ∫ x, coordinateHessian φ x i j*a i x*a j x+
          coordinateDerivative (a i) j x*coordinateDerivative (a j) i x
          ∂potentialMeasure φ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [source_vector_bochner_coordinate_of_L2_first_order hφ (ha i) (ha j) i j
        (ha2 i) (hδa i) (hδa j) (hDa i j) (hDa j i) (hcurv i j),
        integral_add (hcurv i j) (hderiv i j)]
    _ = _ := by
      symm
      rw [integral_finsetSum Finset.univ
        (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hj i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hj i j)]

end KLSConstantImprovement.ActualSourceVectorBochnerGlobalSquare
#print axioms KLSConstantImprovement.ActualSourceVectorBochnerGlobalSquare.bounded_hessian_product_integrable
#print axioms KLSConstantImprovement.ActualSourceVectorBochnerGlobalSquare.integral_source_vector_adjoint_square_of_L2_first_order
