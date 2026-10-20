import KLSConstantImprovement.ActualCompactWeakSourceVectorBochner

/-! Finite vector summation of actual compact H1 source-coordinate Bochner.
The Jacobian product keeps its exact signed transpose pairing. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators ContDiff Topology NNReal ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualCompactWeakSourceVectorSquare
open KLS ActualCompactWeakSourceVectorBochner
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def rawWeakSourceVectorAdjoint (φ : Space n → ℝ)
    (a : Fin n → Space n → ℝ) (Da : Fin n → Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i, rawWeakSourceAdjoint φ (a i) (Da i i) i x

theorem integral_compact_rawWeak_source_vector_adjoint_square
    {φ : Space n → ℝ} {L G : ℝ≥0}
    (hφ : ContDiff ℝ 1 φ) (hLip : LipschitzWith L φ)
    (hG : LipschitzWith G (gradient φ))
    (a : Fin n → Space n → ℝ) (Da : Fin n → Fin n → Space n → ℝ)
    (hac : ∀ i, HasCompactSupport (a i))
    (ha2 : ∀ i, MemLp (a i) 2 (potentialMeasure φ))
    (hDa2 : ∀ i j, MemLp (Da i j) 2 (potentialMeasure φ))
    (hDac : ∀ i j, HasCompactSupport (Da i j))
    (hDaw : ∀ i j, HasLocalWeakCoordinateDerivative (a i) (Da i j) j) :
    (∫ x, (rawWeakSourceVectorAdjoint φ a Da x)^2 ∂potentialMeasure φ) =
      ∫ x, ∑ i : Fin n, ∑ j : Fin n,
        (coordinateHessian φ x i j * a i x * a j x + Da i j x * Da j i x)
          ∂potentialMeasure φ := by
  have hφtop (i : Fin n) := source_coordinate_memLp_top_of_lipschitz hLip (potentialMeasure φ) i
  have hδa (i : Fin n) : MemLp (rawWeakSourceAdjoint φ (a i) (Da i i) i)
      2 (potentialMeasure φ) := ((hφtop i).mul (ha2 i)).sub (hDa2 i i)
  have hcurv (i j : Fin n) : Integrable
      (fun x => coordinateHessian φ x i j * a i x * a j x) (potentialMeasure φ) := by
    have hm : MemLp (fun x => coordinateHessian φ x i j * a i x) 2 (potentialMeasure φ) :=
      (memLp_coordinateHessian_top_of_gradient_lipschitz hG (potentialMeasure φ) i j).mul (ha2 i)
    exact hm.integrable_mul (ha2 j)
  have hderiv (i j : Fin n) : Integrable (fun x => Da i j x * Da j i x)
      (potentialMeasure φ) := (hDa2 i j).integrable_mul (hDa2 j i)
  have hi (i j : Fin n) : Integrable (fun x =>
      rawWeakSourceAdjoint φ (a i) (Da i i) i x * rawWeakSourceAdjoint φ (a j) (Da j j) j x)
      (potentialMeasure φ) := (hδa i).integrable_mul (hδa j)
  have hj (i j : Fin n) : Integrable (fun x =>
      coordinateHessian φ x i j * a i x * a j x + Da i j x * Da j i x)
      (potentialMeasure φ) := (hcurv i j).add (hderiv i j)
  calc
    _ = ∫ x, ∑ i : Fin n, ∑ j : Fin n,
        rawWeakSourceAdjoint φ (a i) (Da i i) i x *
          rawWeakSourceAdjoint φ (a j) (Da j j) j x ∂potentialMeasure φ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [rawWeakSourceVectorAdjoint, pow_two, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ i : Fin n, ∑ j : Fin n, ∫ x,
        rawWeakSourceAdjoint φ (a i) (Da i i) i x *
          rawWeakSourceAdjoint φ (a j) (Da j j) j x ∂potentialMeasure φ := by
      rw [integral_finsetSum Finset.univ
        (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
    _ = ∑ i : Fin n, ∑ j : Fin n, ∫ x,
        coordinateHessian φ x i j * a i x * a j x + Da i j x * Da j i x
          ∂potentialMeasure φ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [compact_rawWeak_source_vector_bochner_coordinate hφ hLip hG
        (hac i) (hac j) (ha2 i) (ha2 j) (hDa2 i) (hDa2 j)
        (hDac i) (hDac j) (hDaw i) (hDaw j) i j,
        integral_add (hcurv i j) (hderiv i j)]
    _ = _ := by
      symm
      rw [integral_finsetSum Finset.univ
        (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hj i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hj i j)]

end KLSConstantImprovement.ActualCompactWeakSourceVectorSquare
#print axioms KLSConstantImprovement.ActualCompactWeakSourceVectorSquare.integral_compact_rawWeak_source_vector_adjoint_square
