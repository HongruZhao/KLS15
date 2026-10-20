import MomentMapThirdPairing
import TwoSlotMatrixReduction

/-! The genuine two-slot cubic contraction for a regular bounded-gradient
moment map. The source and target laws are actual measures. Moment-map
existence, extension to the full class, and all-degree induction remain
separate obligations. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Set Filter
open scoped ContDiff BigOperators ENNReal Matrix.Norms.Elementwise
namespace KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ V : Space n → ℝ}

theorem sum_hessian_gradient_pairings_sq_le_trace
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hφconv : ConvexOn ℝ univ φ) (hVconv : ConvexOn ℝ univ V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (hgrad : Bornology.IsBounded (range (gradient φ)))
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    (R : Matrix (Fin n) (Fin n) ℝ) :
    (∑ a, ∑ b, ∑ k,
      (∫ x, gradient φ x k * hessianCongruence φ R x a b
        ∂potentialMeasure φ)^2) ≤
      ((R.transpose*R)*(R.transpose*R)).trace := by
  have hB : (R.transpose*R).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self R
  have htrace := integral_hessianTraceSquare_le_two_trace_of_bounded_gradient
    hφ hV hφconv hVconv hpos hMA hH hgrad hiso hB
  have hs : (∑ a, ∑ b, ∑ k,
      (∫ x, gradient φ x k * hessianCongruence φ R x a b
        ∂potentialMeasure φ)^2) ≤
      ∑ a, ∑ b, ProbabilityTheory.variance
        (fun x => hessianCongruence φ R x a b) (potentialMeasure φ) := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    exact sum_gradient_pairing_sq_le_variance (hφ.of_le (by norm_num)) hiso
      (memLp_hessianCongruence_entry hφ hH R a b)
  rw [sum_variance_hessianCongruence hφ hH hiso R] at hs
  linarith

def gradientThirdMoment (φ : Space n → ℝ) (k : Fin n) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  ∫ x, gradient φ x i * gradient φ x j * gradient φ x k ∂potentialMeasure φ

/-- The target cubic entries used below are integrable, so the actual-law
contraction is not relying on default-valued Bochner integrals. -/
theorem integrable_coordinate_cubic_gradientPushforward
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 2 φ)
    (hgrad : Bornology.IsBounded (range (gradient φ))) (i j k : Fin n) :
    Integrable (fun y : Space n => y i*y j*y k) (MomentMap.gradientPushforward φ) := by
  letI : IsFiniteMeasure (MomentMap.gradientPushforward φ) := by
    unfold MomentMap.gradientPushforward
    infer_instance
  have hgm : AEMeasurable (gradient φ) (potentialMeasure φ) :=
    (MomentMap.contDiff_gradient_of_contDiff_two hφ).continuous.measurable.aemeasurable
  have hs : MemLp (fun x => gradient φ x i*gradient φ x j*gradient φ x k)
      1 (potentialMeasure φ) :=
    memLp_comp_bounded_gradient hφ hgrad
      (by fun_prop : Continuous (fun y : Space n => y i*y j*y k)) 1
  have ht : MemLp (fun y : Space n => y i*y j*y k) 1 (MomentMap.gradientPushforward φ) :=
    (memLp_map_measure_iff
      (by fun_prop : AEStronglyMeasurable (fun y : Space n => y i*y j*y k)
        (MomentMap.gradientPushforward φ)) hgm).mpr hs
  exact ht.integrable (by norm_num)

theorem integral_hessianCongruence_mul_gradient_eq_half_cubic
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ)
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (hgrad : Bornology.IsBounded (range (gradient φ)))
    (R : Matrix (Fin n) (Fin n) ℝ) (a b k : Fin n) :
    (∫ x, gradient φ x k * hessianCongruence φ R x a b
      ∂potentialMeasure φ) =
      (1/2 : ℝ)*(R*gradientThirdMoment φ k*R.transpose) a b := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have hg : MemLp (fun x => gradient φ x k) 2 (potentialMeasure φ) :=
    memLp_comp_bounded_gradient hφ2 hgrad
      (by fun_prop : Continuous (fun y : Space n => y k)) 2
  have hentry (i j : Fin n) : Integrable
      (fun x => (gradient φ x k • coordinateHessian φ x) i j)
      (potentialMeasure φ) := by
    convert hg.integrable_mul (memLp_coordinateHessian_entry_of_bounded hφ hH i j) using 1
  have hfun : (fun x => gradient φ x k * hessianCongruence φ R x a b) =
      fun x => (R*(gradient φ x k • coordinateHessian φ x)*R.transpose) a b := by
    funext x
    simp [hessianCongruence, Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul]
  rw [hfun, integral_matrix_congruence_entry hentry R a b]
  have hmean : Matrix.of (fun i j =>
      ∫ x, (gradient φ x k • coordinateHessian φ x) i j ∂potentialMeasure φ) =
      (1/2 : ℝ) • gradientThirdMoment φ k := by
    ext i j
    change (∫ x, gradient φ x k * coordinateHessian φ x i j ∂potentialMeasure φ) = _
    rw [show (fun x => gradient φ x k * coordinateHessian φ x i j) =
      (fun x => coordinateHessian φ x i j * gradient φ x k) by
        funext x; ring]
    exact integral_hessian_mul_gradient_eq_half_cubic hφ hH hgrad i j k
  rw [hmean]
  simp [Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul]

theorem sum_gradient_cubic_congruence_sq_le_four_trace
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hφconv : ConvexOn ℝ univ φ) (hVconv : ConvexOn ℝ univ V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (hgrad : Bornology.IsBounded (range (gradient φ)))
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    (R : Matrix (Fin n) (Fin n) ℝ) :
    (∑ a, ∑ b, ∑ k, ((R*gradientThirdMoment φ k*R.transpose) a b)^2) ≤
      4*((R.transpose*R)*(R.transpose*R)).trace := by
  have hp := sum_hessian_gradient_pairings_sq_le_trace
    hφ hV hφconv hVconv hpos hMA hH hgrad hiso R
  have he (a b k : Fin n) : ((R*gradientThirdMoment φ k*R.transpose) a b)^2 =
      4*(∫ x, gradient φ x k*hessianCongruence φ R x a b
        ∂potentialMeasure φ)^2 := by
    rw [integral_hessianCongruence_mul_gradient_eq_half_cubic hφ hH hgrad R a b k]
    ring
  simp_rw [he]
  simp only [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hp (by norm_num)

theorem thirdCumulantMatrix_gradientPushforward_coordinate
    (hφ : ContDiff ℝ 2 φ) (k : Fin n) :
    thirdCumulantMatrix (MomentMap.gradientPushforward φ) (MomentMap.coordinateVector k) =
      gradientThirdMoment φ k := by
  have hgm : AEMeasurable (gradient φ) (potentialMeasure φ) :=
    (MomentMap.contDiff_gradient_of_contDiff_two hφ).continuous.measurable.aemeasurable
  ext i j
  unfold thirdCumulantMatrix gradientThirdMoment
  rw [MomentMap.gradientPushforward, integral_map hgm
    (by fun_prop : AEStronglyMeasurable
      (fun y : Space n => inner ℝ y (MomentMap.coordinateVector k)*y i*y j)
      (Measure.map (gradient φ) (potentialMeasure φ)))]
  apply integral_congr_ae
  exact .of_forall fun x => by
    simp only [MomentMap.coordinateVector, EuclideanSpace.inner_single_right,
      RCLike.conj_to_real, mul_one]
    ring

theorem sum_thirdCumulant_congruence_sq_le_four_trace
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hφconv : ConvexOn ℝ univ φ) (hVconv : ConvexOn ℝ univ V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (hgrad : Bornology.IsBounded (range (gradient φ)))
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    (R : Matrix (Fin n) (Fin n) ℝ) :
    (∑ a, ∑ b, ∑ k,
      ((R*thirdCumulantMatrix (MomentMap.gradientPushforward φ)
        (MomentMap.coordinateVector k)*R.transpose) a b)^2) ≤
      4*((R.transpose*R)*(R.transpose*R)).trace := by
  simp_rw [thirdCumulantMatrix_gradientPushforward_coordinate (hφ.of_le (by norm_num))]
  exact sum_gradient_cubic_congruence_sq_le_four_trace
    hφ hV hφconv hVconv hpos hMA hH hgrad hiso R

/-- Manuscript (3.11), for every symmetric test matrix including singular
and indefinite matrices, on the genuine regular moment-map target law. -/
theorem thirdCumulant_two_slot_bound_regular_momentMap
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hφconv : ConvexOn ℝ univ φ) (hVconv : ConvexOn ℝ univ V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (hgrad : Bornology.IsBounded (range (gradient φ)))
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    (H : Matrix (Fin n) (Fin n) ℝ) (hHsymm : H.IsSymm) :
    (∑ k,
      (H*thirdCumulantMatrix (MomentMap.gradientPushforward φ) (MomentMap.coordinateVector k)*
        H*thirdCumulantMatrix (MomentMap.gradientPushforward φ) (MomentMap.coordinateVector k)).trace) ≤
      4*matrixFrobeniusSq H := by
  apply symmetric_contraction_of_congruence_bound
    (fun k => thirdCumulantMatrix (MomentMap.gradientPushforward φ) (MomentMap.coordinateVector k))
    4 ?_ H hHsymm
  intro R
  have hc := sum_thirdCumulant_congruence_sq_le_four_trace
    hφ hV hφconv hVconv hpos hMA hH hgrad hiso R
  have he : (∑ k, matrixFrobeniusSq
      (R*thirdCumulantMatrix (MomentMap.gradientPushforward φ) (MomentMap.coordinateVector k)*R.transpose)) =
      ∑ a, ∑ b, ∑ k,
        ((R*thirdCumulantMatrix (MomentMap.gradientPushforward φ)
          (MomentMap.coordinateVector k)*R.transpose) a b)^2 := by
    unfold matrixFrobeniusSq
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_comm
  rw [he, matrixFrobeniusSq_eq_trace_sq (Matrix.isSymm_transpose_mul_self R)]
  exact hc

#print axioms sum_hessian_gradient_pairings_sq_le_trace
#print axioms integrable_coordinate_cubic_gradientPushforward
#print axioms integral_hessianCongruence_mul_gradient_eq_half_cubic
#print axioms thirdCumulantMatrix_gradientPushforward_coordinate
#print axioms sum_thirdCumulant_congruence_sq_le_four_trace
#print axioms thirdCumulant_two_slot_bound_regular_momentMap
end KLS.DeterministicBridgeIntegration
