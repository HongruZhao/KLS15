import KLS.HessianTraceBoundedGradient
import KLS.HessianEntryBrascampLieb
import KLS.ThirdCumulant
import KLS.AffineMomentMapContraction

/-! Actual cubic Stein pairing and pullback Bessel estimate.  The source law
is exp(-φ) dx and the coordinates are the genuine gradient pushforward.
Moment-map existence and the all-degree Appell induction are not asserted. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Set Filter
open scoped ContDiff BigOperators ENNReal Matrix.Norms.Elementwise
namespace KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ}

theorem memLp_comp_bounded_gradient [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ)
    (hb : Bornology.IsBounded (range (gradient φ)))
    {F : Space n → ℝ} (hF : Continuous F) (p : ℝ≥0∞) :
    MemLp (fun x => F (gradient φ x)) p (potentialMeasure φ) := by
  obtain ⟨C, hC⟩ := hb.isCompact_closure.bddAbove_image hF.norm.continuousOn
  apply MemLp.of_bound (hF.comp (MomentMap.contDiff_gradient_of_contDiff_two hφ).continuous).aestronglyMeasurable C
  exact .of_forall fun x => hC ⟨gradient φ x, subset_closure ⟨x, rfl⟩, rfl⟩

theorem integral_gradient_cubic_eq_hessian_pairings
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ)
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (hgrad : Bornology.IsBounded (range (gradient φ))) (i j k : Fin n) :
    (∫ x, gradient φ x i * gradient φ x j * gradient φ x k ∂potentialMeasure φ) =
      (∫ x, coordinateHessian φ x i k * gradient φ x j ∂potentialMeasure φ) +
      ∫ x, coordinateHessian φ x j k * gradient φ x i ∂potentialMeasure φ := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have hd := (MomentMap.contDiff_gradient_of_contDiff_two hφ2).differentiable (by norm_num)
  have hgi (a : Fin n) : MemLp (fun x => gradient φ x a) 2 (potentialMeasure φ) :=
    memLp_comp_bounded_gradient hφ2 hgrad
      (by fun_prop : Continuous (fun y : Space n => y a)) 2
  have hhi (a b : Fin n) := memLp_coordinateHessian_entry_of_bounded hφ hH a b
  have h1 := (hgi i).integrable_mul (hgi j)
  have h2 := (hhi i k).integrable_mul (hgi j)
  have h3 := (hgi i).integrable_mul (hhi j k)
  have h4 : Integrable (fun x => gradient φ x i * gradient φ x j * gradient φ x k)
      (potentialMeasure φ) :=
    (memLp_comp_bounded_gradient hφ2 hgrad
      (by fun_prop : Continuous (fun y : Space n => y i * y j * y k)) 1).integrable (by norm_num)
  have hid (a : Fin n) : Differentiable ℝ (fun x => gradient φ x a) :=
    (EuclideanSpace.proj (𝕜 := ℝ) a).differentiable.comp hd
  have hdcoord (x : Space n) (a b : Fin n) :
      fderiv ℝ (fun y => gradient φ y a) x (MomentMap.coordinateVector b) =
        coordinateHessian φ x a b := by
    change MomentMap.hessianMatrix φ x a b = _
    rw [momentMap_hessianMatrix_eq_coordinateHessian hφ2]
  have h := integral_mul_fderiv_potentialMeasure (hφ2.differentiable (by norm_num))
    (hid i) (hid j) (MomentMap.coordinateVector k) h1
    (by
      simp only [hdcoord]
      convert h2 using 1)
    (by
      simp only [hdcoord]
      convert h3 using 1)
    (by simpa only [← MomentMap.gradient_coordinate_eq_fderiv] using h4)
  simp only [hdcoord,
    ← MomentMap.gradient_coordinate_eq_fderiv] at h
  have hc : (∫ x, gradient φ x i * coordinateHessian φ x j k ∂potentialMeasure φ) =
      ∫ x, coordinateHessian φ x j k * gradient φ x i ∂potentialMeasure φ := by
    congr 1; funext x; ring
  rw [hc] at h
  linarith

theorem integral_hessian_mul_gradient_eq_half_cubic
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ)
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (hgrad : Bornology.IsBounded (range (gradient φ))) (i j k : Fin n) :
    (∫ x, coordinateHessian φ x i j * gradient φ x k ∂potentialMeasure φ) =
      (1 / 2 : ℝ) * ∫ x,
        gradient φ x i * gradient φ x j * gradient φ x k ∂potentialMeasure φ := by
  have h1 := integral_gradient_cubic_eq_hessian_pairings hφ hH hgrad i j k
  have h2 := integral_gradient_cubic_eq_hessian_pairings hφ hH hgrad i k j
  have h3 := integral_gradient_cubic_eq_hessian_pairings hφ hH hgrad j k i
  have hs (x : Space n) (a b : Fin n) : coordinateHessian φ x a b = coordinateHessian φ x b a :=
    ((coordinateHessian_symmetric (hφ.of_le (by norm_num)) x).apply a b).symm
  simp_rw [hs _ k j, hs _ k i, hs _ j i] at h2 h3
  have hc1 : (∫ x, gradient φ x i * gradient φ x k * gradient φ x j ∂potentialMeasure φ) =
      ∫ x, gradient φ x i * gradient φ x j * gradient φ x k ∂potentialMeasure φ := by
    congr 1; funext x; ring
  have hc2 : (∫ x, gradient φ x j * gradient φ x k * gradient φ x i ∂potentialMeasure φ) =
      ∫ x, gradient φ x i * gradient φ x j * gradient φ x k ∂potentialMeasure φ := by
    congr 1; funext x; ring
  rw [hc1] at h2
  rw [hc2] at h3
  linarith

theorem sum_gradient_pairing_sq_le_variance
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ)
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    {g : Space n → ℝ} (hg : MemLp g 2 (potentialMeasure φ)) :
    (∑ k, (∫ x, gradient φ x k * g x ∂potentialMeasure φ) ^ 2) ≤
      ProbabilityTheory.variance g (potentialMeasure φ) := by
  let a : Space n := WithLp.toLp 2 (fun k => ∫ x, gradient φ x k * g x ∂potentialMeasure φ)
  let f : Space n → ℝ := fun x => inner ℝ (gradient φ x) a
  have hgm : AEMeasurable (gradient φ) (potentialMeasure φ) :=
    (MomentMap.contDiff_gradient_of_contDiff_two hφ).continuous.measurable.aemeasurable
  have hf : MemLp f 2 (potentialMeasure φ) :=
    (memLp_map_measure_iff
      (by fun_prop : AEStronglyMeasurable (fun y : Space n => inner ℝ y a)
        (MomentMap.gradientPushforward φ)) hgm).mp (hiso.memLp_inner a)
  have hm : (∫ x, f x ∂potentialMeasure φ) = 0 := by
    rw [show (∫ x, f x ∂potentialMeasure φ) =
      ∫ y, inner ℝ y a ∂MomentMap.gradientPushforward φ from
        (integral_map hgm (by fun_prop : AEStronglyMeasurable
          (fun y : Space n => inner ℝ y a) (MomentMap.gradientPushforward φ))).symm]
    exact hiso.integral_inner a
  have hnorm : ProbabilityTheory.variance f (potentialMeasure φ) = ‖a‖ ^ 2 := by
    rw [variance_eq_sub hf, hm, zero_pow (by decide), sub_zero]
    change (∫ x, (inner ℝ (gradient φ x) a) ^ 2 ∂potentialMeasure φ) = _
    rw [show (∫ x, (inner ℝ (gradient φ x) a) ^ 2 ∂potentialMeasure φ) =
      ∫ y, (inner ℝ y a) ^ 2 ∂MomentMap.gradientPushforward φ from
        (integral_map hgm (by fun_prop : AEStronglyMeasurable
          (fun y : Space n => (inner ℝ y a) ^ 2) (MomentMap.gradientPushforward φ))).symm]
    exact hiso.integral_inner_sq a
  have hp : (∫ x, f x * g x ∂potentialMeasure φ) = ‖a‖ ^ 2 := by
    have hgi (k : Fin n) : MemLp (fun x => gradient φ x k) 2 (potentialMeasure φ) :=
      (memLp_map_measure_iff
        (by fun_prop : AEStronglyMeasurable (fun y : Space n => y k)
          (MomentMap.gradientPushforward φ)) hgm).mp (hiso.memLp_coordinate k)
    simp only [f, inner_eq_coordinate_sum, Finset.sum_mul, mul_assoc]
    have hterm (k : Fin n) : Integrable (fun x => a k * (gradient φ x k * g x))
        (potentialMeasure φ) := ((hgi k).integrable_mul hg).const_mul (a k)
    rw [integral_finsetSum Finset.univ (fun k _ => hterm k)]
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul]
    change (∫ x, gradient φ x k * g x ∂potentialMeasure φ) *
      (∫ x, gradient φ x k * g x ∂potentialMeasure φ) = _
    dsimp [a]
    ring
  have hc := covariance_sq_le_variance_mul_variance hf hg
  rw [covariance_eq_sub hf hg, hm, zero_mul, sub_zero, hnorm] at hc
  change (∫ x, f x * g x ∂potentialMeasure φ) ^ 2 ≤ _ at hc
  rw [hp] at hc
  have ha : ‖a‖ ^ 2 ≤ ProbabilityTheory.variance g (potentialMeasure φ) := by
    nlinarith [sq_nonneg ‖a‖, variance_nonneg g (potentialMeasure φ)]
  simpa only [EuclideanSpace.real_norm_sq_eq, a] using ha

#print axioms integral_hessian_mul_gradient_eq_half_cubic
#print axioms sum_gradient_pairing_sq_le_variance
end KLS.DeterministicBridgeIntegration
