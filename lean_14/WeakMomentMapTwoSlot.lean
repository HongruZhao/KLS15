import WeakMomentMapThirdPairing
import KLS.MomentGradientRange

/-! The actual weak moment-map two-slot contraction. Source C1,1 regularity,
trace2, and the bounded target representation are derived or explicitly
specified; no smooth source moment-map existence is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Set Filter
open scoped ContDiff BigOperators ENNReal NNReal Matrix.Norms.Elementwise
namespace KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ} {G : ℝ≥0}

theorem sum_gradient_pairing_sq_le_variance_C11
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hgc : Continuous (gradient φ))
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    {g : Space n → ℝ} (hg : MemLp g 2 (potentialMeasure φ)) :
    (∑ k, (∫ x, gradient φ x k * g x ∂potentialMeasure φ) ^ 2) ≤
      ProbabilityTheory.variance g (potentialMeasure φ) := by
  let a : Space n := WithLp.toLp 2 (fun k => ∫ x, gradient φ x k * g x ∂potentialMeasure φ)
  let f : Space n → ℝ := fun x => inner ℝ (gradient φ x) a
  have hgm : AEMeasurable (gradient φ) (potentialMeasure φ) :=
    hgc.measurable.aemeasurable
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


theorem integral_hessianCongruence_mul_gradient_eq_half_cubic_C11
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hG : LipschitzWith G (gradient φ))
    (hgrad : Bornology.IsBounded (range (gradient φ)))
    (R : Matrix (Fin n) (Fin n) ℝ) (a b k : Fin n) :
    (∫ x, gradient φ x k * hessianCongruence φ R x a b
      ∂potentialMeasure φ) =
      (1/2 : ℝ)*(R*gradientThirdMoment φ k*R.transpose) a b := by
  have hg : MemLp (fun x => gradient φ x k) 2 (potentialMeasure φ) :=
    memLp_comp_continuous_bounded_gradient hG.continuous hgrad
      (by fun_prop : Continuous (fun y : Space n => y k)) 2
  have hentry (i j : Fin n) : Integrable
      (fun x => (gradient φ x k • coordinateHessian φ x) i j)
      (potentialMeasure φ) := by
    convert hg.integrable_mul (memLp_actual_hessian_entry_of_global_gradient_lipschitz hG i j 2) using 1
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
    exact integral_hessian_mul_gradient_eq_half_cubic_C11 hφ hG hgrad i j k
  rw [hmean]
  simp [Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul]


theorem thirdCumulantMatrix_gradientPushforward_coordinate_C11
    (hgc : Continuous (gradient φ)) (k : Fin n) :
    thirdCumulantMatrix (MomentMap.gradientPushforward φ) (MomentMap.coordinateVector k) =
      gradientThirdMoment φ k := by
  have hgm : AEMeasurable (gradient φ) (potentialMeasure φ) :=
    hgc.measurable.aemeasurable
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


theorem bounded_gradient_of_lipschitz_convex_C1 {L : ℝ≥0}
    (hLip : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ) (hφ : ContDiff ℝ 1 φ) :
    Bornology.IsBounded (range (gradient φ)) := by
  apply (Metric.isBounded_closedBall (x := (0 : Space n)) (r := (L : ℝ))).subset
  rintro y ⟨x,rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_of_mem_convexSubgradient hLip
    (gradient_mem_convexSubgradient hc (hφ.differentiable (by norm_num) x))

/-- The literal full symmetric two-slot estimate from a genuine original
weak uniform moment-map representation. Source regularity is constructed. -/
theorem thirdCumulant_two_slot_bound_weak_uniform_momentMap
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 2 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p-(κ/2)*‖p‖^2))
    [IsProbabilityMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hiso : IsIsotropic (MomentMap.gradientPushforward u))
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    (∑ k, (H*thirdCumulantMatrix (MomentMap.gradientPushforward u) (MomentMap.coordinateVector k)*
      H*thirdCumulantMatrix (MomentMap.gradientPushforward u) (MomentMap.coordinateVector k)).trace) ≤
      4*matrixFrobeniusSq H := by
  have hu := moment_contDiff_one_closedTarget hLip hc hV.continuous hK hKc hpush
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc (hV.of_le (by norm_num)) hVc hκ hstrong hK hKc hpush
  have hgrad := bounded_gradient_of_lipschitz_convex_C1 hLip hc hu
  apply symmetric_contraction_of_congruence_bound
    (fun k => thirdCumulantMatrix (MomentMap.gradientPushforward u) (MomentMap.coordinateVector k))
    4 ?_ H hH
  intro R
  have hB : (R.transpose*R).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self R
  have htrace := (weak_moment_trace_square_le_twice_trace
    hLip hc hV hVc hκ hstrong hK hKc hpush hiso hB).2
  change (∫ x, hessianTraceSquare u (R.transpose*R) x ∂potentialMeasure u) ≤
    2*((R.transpose*R)*(R.transpose*R)).trace at htrace
  have hp : (∑ a, ∑ b, ∑ k,
      (∫ x, gradient u x k*hessianCongruence u R x a b ∂potentialMeasure u)^2) ≤
      ((R.transpose*R)*(R.transpose*R)).trace := by
    have hs : (∑ a, ∑ b, ∑ k,
        (∫ x, gradient u x k*hessianCongruence u R x a b ∂potentialMeasure u)^2) ≤
        ∑ a, ∑ b, ProbabilityTheory.variance
          (fun x => hessianCongruence u R x a b) (potentialMeasure u) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact sum_gradient_pairing_sq_le_variance_C11 hG.continuous hiso
        (memLp_hessianCongruence_entry_C11 hG R a b)
    rw [sum_variance_hessianCongruence_C11 hu hG hiso R] at hs
    linarith
  have he (a b k : Fin n) :
      ((R*thirdCumulantMatrix (MomentMap.gradientPushforward u)
        (MomentMap.coordinateVector k)*R.transpose) a b)^2 =
      4*(∫ x, gradient u x k*hessianCongruence u R x a b ∂potentialMeasure u)^2 := by
    rw [thirdCumulantMatrix_gradientPushforward_coordinate_C11 hG.continuous]
    rw [integral_hessianCongruence_mul_gradient_eq_half_cubic_C11 hu hG hgrad R a b k]
    ring
  have hsum : (∑ k, matrixFrobeniusSq
      (R*thirdCumulantMatrix (MomentMap.gradientPushforward u) (MomentMap.coordinateVector k)*R.transpose)) =
      ∑ a, ∑ b, ∑ k,
        ((R*thirdCumulantMatrix (MomentMap.gradientPushforward u)
          (MomentMap.coordinateVector k)*R.transpose) a b)^2 := by
    unfold matrixFrobeniusSq
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_comm
  rw [hsum]
  simp_rw [he]
  simp only [← Finset.mul_sum]
  rw [matrixFrobeniusSq_eq_trace_sq (Matrix.isSymm_transpose_mul_self R)]
  exact mul_le_mul_of_nonneg_left hp (by norm_num)

#print axioms integral_hessianCongruence_mul_gradient_eq_half_cubic_C11
#print axioms thirdCumulant_two_slot_bound_weak_uniform_momentMap
end KLS.DeterministicBridgeIntegration
