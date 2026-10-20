import KLSConstantImprovement.ActualFixedTargetSource405
import KLSConstantImprovement.ActualTargetWeakApproximation
import KLS.StrongConvexAffine
import KLS.RegularMomentMapQuadratic

/-! Actual bounded-source exhaustion of a fixed globally smooth strongly
convex target. The affine cutoff potential and its convexity constant are
retained, giving a common gradient-Lipschitz bound independent of radius. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix Metric
open scoped Topology NNReal ContDiff
namespace KLSConstantImprovement.ActualStrongTargetExhaustion405
open KLS ActualBoundedCanonicalSource ActualFixedTargetSource405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_sourceData_affine_condition (hμ : admissibleMeasure μ)
    {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    {κ : ℝ} (hκ : 0 < κ) (hs : StrongConvexOn univ κ V)
    (heq : μ = potentialMeasure V) {r : ℝ} (hr : 0 < r)
    (hm : μ (closedBall (0 : Space n) r) ≠ 0)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (hA : A.det ≠ 0)
    (ha : admissibleMeasure (affineMatrixMeasure (ProbabilityTheory.cond μ (closedBall 0 r)) A b)) :
    ∃ d : SourceData (affineMatrixMeasure (ProbabilityTheory.cond μ (closedBall 0 r)) A b),
      d.targetPotential = affineTransformedPotential
        (fun x => V x + Real.log (μ.real (closedBall 0 r))) A b hA ∧
      d.targetConvexityConstant = κ / (‖matrixAction A‖ + 1) ^ 2 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let e := affineMatrixEquiv A b hA
  let W := fun x => V x + Real.log (μ.real (closedBall (0 : Space n) r))
  have hW : ContDiff ℝ (⊤ : ℕ∞) W := hV.add contDiff_const
  have hstrong : StrongConvexOn univ κ W := strongConvexOn_add_const hs _
  have hKc : Convex ℝ (e '' ball (0 : Space n) r) :=
    Convex.affine_image e.toAffineEquiv.toAffineMap (convex_ball 0 r)
  have hKb : Bornology.IsBounded (e '' ball (0 : Space n) r) :=
    ((isCompact_closedBall (0 : Space n) r).image e.continuous).isBounded.subset
      (image_mono ball_subset_closedBall)
  have hrep : affineMatrixMeasure (ProbabilityTheory.cond μ (closedBall 0 r)) A b =
      (potentialMeasure (affineTransformedPotential W A b hA)).restrict (e '' ball 0 r) := by
    change (ProbabilityTheory.cond μ (closedBall 0 r)).map e = _
    rw [cond_closedBall_potentialMeasure hV.continuous.measurable heq hr.ne' hm,
      map_restrict_affineMatrixEquiv, map_potentialMeasure_affineMatrixEquiv hW.continuous.measurable]
  obtain ⟨d, hpot, hset, hconst⟩ := exists_sourceData_fixed_target ha (e '' ball 0 r)
    (affineTransformedPotential W A b hA) (κ / (‖matrixAction A‖ + 1) ^ 2)
    (e.toHomeomorph.isOpenMap _ isOpen_ball) hKc hKb
    (affineTransformedPotential_contDiff hW A b hA) (by positivity)
    (affineTransformedPotential_strongConvex hκ.le hstrong A b hA) hrep
  exact ⟨d, hpot, hconst⟩

theorem eventually_whitening_norm_le_two (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) :
    ∀ᶠ k in atTop, ‖matrixAction (inverseSqrtMatrix (covarianceMatrix (ballCutoffMeasure μ R k)))‖ ≤ 2 := by
  have hlim := continuous_matrixAction.norm.continuousAt.tendsto.comp
    (hμ.tendsto_inverseSqrt_covarianceMatrix_ballCutoffMeasure hR)
  have hI : ‖matrixAction (1 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    simp only [matrixAction_one_apply, one_mul]
    exact le_rfl
  have he : ∀ᶠ k in atTop,
      ‖matrixAction (inverseSqrtMatrix (covarianceMatrix (ballCutoffMeasure μ R k)))‖ < 2 :=
    hlim.eventually (eventually_lt_nhds (lt_of_le_of_lt hI (by norm_num)))
  exact he.mono fun _ h => h.le

theorem eventually_exists_sourceData_uniform_convexity (hμ : admissibleMeasure μ)
    {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    {κ : ℝ} (hκ : 0 < κ) (hs : StrongConvexOn univ κ V)
    (heq : μ = potentialMeasure V) {R : ℝ} (hR : 0 < R)
    (hm : μ (closedBall (0 : Space n) R) ≠ 0) :
    ∀ᶠ k in atTop, ∃ d : SourceData (whitenedBallCutoffMeasure μ R k),
      κ / 9 ≤ d.targetConvexityConstant := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  filter_upwards [hμ.eventually_admissible_whitenedBallCutoffMeasure hm,
    hμ.eventually_posDef_covarianceMatrix_ballCutoffMeasure hm,
    eventually_whitening_norm_le_two hμ hm] with k hak hpos hnorm
  let A := inverseSqrtMatrix (covarianceMatrix (ballCutoffMeasure μ R k))
  let b := -matrixAction A (∫ x, x ∂ballCutoffMeasure μ R k)
  have hA : A.det ≠ 0 := inverseSqrtMatrix_det_ne_zero hpos
  obtain ⟨d, hpot, hconst⟩ := exists_sourceData_affine_condition hμ hV hκ hs heq
    (by positivity : 0 < R + k) (cutoffMass_ne_zero hm k) A b hA hak.1
  refine ⟨d, ?_⟩
  rw [hconst]
  have hden : (‖matrixAction A‖ + 1) ^ 2 ≤ 9 := by
    change ‖matrixAction A‖ ≤ 2 at hnorm
    nlinarith [norm_nonneg (matrixAction A)]
  apply (div_le_div_iff₀ (by norm_num : 0 < (9 : ℝ)) (sq_pos_of_pos (by positivity))).mpr
  exact mul_le_mul_of_nonneg_left hden hκ.le

end KLSConstantImprovement.ActualStrongTargetExhaustion405
#print axioms KLSConstantImprovement.ActualStrongTargetExhaustion405.exists_sourceData_affine_condition
#print axioms KLSConstantImprovement.ActualStrongTargetExhaustion405.eventually_whitening_norm_le_two
#print axioms KLSConstantImprovement.ActualStrongTargetExhaustion405.eventually_exists_sourceData_uniform_convexity
