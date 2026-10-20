import KLSConstantImprovement.ActualSoftTargetWhitening405
import KLSConstantImprovement.ActualFixedTargetSource405
import KLSConstantImprovement.ActualCenteredSourceData405

/-! Genuine canonical sources for the actual soft-barrier growing-ball
probability laws after covariance whitening.  The affine potential, target
set and uniform positive convexity modulus remain explicit. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix Metric
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualSoftTargetSource405
open KLS ActualBoundedCanonicalSource ActualFixedTargetSource405 ActualCenteredSourceData405
open ActualSoftTargetIntegrals405 ActualStrongPotentialMoments405 ActualSoftTargetNormalization405
open ActualSoftTargetWhitening405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_softTarget_source_affine
    {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    {κ : ℝ} (hκ : 0 < κ) (hs : StrongConvexOn univ κ V)
    {K : Set (Space n)} (hK : IsClosed K) (hne : K.Nonempty) (hc : Convex ℝ K)
    (j : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (hA : A.det ≠ 0)
    (ha : admissibleMeasure (affineMatrixMeasure (softTargetMeasure V K j) A b)) :
    ∃ d : SourceData (affineMatrixMeasure (softTargetMeasure V K j) A b),
      d.targetPotential = affineTransformedPotential (normalizedSoftTargetPotential V K j) A b hA ∧
      d.targetSet = closure ((affineMatrixEquiv A b hA) '' ball (0 : Space n) ((j : ℝ)+1)) ∧
      d.targetConvexityConstant = κ / (‖matrixAction A‖+1)^2 := by
  let e := affineMatrixEquiv A b hA
  let W := normalizedSoftTargetPotential V K j
  obtain ⟨hW, hWs⟩ := normalizedSoftTargetPotential_regular hV hs hK hne hc j
  have hrepr : affineMatrixMeasure (softTargetMeasure V K j) A b =
      (potentialMeasure (affineTransformedPotential W A b hA)).restrict
        (e '' ball 0 ((j : ℝ)+1)) := by
    change ((potentialMeasure W).restrict (ball 0 ((j : ℝ)+1))).map e = _
    rw [map_restrict_affineMatrixEquiv,
      map_potentialMeasure_affineMatrixEquiv hW.continuous.measurable]
  have hKb : Bornology.IsBounded (e '' ball (0 : Space n) ((j : ℝ)+1)) :=
    ((isCompact_closedBall (0 : Space n) ((j : ℝ)+1)).image e.continuous).isBounded.subset
      (image_mono ball_subset_closedBall)
  exact exists_sourceData_fixed_target ha (e '' ball 0 ((j : ℝ)+1))
    (affineTransformedPotential W A b hA) (κ / (‖matrixAction A‖+1)^2)
    (e.toHomeomorph.isOpenMap _ isOpen_ball)
    (Convex.affine_image e.toAffineEquiv.toAffineMap (convex_ball 0 ((j : ℝ)+1))) hKb
    (affineTransformedPotential_contDiff hW A b hA) (by positivity)
    (affineTransformedPotential_strongConvex hκ.le hWs A b hA) hrepr

theorem eventually_softTarget_sources_uniform_convexity (hμ : admissibleMeasure μ)
    {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    {κ : ℝ} (hκ : 0 < κ) (hs : StrongConvexOn univ κ V)
    {K : Set (Space n)} (hK : IsClosed K) (hne : K.Nonempty) (hc : Convex ℝ K)
    (heq : μ = (potentialMeasure V).restrict K) :
    ∀ᶠ j in atTop,
      let ν := softTargetMeasure V K j
      let A := inverseSqrtMatrix (covarianceMatrix ν)
      let b := -matrixAction A (∫ x, x ∂ν)
      ∃ (hA : A.det ≠ 0) (d : SourceData (whitenedMeasure ν)),
        d.targetPotential = affineTransformedPotential (normalizedSoftTargetPotential V K j) A b hA ∧
        d.targetSet = closure ((affineMatrixEquiv A b hA) '' ball (0 : Space n) ((j : ℝ)+1)) ∧
        d.targetConvexityConstant = κ / (‖matrixAction A‖+1)^2 ∧
        κ/9 ≤ d.targetConvexityConstant := by
  filter_upwards [softTarget_whitening_eventual hμ hV hκ hs hK hne hc heq] with j hj
  dsimp only
  let ν := softTargetMeasure V K j
  let A := inverseSqrtMatrix (covarianceMatrix ν)
  let b := -matrixAction A (∫ x, x ∂ν)
  have hA : A.det ≠ 0 := inverseSqrtMatrix_det_ne_zero hj.2.1
  obtain ⟨d, hp, hset, hconst⟩ := exists_softTarget_source_affine hV hκ hs hK hne hc j A b hA hj.1
  refine ⟨hA, d, hp, hset, hconst, ?_⟩
  rw [hconst]
  have hden : (‖matrixAction A‖+1)^2 ≤ 9 := by
    have hnorm : ‖matrixAction A‖ ≤ 2 := hj.2.2
    nlinarith [norm_nonneg (matrixAction A)]
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 9) (sq_pos_of_pos (by positivity))).mpr
  exact mul_le_mul_of_nonneg_left hden hκ.le

end KLSConstantImprovement.ActualSoftTargetSource405
#print axioms KLSConstantImprovement.ActualSoftTargetSource405.exists_softTarget_source_affine
#print axioms KLSConstantImprovement.ActualSoftTargetSource405.eventually_softTarget_sources_uniform_convexity
