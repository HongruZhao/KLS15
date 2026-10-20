import KLSConstantImprovement.ActualSourceCompactPositiveBochner405
import KLS.ConvexHessian

/-!
The two actual canonical Bochner terms are nonnegative separately, so the
compact identity pays each one's integrability and square-generator cap.
This is still a compact scalar statement; the natural variational domain
passage must be proved independently.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix Filter
open scoped BigOperators ContDiff
namespace KLSConstantImprovement.ActualSourceCompactBochnerBounds405
open KLS ActualBoundedCanonicalSource ActualSourceCanonicalConnectionBalance405
open ActualSourceCompactPositiveBochner405 ActualSourceCompactOperator405
variable {n : ℕ} {μ : Measure (Space n)}

theorem actualCanonicalSecondDensity_nonneg_ae (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ actualCanonicalSecondDensity d ψ x := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source] with x hx
  let J := (coordinateHessian d.potential x)⁻¹
  let C := coordinateHessian ψ x
  have hJ : J.PosSemidef := hx.1.inv.posSemidef
  have hC : C.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr (coordinateHessian_symmetric hψ x)
  have hCJC : (C * J * C).PosSemidef := by
    simpa only [hC.eq] using hJ.conjTranspose_mul_mul_same C
  have ht := trace_mul_nonneg_of_posSemidef hJ hCJC
  change 0 ≤ (J * C * J * C).trace
  simpa only [Matrix.mul_assoc] using ht

theorem actualCanonicalTargetDensity_nonneg (d : SourceData μ)
    (ψ : Space n → ℝ) (x : Space n) : 0 ≤ actualCanonicalTargetDensity d ψ x := by
  have hP := coordinateHessian_posSemidef_of_convex
    (d.target_smooth.of_le (by simp) : ContDiff ℝ 2 d.targetPotential)
    d.target_convex_potential (gradient d.potential x)
  simpa only [actualCanonicalTargetDensity, star_trivial] using
    hP.dotProduct_mulVec_nonneg (fun i => coordinateDerivative ψ i x)

private theorem actualCanonicalTargetDensity_continuous (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) : Continuous (actualCanonicalTargetDensity d ψ) := by
  have hp (i : Fin n) : Continuous (coordinateDerivative ψ i) :=
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous
  have hP (i j : Fin n) : Continuous (fun x => coordinateHessian d.targetPotential
      (gradient d.potential x) i j) :=
    (contDiff_coordinateHessian (d.target_smooth.of_le (by simp) :
        ContDiff ℝ 2 d.targetPotential) (m := 0) (by norm_num) i j).continuous.comp
      d.gradient_lipschitz.continuous
  unfold actualCanonicalTargetDensity
  simp only [dotProduct, Matrix.mulVec]
  apply continuous_finsetSum
  intro i _
  exact (hp i).mul (continuous_finsetSum Finset.univ fun j _ => (hP i j).mul (hp j))

/-- The actual inverse-metric Hessian and target-curvature terms both have
their global compact-domain bounds paid by the same actual A psi. -/
theorem compact_actual_canonical_bochner_bounds (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    Integrable (actualCanonicalSecondDensity d ψ) (potentialMeasure d.potential) ∧
      Integrable (actualCanonicalTargetDensity d ψ) (potentialMeasure d.potential) ∧
      (∫ x, actualCanonicalSecondDensity d ψ x ∂potentialMeasure d.potential) ≤
        (∫ x, actualSourceOperator d ψ x ^ 2 ∂potentialMeasure d.potential) ∧
      (∫ x, actualCanonicalTargetDensity d ψ x ∂potentialMeasure d.potential) ≤
        ∫ x, actualSourceOperator d ψ x ^ 2 ∂potentialMeasure d.potential := by
  obtain ⟨hwhole, heq⟩ := compact_actual_positive_canonical_bochner d hψ hc
  have hsecond0 := actualCanonicalSecondDensity_nonneg_ae d (hψ.of_le (by norm_num))
  have htarget0 : ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ actualCanonicalTargetDensity d ψ x :=
    Eventually.of_forall (actualCanonicalTargetDensity_nonneg d ψ)
  have htarget : Integrable (actualCanonicalTargetDensity d ψ) (potentialMeasure d.potential) := by
    apply hwhole.mono_nonneg
      (actualCanonicalTargetDensity_continuous d (hψ.of_le (by norm_num))).aestronglyMeasurable htarget0
    filter_upwards [hsecond0] with x hx
    exact le_add_of_nonneg_left hx
  have hsecond : Integrable (actualCanonicalSecondDensity d ψ) (potentialMeasure d.potential) := by
    have hh := hwhole.sub htarget
    change Integrable (fun x => actualCanonicalSecondDensity d ψ x + actualCanonicalTargetDensity d ψ x -
      actualCanonicalTargetDensity d ψ x) (potentialMeasure d.potential) at hh
    simpa only [add_sub_cancel_right] using hh
  refine ⟨hsecond, htarget, ?_, ?_⟩
  · rw [heq]
    apply integral_mono_ae hsecond hwhole
    filter_upwards [htarget0] with x hx
    exact le_add_of_nonneg_right hx
  · rw [heq]
    apply integral_mono_ae htarget hwhole
    filter_upwards [hsecond0] with x hx
    exact le_add_of_nonneg_left hx

end KLSConstantImprovement.ActualSourceCompactBochnerBounds405

#print axioms KLSConstantImprovement.ActualSourceCompactBochnerBounds405.actualCanonicalSecondDensity_nonneg_ae
#print axioms KLSConstantImprovement.ActualSourceCompactBochnerBounds405.actualCanonicalTargetDensity_nonneg
#print axioms KLSConstantImprovement.ActualSourceCompactBochnerBounds405.compact_actual_canonical_bochner_bounds
