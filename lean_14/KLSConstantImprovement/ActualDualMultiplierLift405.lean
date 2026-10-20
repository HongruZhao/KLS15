import KLSConstantImprovement.ActualNaturalDualJoint405
import KLSConstantImprovement.ActualJointMultiplierWeakTests405
import KLSConstantImprovement.ActualIntrinsicSourceCompactRange405

/-! A compact multiplier of the actual pair (u,p) lifts to a compact
multiplier of (u,H) without changing its actual value or weak derivative.
The source Hessian has a proved global entry bound; a fixed H cutoff is
therefore identically one on its actual range. Weak derivative uniqueness
identifies the two genuine chain rules and avoids differentiating H classically. -/
noncomputable section
open MeasureTheory Set Filter Matrix Metric
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualDualMultiplierLift405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405
open ActualNaturalDualJoint405 ActualIntrinsicJointWeakTests405 ActualIntrinsicSourceCompactRange405
open ActualJointMultiplierWeakTests405 ActualSmoothScalarTruncation405
open ActualSourceNaturalTargetCurvatureDomain405 ActualSourceNaturalHessian405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
variable {n : ℕ} {μ : Measure (Space n)}

def dualizeJoint (v : JointIndex n → ℝ) : DualIndex n → ℝ :=
  Sum.elim (fun i => v (.inl i)) (fun i => ∑ j : Fin n, v (.inr (i,j)) * v (.inl j))

def hessianJointCutoff (R : ℝ) (v : JointIndex n → ℝ) : ℝ :=
  ∏ ij : Fin n × Fin n, scalarBump (v (.inr ij) / R)

def liftDualMultiplier (R : ℝ) (η : (DualIndex n → ℝ) → ℝ) (v : JointIndex n → ℝ) : ℝ :=
  hessianJointCutoff R v * η (dualizeJoint v)

theorem liftDualMultiplier_contDiff {R : ℝ} {η : (DualIndex n → ℝ) → ℝ}
    (hη : ContDiff ℝ 1 η) : ContDiff ℝ 1 (liftDualMultiplier R η) := by
  have hcut : ContDiff ℝ 1 (hessianJointCutoff (n := n) R) := by
    apply contDiff_prod
    intro ij _
    exact scalarBump.contDiff.comp ((contDiff_apply ℝ ℝ (Sum.inr ij : JointIndex n)).div_const R)
  have hmap : ContDiff ℝ 1 (dualizeJoint (n := n)) := by
    apply contDiff_pi.mpr
    intro a
    cases a with
    | inl i => exact contDiff_apply ℝ ℝ (Sum.inl i : JointIndex n)
    | inr i =>
        change ContDiff ℝ 1 (fun v : JointIndex n → ℝ => ∑ j : Fin n, v (.inr (i,j)) * v (.inl j))
        fun_prop
  exact hcut.mul (hη.comp hmap)

theorem liftDualMultiplier_compact {R : ℝ} (hR : 0 < R)
    {η : (DualIndex n → ℝ) → ℝ} (hcη : HasCompactSupport η) :
    HasCompactSupport (liftDualMultiplier R η) := by
  obtain ⟨C, hC, hηC⟩ := hcη.isBounded.subset_ball_lt 0 (0 : DualIndex n → ℝ)
  let D : ℝ := max C (2 * R)
  apply (isCompact_closedBall (0 : JointIndex n → ℝ) D).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closedBall
  intro v hv
  have hparts := mul_ne_zero_iff.mp hv
  have hηv : dualizeJoint v ∈ tsupport η := subset_closure hparts.2
  have hnorm : ‖dualizeJoint v‖ < C := by
    have he := hηC hηv
    simpa only [Metric.mem_ball, dist_zero_right] using he
  have hH (ij : Fin n × Fin n) : ‖v (.inr ij)‖ ≤ 2 * R := by
    have hprod : (∏ ij : Fin n × Fin n, scalarBump (v (.inr ij) / R)) ≠ 0 := hparts.1
    have hneq := (Finset.prod_ne_zero_iff.mp hprod) ij (Finset.mem_univ ij)
    have hx : ‖v (.inr ij) / R‖ < 2 := by
      by_contra hh
      apply hneq
      apply scalarBump.zero_of_le_dist
      simpa only [scalarBump, dist_zero_right] using le_of_not_gt hh
    rw [norm_div, Real.norm_of_nonneg hR.le] at hx
    exact ((div_lt_iff₀ hR).mp hx).le
  change ‖v - 0‖ ≤ D
  rw [sub_zero]
  apply (pi_norm_le_iff_of_nonneg (le_trans hC.le (le_max_left C (2 * R)))).mpr
  intro a
  cases a with
  | inl i =>
      have hi : ‖v (.inl i)‖ ≤ ‖dualizeJoint v‖ := norm_le_pi_norm (dualizeJoint v) (.inl i)
      exact (hi.trans hnorm.le).trans (le_max_left _ _)
  | inr ij => exact (hH ij).trans (le_max_right _ _)

theorem actual_hessianJointCutoff_eq_one (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (x : Space n) :
    hessianJointCutoff (16 / d.targetConvexityConstant + 1)
      (fun a => sourceJointValue d (naturalCanonicalFlux d g) a x) = 1 := by
  have hκ := d.target_convexity_pos
  have hR : 0 < 16 / d.targetConvexityConstant + 1 := by positivity
  unfold hessianJointCutoff
  apply Finset.prod_eq_one
  intro ij _
  apply scalarBump.one_of_mem_closedBall
  change ‖coordinateHessian d.potential x ij.1 ij.2 / (16 / d.targetConvexityConstant + 1) - 0‖ ≤ 1
  rw [sub_zero, norm_div, Real.norm_of_nonneg hR.le]
  apply (div_le_one hR).mpr
  have hb := coordinateHessian_entry_bound_of_gradient_lipschitz d.gradient_lipschitz x ij.1 ij.2
  change |coordinateHessian d.potential x ij.1 ij.2| ≤ 16 / d.targetConvexityConstant at hb
  simpa only [Real.norm_eq_abs] using hb.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))

theorem actual_dual_lift_value_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (η : (DualIndex n → ℝ) → ℝ) :
    jointSource d (naturalCanonicalFlux d g) (liftDualMultiplier (16 / d.targetConvexityConstant + 1) η)
      =ᵐ[potentialMeasure d.potential] dualSource d g η := by
  filter_upwards [hessian_mul_naturalCanonicalFlux_ae d g] with x hx
  have he : dualizeJoint (fun a => sourceJointValue d (naturalCanonicalFlux d g) a x) =
      (fun a => dualValue d g a x) := by
    funext a
    cases a with
    | inl i => rfl
    | inr i =>
        exact congrFun hx i
  change hessianJointCutoff _ _ * η _ = η _
  rw [actual_hessianJointCutoff_eq_one, one_mul, he]

theorem exists_actual_dual_multiplier_lift (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i b E, IsCompact E → MemLp (Du i b) 2 (volume.restrict E))
    (hw : ∀ i b, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i b) b)
    (hC : ∀ i b E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i b) 2 (volume.restrict E))
    {η : (DualIndex n → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) :
    ∃ ζ : (JointIndex n → ℝ) → ℝ, ContDiff ℝ 1 ζ ∧ HasCompactSupport ζ ∧
      (jointSource d (naturalCanonicalFlux d g) ζ =ᵐ[potentialMeasure d.potential] dualSource d g η) ∧
      ∀ a : Fin n, jointSourceDerivative d (naturalCanonicalFlux d g) Du ζ a
        =ᵐ[potentialMeasure d.potential] dualSourceDerivative d g Du η a := by
  let R : ℝ := 16 / d.targetConvexityConstant + 1
  have hR : 0 < R := by have hκ := d.target_convexity_pos; dsimp only [R]; positivity
  let ζ := liftDualMultiplier R η
  have hζ : ContDiff ℝ 1 ζ := liftDualMultiplier_contDiff hη
  have hcζ : HasCompactSupport ζ := liftDualMultiplier_compact hR hcη
  have hv := actual_dual_lift_value_ae d g η
  obtain ⟨_hB, _hvl, hDl, hWl⟩ := actual_compact_joint_domains d hu hDu hw hζ hcζ
  obtain ⟨_hB', _hvr, hDr, hWr⟩ := actual_dual_compact_chain d g Du hu hDu hw hC hη hcη
  refine ⟨ζ, hζ, hcζ, hv, ?_⟩
  intro a
  have hvol : (volume : Measure (Space n)) ≪ potentialMeasure d.potential :=
    volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous
  have hval := hvol.ae_eq hv
  have hWL := (hWl a).congr_ae hval EventuallyEq.rfl
  have he := hWL.unique (hWr a)
    (locallyIntegrable_of_memLp_two_on_compacts (hDl a))
    (locallyIntegrable_of_memLp_two_on_compacts (hDr a))
  exact he.filter_mono (withDensity_absolutelyContinuous _ _).ae_le

end KLSConstantImprovement.ActualDualMultiplierLift405
#print axioms KLSConstantImprovement.ActualDualMultiplierLift405.liftDualMultiplier_contDiff
#print axioms KLSConstantImprovement.ActualDualMultiplierLift405.liftDualMultiplier_compact
#print axioms KLSConstantImprovement.ActualDualMultiplierLift405.actual_dual_lift_value_ae
#print axioms KLSConstantImprovement.ActualDualMultiplierLift405.exists_actual_dual_multiplier_lift
