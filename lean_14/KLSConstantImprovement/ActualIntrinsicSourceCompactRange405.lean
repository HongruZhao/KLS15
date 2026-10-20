import KLSConstantImprovement.ActualIntrinsicJointWeakTests405

/-! The positive compact range used by the intrinsic joint tests is paid by
the actual weak moment-map ellipticity theorem. The constants do not bound
u and no Hessian continuity is assumed. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff ENNReal NNReal
namespace KLSConstantImprovement.ActualIntrinsicSourceCompactRange405
open KLS ActualBoundedCanonicalSource ActualIntrinsicJointWeakTests405
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem sourceJointValue_local_L2 (d : SourceData μ)
    {u : Fin n → Space n → ℝ}
    (hu : ∀ i E, IsCompact E → MemLp (u i) 2 (volume.restrict E))
    (a : JointIndex n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (sourceJointValue d u a) 2 (volume.restrict E) := by
  cases a with
  | inl i => exact hu i E hE
  | inr ij =>
      exact KLS.MemLp.restrict_volume_of_potentialMeasure
        (d.hessian_entry_memLp ij.1 ij.2 2) d.source_C1.continuous hE

theorem sourceJointDerivative_local_L2 (d : SourceData μ)
    {Du : Fin n → Fin n → Space n → ℝ}
    (hDu : ∀ i b E, IsCompact E → MemLp (Du i b) 2 (volume.restrict E))
    (a : JointIndex n) (b : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (sourceJointDerivative d Du a b) 2 (volume.restrict E) := by
  cases a with
  | inl i => exact hDu i b E hE
  | inr ij => exact d.third_local_L2 b ij.1 ij.2 E hE

theorem actual_source_joint_metric_range (d : SourceData μ)
    (E : Set (Space n)) (hE : IsCompact E) :
    ∃ c G : ℝ, 0 < c ∧ 0 ≤ G ∧
      (∀ᵐ x ∂volume.restrict E, ∀ u : Fin n → ℝ,
        c * (∑ a : Fin n, u a ^ 2) ≤
          jointMass (Sum.elim u (fun ij => coordinateHessian d.potential x ij.1 ij.2))) ∧
      ∀ x : Space n, ∀ i j, |coordinateHessian d.potential x i j| ≤ G := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨B, c, Λ, _hB, hc, _hΛ, hell⟩ :=
    weak_moment_ae_hessian_uniformly_elliptic_on_compact d.source_lipschitz d.source_convex
      (d.target_smooth.of_le (by simp)) d.target_convex_potential d.target_convexity_pos
      d.target_strong d.target_closed d.target_convex
      (d.pushforward.trans d.target_representation) hE
  refine ⟨c, 16 / d.targetConvexityConstant, hc, by have hk := d.target_convexity_pos; positivity, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae hell, ae_restrict_mem hE.measurableSet] with x hx hxE
    intro u
    have hv := ((hx hxE).2.2.2.2 (WithLp.toLp 2 u)).1
    have hn : ‖(WithLp.toLp 2 u : Space n)‖ ^ 2 = ∑ a : Fin n, u a ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.toLp_apply, pow_two]
    have hq : inner ℝ (WithLp.toLp 2 u : Space n)
        (matrixAction (coordinateHessian d.potential x) (WithLp.toLp 2 u)) =
        jointMass (Sum.elim u (fun ij => coordinateHessian d.potential x ij.1 ij.2)) := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, matrixAction_apply,
        PiLp.toLp_apply, jointMass, Sum.elim_inl, Sum.elim_inr, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rwa [hn, hq] at hv
  · intro x i j
    have hb := coordinateHessian_entry_bound_of_gradient_lipschitz d.gradient_lipschitz x i j
    change |coordinateHessian d.potential x i j| ≤ 16 / d.targetConvexityConstant at hb
    exact hb

end KLSConstantImprovement.ActualIntrinsicSourceCompactRange405
#print axioms KLSConstantImprovement.ActualIntrinsicSourceCompactRange405.sourceJointValue_local_L2
#print axioms KLSConstantImprovement.ActualIntrinsicSourceCompactRange405.sourceJointDerivative_local_L2
#print axioms KLSConstantImprovement.ActualIntrinsicSourceCompactRange405.actual_source_joint_metric_range
