import KLSConstantImprovement.ActualIntrinsicJointWeakTests405
import KLS.MollificationLocalization

/-! The concrete joint cutoffs have one global Lipschitz constant, and are
identically one on a neighborhood of each fixed joint value eventually.
Thus their finite-dimensional differentials genuinely disappear when the
joint truncation is removed. -/
noncomputable section
open Filter Metric
open scoped BigOperators Topology ContDiff
namespace KLSConstantImprovement.ActualJointBumpControl405
open KLS ActualIntrinsicJointWeakTests405 ActualSmoothScalarTruncation405
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem jointBump_scale (k : ℕ) (v : JointIndex n → ℝ) :
    jointBump k v = jointBump 0 (cutoffScale k • v) := by
  simp only [jointBump, cutoffScale, Nat.cast_zero, zero_add, inv_one, one_mul, Pi.smul_apply,
    smul_eq_mul]

theorem jointBump_uniform_lipschitz :
    ∃ L : NNReal, ∀ k, LipschitzWith L (jointBump (n := n) k) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (jointBump_compact (n := n) 0) (jointBump_contDiff 0) (by norm_num)
  refine ⟨L, fun k => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [dist_eq_norm, dist_eq_norm, jointBump_scale k v, jointBump_scale k w]
  calc
    _ ≤ (L : ℝ) * ‖cutoffScale k • v - cutoffScale k • w‖ := hL.norm_sub_le _ _
    _ = (L : ℝ) * (cutoffScale k * ‖v - w‖) := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (cutoffScale_pos k).le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (norm_nonneg _) (cutoffScale_le_one k)) L.coe_nonneg

theorem jointBump_eventually_one_nhds (v : JointIndex n → ℝ) :
    ∀ᶠ k in atTop, jointBump k =ᶠ[𝓝 v] (fun _ => (1 : ℝ)) := by
  have ht : Tendsto (fun k => cutoffScale k * ‖v‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using cutoffScale_tendsto_zero.mul_const ‖v‖
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k hk
  have he (a : JointIndex n) :
      (fun w : JointIndex n → ℝ => scalarBump (cutoffScale k * w a)) =ᶠ[𝓝 v] (fun _ => (1 : ℝ)) := by
    have ha : ‖cutoffScale k * v a‖ < 1 := by
      rw [norm_mul, Real.norm_of_nonneg (cutoffScale_pos k).le]
      exact (mul_le_mul_of_nonneg_left (norm_le_pi_norm v a) (cutoffScale_pos k).le).trans_lt hk
    have hb := scalarBump.eventuallyEq_one_of_mem_ball
      (show cutoffScale k * v a ∈ Metric.ball (0 : ℝ) scalarBump.rIn from by
        simpa only [scalarBump, Metric.mem_ball, dist_zero_right] using ha)
    exact hb.comp_tendsto ((continuous_const.mul (continuous_apply a)).continuousAt)
  have hall : ∀ᶠ w in 𝓝 v, ∀ a : JointIndex n,
      scalarBump (cutoffScale k * w a) = 1 := Filter.eventually_all.mpr he
  filter_upwards [hall] with w hw
  simp only [jointBump, hw, Finset.prod_const_one]

theorem jointBump_eventually_fderiv_zero (v : JointIndex n → ℝ) :
    ∀ᶠ k in atTop, fderiv ℝ (jointBump k) v = 0 := by
  filter_upwards [jointBump_eventually_one_nhds v] with k hk
  have hz : fderiv ℝ (fun _ : JointIndex n → ℝ => (1 : ℝ)) v = 0 :=
    congrFun (fderiv_const (𝕜 := ℝ) (1 : ℝ)) v
  exact (hk.fderiv_eq (𝕜 := ℝ)).trans hz

end KLSConstantImprovement.ActualJointBumpControl405
#print axioms KLSConstantImprovement.ActualJointBumpControl405.jointBump_uniform_lipschitz
#print axioms KLSConstantImprovement.ActualJointBumpControl405.jointBump_eventually_one_nhds
#print axioms KLSConstantImprovement.ActualJointBumpControl405.jointBump_eventually_fderiv_zero
