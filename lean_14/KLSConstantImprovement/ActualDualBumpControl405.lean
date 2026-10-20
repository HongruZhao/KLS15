import KLSConstantImprovement.ActualNaturalDualJoint405
import KLS.MollificationLocalization

/-! One common compact cutoff in the actual pair (u,p). It has a uniform
Lipschitz bound and becomes identically one near every fixed pair, with
zero differential there. -/
noncomputable section
open Filter Metric
open scoped BigOperators Topology ContDiff
namespace KLSConstantImprovement.ActualDualBumpControl405
open KLS ActualNaturalDualJoint405 ActualSmoothScalarTruncation405
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem dualBump_contDiff (k : ℕ) : ContDiff ℝ 1 (dualBump (n := n) k) := by
  unfold dualBump
  apply contDiff_prod
  intro a _
  exact scalarBump.contDiff.comp (contDiff_const.mul (contDiff_apply ℝ ℝ a))

theorem dualBump_compact (k : ℕ) : HasCompactSupport (dualBump (n := n) k) := by
  apply (isCompact_closedBall (0 : DualIndex n → ℝ) (2 / cutoffScale k)).of_isClosed_subset
    (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closedBall
  intro v hv
  change ‖v - 0‖ ≤ 2 / cutoffScale k
  rw [sub_zero]
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (by norm_num) (cutoffScale_pos k).le : 0 ≤ 2 / cutoffScale k)).mpr
  intro a
  have hprod : dualBump k v ≠ 0 := hv
  change (∏ a : DualIndex n, scalarBump (cutoffScale k * v a)) ≠ 0 at hprod
  have ha : scalarBump (cutoffScale k * v a) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) a (Finset.mem_univ a)
  have hn : ‖cutoffScale k * v a‖ < 2 := by
    by_contra h
    apply ha
    apply scalarBump.zero_of_le_dist
    simpa only [scalarBump, dist_zero_right] using le_of_not_gt h
  rw [norm_mul, Real.norm_of_nonneg (cutoffScale_pos k).le] at hn
  exact (le_div_iff₀ (cutoffScale_pos k)).mpr (by nlinarith)

theorem dualBump_scale (k : ℕ) (v : DualIndex n → ℝ) :
    dualBump k v = dualBump 0 (cutoffScale k • v) := by
  simp only [dualBump, cutoffScale, Nat.cast_zero, zero_add, inv_one, one_mul, Pi.smul_apply,
    smul_eq_mul]

theorem dualBump_uniform_lipschitz :
    ∃ L : NNReal, ∀ k, LipschitzWith L (dualBump (n := n) k) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (dualBump_compact (n := n) 0) (dualBump_contDiff 0) (by norm_num)
  refine ⟨L, fun k => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [dist_eq_norm, dist_eq_norm, dualBump_scale k v, dualBump_scale k w]
  calc
    _ ≤ (L : ℝ) * ‖cutoffScale k • v - cutoffScale k • w‖ := hL.norm_sub_le _ _
    _ = (L : ℝ) * (cutoffScale k * ‖v - w‖) := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (cutoffScale_pos k).le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (norm_nonneg _) (cutoffScale_le_one k)) L.coe_nonneg

theorem dualBump_eventually_one_nhds (v : DualIndex n → ℝ) :
    ∀ᶠ k in atTop, dualBump k =ᶠ[𝓝 v] (fun _ => (1 : ℝ)) := by
  have ht : Tendsto (fun k => cutoffScale k * ‖v‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using cutoffScale_tendsto_zero.mul_const ‖v‖
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k hk
  have he (a : DualIndex n) :
      (fun w : DualIndex n → ℝ => scalarBump (cutoffScale k * w a)) =ᶠ[𝓝 v] (fun _ => (1 : ℝ)) := by
    have ha : ‖cutoffScale k * v a‖ < 1 := by
      rw [norm_mul, Real.norm_of_nonneg (cutoffScale_pos k).le]
      exact (mul_le_mul_of_nonneg_left (norm_le_pi_norm v a) (cutoffScale_pos k).le).trans_lt hk
    have hb := scalarBump.eventuallyEq_one_of_mem_ball
      (show cutoffScale k * v a ∈ Metric.ball (0 : ℝ) scalarBump.rIn from by
        simpa only [scalarBump, Metric.mem_ball, dist_zero_right] using ha)
    exact hb.comp_tendsto ((continuous_const.mul (continuous_apply a)).continuousAt)
  have hall : ∀ᶠ w in 𝓝 v, ∀ a : DualIndex n,
      scalarBump (cutoffScale k * w a) = 1 := Filter.eventually_all.mpr he
  filter_upwards [hall] with w hw
  simp only [dualBump, hw, Finset.prod_const_one]

theorem dualBump_eventually_fderiv_zero (v : DualIndex n → ℝ) :
    ∀ᶠ k in atTop, fderiv ℝ (dualBump k) v = 0 := by
  filter_upwards [dualBump_eventually_one_nhds v] with k hk
  have hz : fderiv ℝ (fun _ : DualIndex n → ℝ => (1 : ℝ)) v = 0 :=
    congrFun (fderiv_const (𝕜 := ℝ) (1 : ℝ)) v
  exact (hk.fderiv_eq (𝕜 := ℝ)).trans hz

end KLSConstantImprovement.ActualDualBumpControl405
#print axioms KLSConstantImprovement.ActualDualBumpControl405.dualBump_compact
#print axioms KLSConstantImprovement.ActualDualBumpControl405.dualBump_uniform_lipschitz
#print axioms KLSConstantImprovement.ActualDualBumpControl405.dualBump_eventually_one_nhds
#print axioms KLSConstantImprovement.ActualDualBumpControl405.dualBump_eventually_fderiv_zero
