import KLSConstantImprovement.ActualIntrinsicDerivativeBounds405
import KLSConstantImprovement.ActualJointBumpControl405

/-! The concrete compact joint test has uniformly bounded partials on each
positive metric range. Its value and partials eventually agree with the
untruncated rational test at every fixed joint value. -/
noncomputable section
open Filter
open scoped BigOperators Topology ContDiff
namespace KLSConstantImprovement.ActualIntrinsicJointCutoffPassage405
open KLS ActualIntrinsicJointWeakTests405 ActualIntrinsicJointCalculus405
open ActualIntrinsicDerivativeBounds405 ActualJointBumpControl405 ActualVectorDifferential405
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem intrinsicJointMatrixEntry_partial {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε)
    (k : ℕ) (i j : Fin n) (b : JointIndex n) (v : JointIndex n → ℝ) :
    vectorPartial (intrinsicJointMatrixEntry δ ε k i j) b v =
      jointBump k v * vectorPartial (intrinsicJointRawEntry δ ε i j) b v +
        intrinsicJointRawEntry δ ε i j v * vectorPartial (jointBump k) b v := by
  change fderiv ℝ (fun w => jointBump k w * intrinsicJointRawEntry δ ε i j w) v
    (Pi.single b 1) = _
  rw [fderiv_fun_mul ((jointBump_contDiff k).differentiable one_ne_zero v)
    ((intrinsicJointRawEntry_contDiff hδ hε i j).differentiable one_ne_zero v)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    vectorPartial]

theorem intrinsicJointMatrixEntry_uniform_partials :
    ∃ L : NNReal, ∀ {δ ε c G : ℝ}, 0 < δ → 0 < ε → 0 < c → 0 ≤ G →
      ∀ (k : ℕ) (i j : Fin n) (v : JointIndex n → ℝ),
      c * (∑ a : Fin n, v (.inl a) ^ 2) ≤ jointMass v →
      (∀ a b, |v (.inr (a,b))| ≤ G) → ∀ b : JointIndex n,
      ‖vectorPartial (intrinsicJointMatrixEntry δ ε k i j) b v‖ ≤
        (L : ℝ) * (δ * c)⁻¹ +
          (2 * (1 + (δ * c)⁻¹) + δ * (δ * c)⁻¹ * jointDerivativeRatioBound n G (δ * c)) := by
  obtain ⟨L, hL⟩ := jointBump_uniform_lipschitz (n := n)
  refine ⟨L, ?_⟩
  intro δ ε c G hδ hε hc hG k i j v hM hH b
  have hb := jointBump_nonnegative_le_one k v
  have hr := intrinsicJointRawEntry_bound (ε := ε) hδ hc i j v hM
  have hd := intrinsicJointRawEntry_uniform_partial_bound hδ hε hc hG i j v hM hH b
  have hbd := vectorPartial_bound (hL k) b v
  rw [intrinsicJointMatrixEntry_partial hδ.le hε]
  calc
    _ ≤ ‖jointBump k v * vectorPartial (intrinsicJointRawEntry δ ε i j) b v‖ +
        ‖intrinsicJointRawEntry δ ε i j v * vectorPartial (jointBump k) b v‖ := norm_add_le _ _
    _ = |jointBump k v| * ‖vectorPartial (intrinsicJointRawEntry δ ε i j) b v‖ +
        |intrinsicJointRawEntry δ ε i j v| * ‖vectorPartial (jointBump k) b v‖ := by
      rw [norm_mul, norm_mul, Real.norm_eq_abs (jointBump k v),
        Real.norm_eq_abs (intrinsicJointRawEntry δ ε i j v)]
    _ ≤ 1 * (2 * (1 + (δ * c)⁻¹) + δ * (δ * c)⁻¹ * jointDerivativeRatioBound n G (δ * c)) +
        (δ * c)⁻¹ * (L : ℝ) := add_le_add
      (mul_le_mul (by simpa only [abs_of_nonneg hb.1] using hb.2) hd
        (norm_nonneg _) (by norm_num))
      (mul_le_mul hr hbd (norm_nonneg _) (by positivity))
    _ = _ := by ring

theorem intrinsicJointMatrixEntry_eventually_raw (δ ε : ℝ) (i j : Fin n)
    (v : JointIndex n → ℝ) :
    ∀ᶠ k in atTop, intrinsicJointMatrixEntry δ ε k i j v = intrinsicJointRawEntry δ ε i j v := by
  filter_upwards [jointBump_eventually_one_nhds v] with k hk
  change jointBump k v * intrinsicJointRawEntry δ ε i j v = _
  rw [hk.eq_of_nhds, one_mul]

theorem intrinsicJointMatrixEntry_eventually_raw_partial {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 < ε) (i j : Fin n) (b : JointIndex n) (v : JointIndex n → ℝ) :
    ∀ᶠ k in atTop, vectorPartial (intrinsicJointMatrixEntry δ ε k i j) b v =
      vectorPartial (intrinsicJointRawEntry δ ε i j) b v := by
  filter_upwards [jointBump_eventually_one_nhds v, jointBump_eventually_fderiv_zero v] with k hk hd
  rw [intrinsicJointMatrixEntry_partial hδ hε, hk.eq_of_nhds]
  have hz : vectorPartial (jointBump k) b v = 0 := by
    unfold vectorPartial
    rw [hd]
    rfl
  rw [hz, mul_zero, one_mul, add_zero]

end KLSConstantImprovement.ActualIntrinsicJointCutoffPassage405
#print axioms KLSConstantImprovement.ActualIntrinsicJointCutoffPassage405.intrinsicJointMatrixEntry_partial
#print axioms KLSConstantImprovement.ActualIntrinsicJointCutoffPassage405.intrinsicJointMatrixEntry_uniform_partials
#print axioms KLSConstantImprovement.ActualIntrinsicJointCutoffPassage405.intrinsicJointMatrixEntry_eventually_raw
#print axioms KLSConstantImprovement.ActualIntrinsicJointCutoffPassage405.intrinsicJointMatrixEntry_eventually_raw_partial
