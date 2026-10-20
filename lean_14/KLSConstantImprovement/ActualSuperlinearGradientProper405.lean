import KLSConstantImprovement.ActualDualCapCoercivity405
import KLS.WeightedCaccioppoli
import KLS.ConvexSubgradient

/-! A genuine geometric consequence of the target-cap cones. For a C1 convex
limit potential, the gradient has compact inverse images of bounded closed
sets. This proves the compact-support part of the proposed full-support
pullback cutoffs, not their metric energy or any natural-domain estimate. -/
noncomputable section
open MeasureTheory Filter Set Metric InnerProductSpace
open scoped Topology BigOperators
namespace KLSConstantImprovement.ActualSuperlinearGradientProper405
open KLS ActualDualCapCoercivity405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem cones_of_eventual_cones {f : ℕ → Space n → ℝ} {φ : Space n → ℝ}
    (hcones : ∀ a : ℝ, 0 ≤ a → ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ k in atTop, ∀ x, a * ‖x‖ - B ≤ f k x)
    (hlim : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (φ x))) :
    ∀ a : ℝ, 0 ≤ a → ∃ B : ℝ, 0 ≤ B ∧ ∀ x, a * ‖x‖ - B ≤ φ x := by
  intro a ha
  obtain ⟨B, hB, hc⟩ := hcones a ha
  refine ⟨B, hB, fun x => ge_of_tendsto (hlim x) ?_⟩
  exact hc.mono fun k hk => hk x

theorem gradient_preimage_closedBall_compact {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : ConvexOn ℝ univ φ)
    (hcones : ∀ a : ℝ, 0 ≤ a → ∃ B : ℝ, 0 ≤ B ∧ ∀ x, a * ‖x‖ - B ≤ φ x)
    {R : ℝ} (hR : 0 ≤ R) :
    IsCompact ((gradient φ) ⁻¹' closedBall (0 : Space n) R) := by
  obtain ⟨B, hB, hcone⟩ := hcones (R + 1) (by linarith)
  have hg := continuous_gradient_of_contDiff hφ
  apply (isCompact_closedBall (0 : Space n) (B + |φ 0| + 1)).of_isClosed_subset
    (isClosed_closedBall.preimage hg)
  intro x hx
  have hxR : ‖gradient φ x‖ ≤ R := by simpa only [mem_preimage, mem_closedBall, dist_zero_right] using hx
  have hs := gradient_mem_convexSubgradient hc (hφ.differentiable (by norm_num) x) 0
  have hi := real_inner_le_norm (gradient φ x) x
  have hm := mul_le_mul_of_nonneg_right hxR (norm_nonneg x)
  simp only [zero_sub, inner_neg_right] at hs
  have hn := hcone x
  have hb : ‖x‖ ≤ B + |φ 0| + 1 := by
    nlinarith [le_abs_self (φ 0)]
  simpa only [mem_closedBall, dist_zero_right] using hb

theorem gradient_preimage_compact {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : ConvexOn ℝ univ φ)
    (hcones : ∀ a : ℝ, 0 ≤ a → ∃ B : ℝ, 0 ≤ B ∧ ∀ x, a * ‖x‖ - B ≤ φ x)
    {K : Set (Space n)} (hK : IsCompact K) : IsCompact ((gradient φ) ⁻¹' K) := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  apply (gradient_preimage_closedBall_compact hφ hc hcones hR.le).of_isClosed_subset
    (hK.isClosed.preimage (continuous_gradient_of_contDiff hφ))
  intro x hx
  simpa only [mem_preimage, mem_closedBall, dist_zero_right] using hbound _ hx

end KLSConstantImprovement.ActualSuperlinearGradientProper405
#print axioms KLSConstantImprovement.ActualSuperlinearGradientProper405.cones_of_eventual_cones
#print axioms KLSConstantImprovement.ActualSuperlinearGradientProper405.gradient_preimage_closedBall_compact
#print axioms KLSConstantImprovement.ActualSuperlinearGradientProper405.gradient_preimage_compact
