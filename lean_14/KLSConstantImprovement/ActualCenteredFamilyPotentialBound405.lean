import KLSConstantImprovement.ActualBoundedCanonicalSource
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.Calculus.MeanValue

/-! Common compact upper bounds on the actual centered source potentials.
Only their constructed common gradient Lipschitz bound, gradient(0)=0 and
convergence at zero enter; no compact potential bound is an extra witness. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ContDiff
namespace KLSConstantImprovement.ActualCenteredFamilyPotentialBound405
open KLS ActualBoundedCanonicalSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem anchored_C1_value_bound {f : Space n → ℝ} (hf : ContDiff ℝ 1 f)
    {L : ℝ≥0} (hL : LipschitzWith L (gradient f)) (h0 : gradient f 0 = 0)
    {R : ℝ} (hR : 0 ≤ R) {x : Space n} (hx : ‖x‖ ≤ R) :
    f x ≤ f 0 + (L : ℝ)*R^2 := by
  have hb (y : Space n) (hy : y ∈ closedBall (0 : Space n) R) :
      ‖fderiv ℝ f y‖ ≤ (L : ℝ)*R := by
    rw [← norm_gradient_eq_norm_fderiv]
    have hg : ‖gradient f y‖ ≤ (L : ℝ)*‖y‖ := by
      simpa only [h0, sub_zero] using hL.norm_sub_le y 0
    exact hg.trans (mul_le_mul_of_nonneg_left
      (by simpa only [mem_closedBall, dist_zero_right] using hy) L.coe_nonneg)
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℝ) (f := f) (s := closedBall (0 : Space n) R)
    (fun y _ => hf.differentiable (by norm_num) y) hb (convex_closedBall _ _)
    (mem_closedBall_self hR) (by simpa only [mem_closedBall, dist_zero_right] using hx)
  have hh' : f x-f 0 ≤ (L : ℝ)*R^2 := by
    have h := (le_abs_self (f x-f 0)).trans
      (by simpa only [Real.norm_eq_abs, sub_zero] using hh)
    have hm := mul_le_mul_of_nonneg_left hx (mul_nonneg L.coe_nonneg hR)
    nlinarith
  linarith

theorem actual_centered_family_compact_potential_upper
    {ρ : ℕ → Measure (Space n)} (d : ∀ k, SourceData (ρ k))
    {c : ℝ} (hc : 0 < c) (hκ : ∀ k, c ≤ (d k).targetConvexityConstant)
    (hgrad0 : ∀ k, gradient (d k).potential 0 = 0)
    {z : ℝ} (hlim0 : Tendsto (fun k => (d k).potential (0 : Space n)) atTop (𝓝 z))
    {E : Set (Space n)} (hE : Bornology.IsBounded E) :
    ∃ P : ℝ, ∀ k x, x ∈ E → (d k).potential x ≤ P := by
  obtain ⟨P0, hP0⟩ := hlim0.bddAbove_range
  obtain ⟨R, hR, hbound⟩ := hE.exists_pos_norm_le
  let L : ℝ≥0 := ⟨16/c, div_nonneg (by norm_num) hc.le⟩
  have hL (k : ℕ) : LipschitzWith L (gradient (d k).potential) := by
    apply (d k).gradient_lipschitz.weaken
    change 16/(d k).targetConvexityConstant ≤ 16/c
    exact div_le_div_of_nonneg_left (by norm_num) hc (hκ k)
  refine ⟨P0+(L : ℝ)*R^2, fun k x hx => ?_⟩
  have hh := anchored_C1_value_bound (d k).source_C1 (hL k) (hgrad0 k) hR.le (hbound x hx)
  have h0 : (d k).potential 0 ≤ P0 := hP0 (mem_range_self k)
  linarith

end KLSConstantImprovement.ActualCenteredFamilyPotentialBound405
#print axioms KLSConstantImprovement.ActualCenteredFamilyPotentialBound405.anchored_C1_value_bound
#print axioms KLSConstantImprovement.ActualCenteredFamilyPotentialBound405.actual_centered_family_compact_potential_upper
