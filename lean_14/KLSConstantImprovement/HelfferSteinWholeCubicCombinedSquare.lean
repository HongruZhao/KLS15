import KLSConstantImprovement.SourceThirdAdjointResponse

/-! The ordinary-source HS rows represent the entire SAME cubic datum by
6 Hhalf Sym(U) Hhalf. Actual row construction, source IBP, graph/core and
target Bochner identification remain explicit analytic inputs. The norm
budget28N/3 is OPEN; no universal numerical or Poincare bound is proved. -/
noncomputable section
namespace KLSConstantImprovement.HelfferSteinWholeCubicCombinedSquare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem main_response_cancel_inside_same_field (a f : E) (u z : F)
    (r : E → F)
    (hmain : ∀ v, inner ℝ a v = inner ℝ z (r v))
    (hresponse : ∀ v, inner ℝ f v = inner ℝ ((2:ℝ) • u-z) (r v)) :
    ∀ v, inner ℝ (a+f) v = 2*inner ℝ u (r v) := by
  intro v
  rw [inner_add_left, hmain v, hresponse v, inner_sub_left, real_inner_smul_left]
  ring

theorem whole_cubic_objective (u R : F) {functional graph curvature : ℝ}
    (hpair : functional = 6*inner ℝ R u)
    (hbochner : graph = ‖R‖^2+curvature) :
    2*functional-graph =
      36*‖u‖^2-‖R-(6:ℝ) • u‖^2-curvature := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul]
  norm_num
  nlinarith

theorem whole_cubic_norm_coercivity (P : E) (u : F) (r : E → F)
    (hcontract : ∀ v, ‖r v‖ ≤ ‖v‖)
    (hpair : ∀ v, inner ℝ P v = 6*inner ℝ u (r v)) :
    ‖P‖^2 ≤ 36*‖u‖^2 := by
  have h := SourceThirdAdjointResponse.third_adjoint_norm_coercivity
    P ((6:ℝ) • u) r hcontract (by
      intro v
      simpa only [real_inner_smul_left] using hpair v)
  have hn : ‖(6:ℝ) • u‖^2 = 36*‖u‖^2 := by
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    ring
  rw [hn] at h
  exact h

theorem combined_norm_budget_gives_raw336 (P : E) (u : F) (r : E → F)
    {N : ℝ} (hcontract : ∀ v, ‖r v‖ ≤ ‖v‖)
    (hpair : ∀ v, inner ℝ P v = 6*inner ℝ u (r v))
    (hbudget : ‖u‖^2 ≤ (28/3:ℝ)*N) : ‖P‖^2 ≤ 336*N := by
  have h := whole_cubic_norm_coercivity P u r hcontract hpair
  linarith

theorem exponential_whole_field_calibration : (36:ℝ)*6=216 := by norm_num

end KLSConstantImprovement.HelfferSteinWholeCubicCombinedSquare
#print axioms KLSConstantImprovement.HelfferSteinWholeCubicCombinedSquare.main_response_cancel_inside_same_field
#print axioms KLSConstantImprovement.HelfferSteinWholeCubicCombinedSquare.whole_cubic_objective
#print axioms KLSConstantImprovement.HelfferSteinWholeCubicCombinedSquare.whole_cubic_norm_coercivity
#print axioms KLSConstantImprovement.HelfferSteinWholeCubicCombinedSquare.combined_norm_budget_gives_raw336
#print axioms KLSConstantImprovement.HelfferSteinWholeCubicCombinedSquare.exponential_whole_field_calibration
