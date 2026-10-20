import KLSConstantImprovement.QuadraticCapBellmanCertificates

/-! Rounding each supporting affine line down preserves its global Bellman
certificate. This prevents exact rational contact recursions from producing
exponentially long coefficients; no numerical approximation is assumed. -/
noncomputable section
namespace KLSConstantImprovement.RoundedAffineBellman
open PositiveFiniteHeadBellman
set_option maxHeartbeats 1000000

theorem eval_le_of_coeff_le {L M : Affine}
    (hs : L.slope ≤ M.slope) (hb : L.intercept ≤ M.intercept)
    {r : ℝ} (hr : 0 ≤ r) : L.eval r ≤ M.eval r := by
  exact add_le_add (mul_le_mul_of_nonneg_right hs hr) hb

theorem stage_of_coeff_minorant {w R : ℝ} {lower : ℝ → ℝ}
    {L M next : Affine} (h : StageCertificate w R lower M next)
    (hL : 0 ≤ L.slope) (hs : L.slope ≤ M.slope)
    (hb : L.intercept ≤ M.intercept) :
    StageCertificate w R lower L next := by
  refine ⟨h.weight_nonneg,hL,h.next_slope_nonneg,?_,h.next_at_one,?_⟩
  · exact (eval_le_of_coeff_le hs hb (by norm_num : (0:ℝ) ≤ 1)).trans h.current_at_one
  · intro r hr hrR s hs1 hls hsr
    exact (eval_le_of_coeff_le hs hb (by linarith : 0 ≤ r)).trans
      (h.stage r hr hrR s hs1 hls hsr)

end KLSConstantImprovement.RoundedAffineBellman
#print axioms KLSConstantImprovement.RoundedAffineBellman.eval_le_of_coeff_le
#print axioms KLSConstantImprovement.RoundedAffineBellman.stage_of_coeff_minorant
