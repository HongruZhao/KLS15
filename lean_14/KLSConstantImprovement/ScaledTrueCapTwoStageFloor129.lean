import KLSConstantImprovement.TrueCapTwoStageOrbitObstruction

/-! The two-step method obstruction does not require the first weight
to equal one. Divide the two weights, value functions, and budget by the
positive first weight. This covers finite nonnegative mixtures of proved
raw budgets once their linear degree-two/three base budget is supplied.
It is a scalar proof-family restriction, not a KLS lower bound.

This isolated source draft has not been compiled by its author. -/

noncomputable section
namespace KLSConstantImprovement.ScaledTrueCapTwoStageFloor129

theorem scaled_true_cap_endpoint_gt_129
    (K C w0 w1 p : ℝ) (V0 V1 V2 : ℝ → ℝ)
    (hKfloor : 6 + 4 * Real.sqrt 2 ≤ K) (hw0 : 0 < w0) (hw1 : 0 ≤ w1)
    (hp : 1 ≤ p)
    (hstep0 : ∀ s, 1 ≤ s → p - (2 / K ^ 2) / p ≤ s → s ≤ p →
      V0 p ≤ w0 * (p - s) + s * V1 s)
    (hstep1 : ∀ r, 1 ≤ r → r ≤ p → ∀ s, 1 ≤ s →
      r - (2 / K ^ 2) / r ≤ s → s ≤ r →
      V1 r ≤ w1 * (r - s) + s * V2 s)
    (hboundary : V2 1 = 0)
    (hbase : w0 * (2 / K ^ 2) +
      w1 * ((802604693 / 2000000 : ℝ) / (36 * K ^ 3)) ≤ C)
    (hbudget : C < p * V0 p) :
    (129 / 10 : ℝ) < 1 + K * p := by
  let U0 : ℝ → ℝ := fun r => V0 r / w0
  let U1 : ℝ → ℝ := fun r => V1 r / w0
  let U2 : ℝ → ℝ := fun r => V2 r / w0
  have hn : w0 ≠ 0 := ne_of_gt hw0
  have h0 : ∀ s, 1 ≤ s → p - (2 / K ^ 2) / p ≤ s → s ≤ p →
      U0 p ≤ p - s + s * U1 s := by
    intro s hs hl hu
    have hh := div_le_div_of_nonneg_right (hstep0 s hs hl hu) hw0.le
    convert hh using 1 <;> dsimp only [U0, U1] <;> field_simp [hn] <;> ring
  have h1 : ∀ r, 1 ≤ r → r ≤ p → ∀ s, 1 ≤ s →
      r - (2 / K ^ 2) / r ≤ s → s ≤ r →
      U1 r ≤ (w1 / w0) * (r - s) + s * U2 s := by
    intro r hr hu s hs hl hsr
    have hh := div_le_div_of_nonneg_right (hstep1 r hr hu s hs hl hsr) hw0.le
    convert hh using 1 <;> dsimp only [U1, U2] <;> field_simp [hn] <;> ring
  have hb : 2 / K ^ 2 + (w1 / w0) *
      ((802604693 / 2000000 : ℝ) / (36 * K ^ 3)) ≤ C / w0 := by
    have hh := div_le_div_of_nonneg_right hbase hw0.le
    convert hh using 1 <;> field_simp [hn] <;> ring
  have hstrict : C / w0 < p * U0 p := by
    have hh := div_lt_div_of_pos_right hbudget hw0
    convert hh using 1 <;> dsimp only [U0] <;> field_simp [hn] <;> ring
  exact TrueCapTwoStageOrbitObstruction.true_cap_family_endpoint_gt_129
    K (C / w0) (w1 / w0) p U0 U1 U2 hKfloor (div_nonneg hw1 hw0.le) hp
    h0 h1 (by simp only [U2, hboundary, zero_div]) hb hstrict

end KLSConstantImprovement.ScaledTrueCapTwoStageFloor129

#print axioms KLSConstantImprovement.ScaledTrueCapTwoStageFloor129.scaled_true_cap_endpoint_gt_129
