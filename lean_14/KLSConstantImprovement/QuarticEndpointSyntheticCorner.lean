import KLSConstantImprovement.RawCubicQuarticEndpointBarrier
import KLSConstantImprovement.SyntheticEightDegreeBudget

/-! The actual current quartic endpoint certificate implies the synthetic
corner condition. Thus that condition is discharged for this analytic head
family, rather than silently assumed for arbitrary supports.
This isolated source draft has not been compiled by its author. -/

noncomputable section
namespace KLSConstantImprovement.QuarticEndpointSyntheticCorner

theorem endpoint_forces_J_lower {H J s a b c : ℝ}
    (h : RawCubicQuarticEndpointBarrier.EndpointCertificate H J s a b c) :
    112 * H ≤ J * (1 - s) := by
  have hs : 0 < s := h.contact_unit.1
  have hden : 0 < 1 - s := sub_pos.mpr h.contact_unit.2
  have hq : 0 ≤ s / (1 - s) := div_nonneg hs.le hden.le
  have hqa : 0 ≤ (s / (1 - s)) * a := mul_nonneg hq h.a_nonneg
  have hleft : 0 < 29 + b + c := by linarith [h.b_nonneg, h.c_nonneg]
  have hbase : 56 * (s / (1 - s)) < s * J / (2 * H) := by
    nlinarith only [h.margin, hqa, hleft]
  have hm := mul_lt_mul_of_pos_right hbase
    (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) h.H_positive) hden)
  have hL : (56 * (s / (1 - s))) * (2 * H * (1 - s)) = s * (112 * H) := by
    field_simp [ne_of_gt hden] <;> ring
  have hR : (s * J / (2 * H)) * (2 * H * (1 - s)) = s * (J * (1 - s)) := by
    field_simp [ne_of_gt h.H_positive] <;> ring
  rw [hL, hR] at hm
  exact (lt_of_mul_lt_mul_left hm hs.le).le

theorem endpoint_contains_synthetic_corner {H J s a b c : ℝ}
    (h : RawCubicQuarticEndpointBarrier.EndpointCertificate H J s a b c)
    (hH : (400 : ℝ) ≤ H) :
    (265 / 4 : ℝ) + (J * s / (16 * H)) * 10 ≤ J / 576 :=
  SyntheticEightDegreeBudget.current_barrier_corner H J s hH h.contact_unit.1.le h.contact_unit.2
    (endpoint_forces_J_lower h)

end KLSConstantImprovement.QuarticEndpointSyntheticCorner

#print axioms KLSConstantImprovement.QuarticEndpointSyntheticCorner.endpoint_forces_J_lower
#print axioms KLSConstantImprovement.QuarticEndpointSyntheticCorner.endpoint_contains_synthetic_corner
