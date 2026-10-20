import QuinticInterval24886
import ScalarGrowth

/-! Scalar certificate for the candidate 24.886. No universal Poincare
endpoint is asserted here; the actual-law analytic gates remain open. -/

noncomputable section
namespace Quintic24886

def limitingMargin (z : ℝ) : ℝ :=
  (-1 / (z * Up z)) * (alpha * K * z - A * U z - r * Real.sqrt (U z)) -
    2 - r / Real.sqrt z

theorem limitingMargin_positive {z : ℝ} (hz : z ∈ Set.Icc (29 / 50) 1) :
    0 < limitingMargin z := by
  have hzpos : 0 < z := by linarith [hz.1]
  have hup := Up_negative_on_interval hz
  have hm := strict_barrier_margin hz
  have hden : 0 < -z * Up z := by nlinarith
  have hid : limitingMargin z * (-z * Up z) =
      alpha * K * z - A * U z - r * Real.sqrt (U z) +
        (2 * z + r * Real.sqrt z) * Up z := by
    unfold limitingMargin
    have hs : Real.sqrt z * Real.sqrt z = z := Real.mul_self_sqrt hzpos.le
    have hsne : Real.sqrt z ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hzpos)
    field_simp [ne_of_gt hzpos, ne_of_lt hup, hsne]
    linear_combination -(Up z * r) * hs
  have hp : 0 < limitingMargin z * (-z * Up z) := by rwa [hid]
  exact (mul_pos_iff_of_pos_right hden).1 hp

theorem certified_inverse_branch (u : ℝ) (hu : u ∈ Set.Icc 0 1) :
    ∃! z, z ∈ Set.Icc (29 / 50) 1 ∧ U z = u ∧ 0 < limitingMargin z := by
  obtain ⟨z, hz, hunique⟩ := U_branch_has_all_values u hu
  refine ⟨z, ⟨hz.1, hz.2, limitingMargin_positive hz.1⟩, ?_⟩
  intro y hy
  exact hunique y ⟨hy.1, hy.2.1⟩

theorem optimized_scalar_growth (z : ℕ → ℝ) (hz0 : z 0 = 1)
    (hz1 : 1 + Delta / (K * s) < z 1)
    (hrec : ∀ j : ℕ, 0 < z j → 0 < z (j + 1) →
      z (j + 1) ^ 2 / z j - B / (K ^ 2 * s) ≤ z (j + 2)) :
    ∀ j : ℕ, 0 < z j ∧
      (1 + Real.sqrt ((Delta / (K * s)) ^ 2 - 2 * (B / (K ^ 2 * s)))) ^ j ≤ z j := by
  obtain ⟨hq, he, hgap⟩ := scalar_q_epsilon
    (Delta / (K * s)) (B / (K ^ 2 * s)) rfl rfl
  exact KLSBelow25.scalar_growth_of_initial_gap he hq hgap z hz0 hz1 hrec

#print axioms limitingMargin_positive
#print axioms certified_inverse_branch
#print axioms optimized_scalar_growth

end Quintic24886
