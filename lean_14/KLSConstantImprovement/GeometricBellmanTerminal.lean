import Mathlib

/-! Pure scalar fixed-rate terminal subsolution. This draft has not been
compiled. The actual orbit payment and its envelope assumptions belong
to the separate rescaled-orbit wrapper. -/
noncomputable section
namespace KLSConstantImprovement.GeometricBellmanTerminal

def B (b ρ r : ℝ) : ℝ := b*max 0 (r-ρ)

theorem B_nonnegative {b ρ r : ℝ} (hb : 0 ≤ b) : 0 ≤ B b ρ r :=
  mul_nonneg hb (le_max_left _ _)

theorem B_eq_zero_of_le {b ρ r : ℝ} (hr : r ≤ ρ) : B b ρ r=0 := by
  simp only [B,max_eq_left (sub_nonpos.mpr hr),mul_zero]

/-- Unit-coefficient inequality. The successor may exceed the current
ratio or lie below the fixed-rate threshold. -/
theorem positive_part_step
    {ρ r s d : ℝ} (hρ : 0 < ρ) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hdrop : r-s ≤ d) :
    max 0 (r-ρ) ≤ d+(s/ρ)*max 0 (s-ρ) := by
  have hraw : r-ρ ≤ d+(s/ρ)*max 0 (s-ρ) := by
    by_cases hsρ : s ≤ ρ
    · rw [max_eq_left (sub_nonpos.mpr hsρ),mul_zero,add_zero]
      linarith only [hdrop,hsρ]
    · have hρs : ρ ≤ s := (lt_of_not_ge hsρ).le
      rw [max_eq_right (sub_nonneg.mpr hρs)]
      have hnonneg : 0 ≤ ρ*(d-(r-s))+(s-ρ)^2 :=
        add_nonneg (mul_nonneg hρ.le (sub_nonneg.mpr hdrop)) (sq_nonneg _)
      have hid :
          ρ*(d+(s/ρ)*(s-ρ)-(r-ρ))=
            ρ*(d-(r-s))+(s-ρ)^2 := by
        field_simp [ne_of_gt hρ]
        ring
      rw [←hid] at hnonneg
      have hh : 0 ≤ d+(s/ρ)*(s-ρ)-(r-ρ) :=
        (mul_nonneg_iff_of_pos_left hρ).mp hnonneg
      linarith only [hh]
  have hright : 0 ≤ d+(s/ρ)*max 0 (s-ρ) :=
    add_nonneg hd (mul_nonneg (div_nonneg hs hρ.le) (le_max_left _ _))
  exact max_le hright hraw

/-- A geometric terminal coefficient may decrease by rho at each stage.
Only b<=w is needed; there is no monotonicity restriction on r,s. -/
theorem terminal_step
    {ρ b w r s d : ℝ} (hρ : 0 < ρ) (hb : 0 ≤ b) (hbw : b ≤ w)
    (hs : 0 ≤ s) (hd : 0 ≤ d) (hdrop : r-s ≤ d) :
    B b ρ r ≤ w*d+s*B (b/ρ) ρ s := by
  have hh := positive_part_step hρ hs hd hdrop
  calc
    B b ρ r ≤ b*(d+(s/ρ)*max 0 (s-ρ)) :=
      mul_le_mul_of_nonneg_left hh hb
    _ = b*d+s*B (b/ρ) ρ s := by
      unfold B
      simp only [div_eq_mul_inv]
      ring
    _ ≤ w*d+s*B (b/ρ) ρ s :=
      add_le_add (mul_le_mul_of_nonneg_right hbw hd) (le_refl _)

end KLSConstantImprovement.GeometricBellmanTerminal

#print axioms KLSConstantImprovement.GeometricBellmanTerminal.B_nonnegative
#print axioms KLSConstantImprovement.GeometricBellmanTerminal.positive_part_step
#print axioms KLSConstantImprovement.GeometricBellmanTerminal.terminal_step
