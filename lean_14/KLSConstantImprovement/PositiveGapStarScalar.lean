import KLSConstantImprovement.DeficitCurvatureScalar

/-! Scalar values of two dimension-growing fully symmetric tensor families.
Literal tensor contraction identification and original-law fourth-operator
exclusion are in the independent proof note/checker. This module proves the
gap/excess sequence arithmetic, with no actual log-concave-law realization.
The scalar fourth-deficit exclusion bounds remain explicit hypotheses. -/
noncomputable section
namespace KLSConstantImprovement.PositiveGapStarScalar
set_option maxHeartbeats 2000000

def positiveR2 (k : ℝ) : ℝ := 4/k+2/k^2
def positiveR3 (k : ℝ) : ℝ := 2/k+3/k^2
def positiveS (k : ℝ) : ℝ := 1+4/k^2
def positiveGap (k : ℝ) : ℝ := positiveR2 k-positiveR3 k
def negativeR2 (k : ℝ) : ℝ := 4*Real.sqrt 2/k+4/k^2
def negativeR3 (k : ℝ) : ℝ := 2/k^2
def negativeS (_k : ℝ) : ℝ := -2
def negativeGap (k : ℝ) : ℝ := negativeR2 k-negativeR3 k

theorem bounded_fourth_operator_cross {plus minus cross : ℝ}
    (hp0 : 0 ≤ plus) (hp16 : plus ≤ 16)
    (hm0 : 0 ≤ minus) (hm16 : minus ≤ 16)
    (hpolarization : 4*cross = plus-minus) : |cross| ≤ 4 := by
  apply abs_le.mpr
  constructor <;> linarith

theorem positive_fourth_deficit_from_cross {k d head cross : ℝ}
    (hk : 0 < k) (hhead : 0 ≤ head) (hcross : |cross| ≤ 4)
    (hidentity : d = head+12+4*cross/k) : 12-16/k ≤ d := by
  have hlow : -4 ≤ cross := (abs_le.mp hcross).1
  have hdiv := div_le_div_of_nonneg_right hlow hk.le
  ring_nf at hidentity hdiv ⊢
  nlinarith

theorem negative_fourth_deficit_from_cross {k d head0 head1 cross0 cross1 : ℝ}
    (hk : 0 < k) (hhead0 : 0 ≤ head0) (hhead1 : 0 ≤ head1)
    (hcross0 : |cross0| ≤ 4) (hcross1 : |cross1| ≤ 4)
    (hidentity : d = head0+head1+24+4*(cross0+cross1)/k) :
    24-32/k ≤ d := by
  have hlow0 : -4 ≤ cross0 := (abs_le.mp hcross0).1
  have hlow1 : -4 ≤ cross1 := (abs_le.mp hcross1).1
  have hdiv := div_le_div_of_nonneg_right (by linarith : -8 ≤ cross0+cross1) hk.le
  ring_nf at hidentity hdiv ⊢
  nlinarith

theorem positive_gap_formula (k : ℝ) :
    positiveGap k = 2/k-1/k^2 := by
  unfold positiveGap positiveR2 positiveR3
  ring

theorem positive_excess_formula {k : ℝ} (hk : k ≠ 0) :
    positiveS k-positiveR3 k = (1-1/k)^2 := by
  unfold positiveS positiveR3
  field_simp [hk] <;> ring

theorem positive_gap_upper (k : ℝ) : positiveGap k ≤ 2/k := by
  rw [positive_gap_formula]
  have hn : 0 ≤ 1/k^2 := by positivity
  linarith

theorem positive_gap_nonneg {k : ℝ} (hk : 1 ≤ k) : 0 ≤ positiveGap k := by
  have hp : 0 < k := by linarith
  have hratio : 1/k ≤ 1 := (div_le_iff₀ hp).mpr (by linarith)
  have hratio0 : 0 ≤ 1/k := by positivity
  have hid : positiveGap k = 2*(1/k)-(1/k)^2 := by
    rw [positive_gap_formula]
    field_simp [hp.ne'] <;> ring
  rw [hid]
  nlinarith

theorem positive_excess_lower {k : ℝ} (hk : 2 ≤ k) :
    (1/4:ℝ) ≤ positiveS k-positiveR3 k := by
  have hp : 0 < k := by linarith
  have hratio : 1/k ≤ (1/2:ℝ) := (div_le_iff₀ hp).mpr (by linarith)
  rw [positive_excess_formula hp.ne']
  nlinarith [sq_nonneg ((1-1/k)-(1/2:ℝ))]

theorem arbitrarily_small_positive_gap_with_fixed_excess {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ k : ℕ, 2 ≤ k ∧ 0 ≤ positiveGap (k:ℝ) ∧
      positiveGap (k:ℝ) ≤ epsilon ∧
        (1/4:ℝ) ≤ positiveS (k:ℝ)-positiveR3 (k:ℝ) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max (2:ℝ) (2/epsilon))
  have hk2 : (2:ℝ) ≤ (k:ℝ) := (le_max_left _ _).trans hk.le
  have hkNat : 2 ≤ k := by exact_mod_cast hk2
  have hp : 0 < (k:ℝ) := by linarith
  have hscale : 2/epsilon ≤ (k:ℝ) := (le_max_right _ _).trans hk.le
  have hmul := (div_le_iff₀ hepsilon).mp hscale
  have hupper : 2/(k:ℝ) ≤ epsilon := (div_le_iff₀ hp).mpr (by nlinarith)
  exact ⟨k,hkNat,positive_gap_nonneg (by linarith),
    (positive_gap_upper _).trans hupper,positive_excess_lower hk2⟩

theorem negative_gap_nonneg {k : ℝ} (hk : 1 ≤ k) : 0 ≤ negativeGap k := by
  have hp : 0 < k := by linarith
  have hid : negativeGap k = 4*Real.sqrt 2/k+2/k^2 := by
    unfold negativeGap negativeR2 negativeR3
    ring
  rw [hid]
  positivity

theorem negative_gap_upper {k : ℝ} (hk : 1 ≤ k) :
    negativeGap k ≤ (4*Real.sqrt 2+2)/k := by
  have hp : 0 < k := by linarith
  have hratio : 1/k ≤ 1 := (div_le_iff₀ hp).mpr (by linarith)
  have hratio0 : 0 ≤ 1/k := by positivity
  have hsq : (1/k)^2 ≤ 1/k := by nlinarith
  have hid : negativeGap k = 4*Real.sqrt 2*(1/k)+2*(1/k)^2 := by
    unfold negativeGap negativeR2 negativeR3
    field_simp [hp.ne'] <;> ring
  have hr : (4*Real.sqrt 2+2)/k = 4*Real.sqrt 2*(1/k)+2*(1/k) := by ring
  rw [hid,hr]
  nlinarith

theorem arbitrarily_small_gap_with_negative_signed_value {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ k : ℕ, 2 ≤ k ∧ 0 ≤ negativeGap (k:ℝ) ∧
      negativeGap (k:ℝ) ≤ epsilon ∧ negativeS (k:ℝ) = -2 := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max (2:ℝ) ((4*Real.sqrt 2+2)/epsilon))
  have hk2 : (2:ℝ) ≤ (k:ℝ) := (le_max_left _ _).trans hk.le
  have hkNat : 2 ≤ k := by exact_mod_cast hk2
  have hp : 0 < (k:ℝ) := by linarith
  have hscale : (4*Real.sqrt 2+2)/epsilon ≤ (k:ℝ) := (le_max_right _ _).trans hk.le
  have hmul := (div_le_iff₀ hepsilon).mp hscale
  have hupper : (4*Real.sqrt 2+2)/(k:ℝ) ≤ epsilon :=
    (div_le_iff₀ hp).mpr (by nlinarith)
  exact ⟨k,hkNat,negative_gap_nonneg (by linarith),
    (negative_gap_upper (by linarith)).trans hupper,rfl⟩

theorem positive_fourth_deficit_exclusion {k d : ℝ}
    (hk : 8 ≤ k) (hd : 12-16/k ≤ d) : 10 ≤ d := by
  have hp : 0 < k := by linarith
  have hfrac : 16/k ≤ 2 := (div_le_iff₀ hp).mpr (by linarith)
  linarith

theorem negative_fourth_deficit_exclusion {k d : ℝ}
    (hk : 8 ≤ k) (hd : 24-32/k ≤ d) : 20 ≤ d := by
  have hp : 0 < k := by linarith
  have hfrac : 32/k ≤ 4 := (div_le_iff₀ hp).mpr (by linarith)
  linarith

end KLSConstantImprovement.PositiveGapStarScalar
#print axioms KLSConstantImprovement.PositiveGapStarScalar.bounded_fourth_operator_cross
#print axioms KLSConstantImprovement.PositiveGapStarScalar.positive_fourth_deficit_from_cross
#print axioms KLSConstantImprovement.PositiveGapStarScalar.negative_fourth_deficit_from_cross
#print axioms KLSConstantImprovement.PositiveGapStarScalar.positive_gap_formula
#print axioms KLSConstantImprovement.PositiveGapStarScalar.positive_excess_formula
#print axioms KLSConstantImprovement.PositiveGapStarScalar.positive_gap_nonneg
#print axioms KLSConstantImprovement.PositiveGapStarScalar.positive_excess_lower
#print axioms KLSConstantImprovement.PositiveGapStarScalar.arbitrarily_small_positive_gap_with_fixed_excess
#print axioms KLSConstantImprovement.PositiveGapStarScalar.negative_gap_upper
#print axioms KLSConstantImprovement.PositiveGapStarScalar.arbitrarily_small_gap_with_negative_signed_value
#print axioms KLSConstantImprovement.PositiveGapStarScalar.positive_fourth_deficit_exclusion
#print axioms KLSConstantImprovement.PositiveGapStarScalar.negative_fourth_deficit_exclusion
