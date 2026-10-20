import KLSConstantImprovement.SyntheticGeneratorLossLower

/-! A synthetic finite generator dual for the CURRENT quartic-head family.
The numbers are scalar test energies and are not claimed to arise from an
admissible probability law.  The corner condition at degrees3/4 is explicit;
arbitrary stronger future cubic/quartic supports need not contain it.

This isolated draft has not been compiled by its author. -/

noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.SyntheticEightDegreeBudget
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
open KLSConstantImprovement.SyntheticGeneratorLossLower

def z (d : ℕ) : ℝ :=
  if d = 2 then 2 else
  if d = 3 then 10 else
  if d = 4 then 265 / 4 else
  if d = 5 then 1007 / 2 else
  if d = 6 then 150043 / 36 else
  if d = 7 then 16054601 / 441 else
  if d = 8 then 1557296297 / 4704 else 0

def m (d : ℕ) : ℝ :=
  if d = 2 then 45 else
  if d = 3 then 106 else
  if d = 4 then 190 else
  if d = 5 then 298 else
  if d = 6 then 428 else
  if d = 7 then 582 else 0

def e (P : Parameters) (d : ℕ) : ℝ := P.t d * z d / P.K ^ d

def G (P : Parameters) (d : ℕ) : ℝ :=
  PositiveEnergyWeightedGenerator.generatorLoss P.K P.young P.t P.alpha P.theta P.lambda d +
    1 + cost P d

theorem z_nonnegative (d : ℕ) : 0 ≤ z d := by
  unfold z
  split_ifs <;> norm_num

theorem e_nonnegative {P : Parameters} {H A B : ℝ}
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (d : ℕ) (hd : 2 ≤ d) : 0 ≤ e P d := by
  exact div_nonneg (mul_nonneg (h.weight_positive d hd).le (z_nonnegative d))
    (pow_nonneg h.K_positive.le d)

theorem coefficient_eq (P : Parameters) (d : ℕ) :
    coefficient P d = PositiveEnergyWeightedGenerator.incoming P.K P.t P.alpha d - G P d := by
  unfold coefficient TriplePositiveEnergyWeightedGenerator.coefficient G cost
  ring

theorem head_eq (P : Parameters) : head P = G P 2 := rfl

theorem slope_lower {P : Parameters} {H A B : ℝ}
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (d : ℕ) (hd : 2 ≤ d) (hD : d ≤ 7) : m d * P.alpha d ≤ G P d := by
  have hh := effective_loss_lower h d hd
  change unreservedG d (P.alpha d) ≤ G P d at hh
  interval_cases d
  · exact (slope_two (P.alpha 2) (h.alpha_lt_one 2 (by omega))).trans hh
  · exact (slope_three (P.alpha 3) (h.alpha_lt_one 3 (by omega))).trans hh
  · exact (slope_four (P.alpha 4) (h.alpha_lt_one 4 (by omega))).trans hh
  · exact (slope_five (P.alpha 5) (h.alpha_lt_one 5 (by omega))).trans hh
  · exact (slope_six (P.alpha 6) (h.alpha_lt_one 6 (by omega))).trans hh
  · exact (slope_seven (P.alpha 7) (h.alpha_lt_one 7 (by omega))).trans hh

theorem edge_identity {P : Parameters} {H A B : ℝ}
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (d : ℕ) (hd : 3 ≤ d) (hD : d ≤ 8) :
    PositiveEnergyWeightedGenerator.incoming P.K P.t P.alpha d * e P d =
      (m (d - 1) * P.alpha (d - 1)) * e P (d - 1) := by
  have hK : P.K ≠ 0 := ne_of_gt h.K_positive
  have h2 : P.t 2 ≠ 0 := ne_of_gt (h.weight_positive 2 (by omega))
  have h3 : P.t 3 ≠ 0 := ne_of_gt (h.weight_positive 3 (by omega))
  have h4 : P.t 4 ≠ 0 := ne_of_gt (h.weight_positive 4 (by omega))
  have h5 : P.t 5 ≠ 0 := ne_of_gt (h.weight_positive 5 (by omega))
  have h6 : P.t 6 ≠ 0 := ne_of_gt (h.weight_positive 6 (by omega))
  have h7 : P.t 7 ≠ 0 := ne_of_gt (h.weight_positive 7 (by omega))
  have h8 : P.t 8 ≠ 0 := ne_of_gt (h.weight_positive 8 (by omega))
  interval_cases d <;> norm_num [PositiveEnergyWeightedGenerator.incoming, e, z, m] <;>
    field_simp [hK, h2, h3, h4, h5, h6, h7, h8] <;> ring

theorem coefficient_edge {P : Parameters} {H A B : ℝ}
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (d : ℕ) (hd : 3 ≤ d) (hD : d ≤ 8) :
    coefficient P d * e P d ≤ G P (d - 1) * e P (d - 1) - G P d * e P d := by
  have hs := mul_le_mul_of_nonneg_right (slope_lower h (d - 1) (by omega) (by omega))
    (e_nonnegative h (d - 1) (by omega))
  rw [←edge_identity h d hd hD] at hs
  rw [coefficient_eq]
  nlinarith only [hs]

/-- The synthetic incoming energies telescope against the actual loss,
retaining all same-source reservations and harmonic charges. -/
theorem synthetic_generator_nonpositive {P : Parameters} {H A B : ℝ}
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B) :
    (∑ d ∈ Finset.Icc 3 8, coefficient P d * e P d) - head P * e P 2 ≤ 0 := by
  have h3 := coefficient_edge h 3 (by omega) (by omega)
  have h4 := coefficient_edge h 4 (by omega) (by omega)
  have h5 := coefficient_edge h 5 (by omega) (by omega)
  have h6 := coefficient_edge h 6 (by omega) (by omega)
  have h7 := coefficient_edge h 7 (by omega) (by omega)
  have h8 := coefficient_edge h 8 (by omega) (by omega)
  have hlast : 0 ≤ G P 8 * e P 8 :=
    mul_nonneg (effective_loss_nonnegative h 8 (by omega)) (e_nonnegative h 8 (by omega))
  have heval : (∑ d ∈ Finset.Icc 3 8, coefficient P d * e P d) =
      coefficient P 3 * e P 3 + coefficient P 4 * e P 4 + coefficient P 5 * e P 5 +
      coefficient P 6 * e P 6 + coefficient P 7 * e P 7 + coefficient P 8 * e P 8 := by
    norm_num [show Finset.Icc 3 8 = {3, 4, 5, 6, 7, 8} by decide] <;> ring
  rw [heval, head_eq]
  norm_num only [Nat.reduceSub] at h3 h4 h5 h6 h7 h8
  nlinarith only [h3, h4, h5, h6, h7, h8, hlast]

/-- The current scalar certificate must pay a fixed positive synthetic
energy corner. This is not a universal lower bound for actual energies. -/
theorem synthetic_budget_lt {P : Parameters} {H A B : ℝ}
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (hH : (360 : ℝ) ≤ H) (hcorner : (265 / 4 : ℝ) + A * 10 ≤ B) :
    (∑ d ∈ Finset.Icc 2 8, P.t d * z d / P.K ^ d) < P.C := by
  apply RawCubicQuarticWeightedHead.finite_energy_sum_lt_budget (y := 10) (z := 265 / 4) P
    h.K_positive h.c_positive h.coefficient_lower h.head_nonneg h.fourth_nonneg h.head_margin
    (e P) 8 (by omega)
  · intro d hd
    exact e_nonnegative h d (by have := (Finset.mem_Icc.mp hd).1; omega)
  · apply le_of_eq
    norm_num [e, z] <;> ring
  · norm_num [e, z]
  · norm_num [e, z]
  · norm_num
  · exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 36)).mpr (by linarith)
  · exact hcorner
  · exact synthetic_generator_nonpositive h

/-- The corner lies inside every support from the displayed current raw
cubic-to-quartic barrier family. A stronger future analytic support is
not covered merely by having the same ScalarCertificate type. -/
theorem current_barrier_corner (H J s : ℝ) (hH : (400 : ℝ) ≤ H)
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hJ : 112 * H ≤ J * (1 - s)) :
    (265 / 4 : ℝ) + (J * s / (16 * H)) * 10 ≤ J / 576 := by
  have hH0 : 0 < H := by linarith
  have hJ0 : 0 ≤ J := by
    by_contra hn
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hn) (by linarith : 0 ≤ 1 - s)
    nlinarith
  have hb := mul_le_mul_of_nonneg_right hJ hH0.le
  have hbonus : 0 ≤ J * s * (H - 360) :=
    mul_nonneg (mul_nonneg hJ0 hs0) (by linarith)
  have hsq : 0 ≤ H * (H - 400) := mul_nonneg hH0.le (by linarith)
  have hpoly : (265 / 4 : ℝ) * (576 * H) ≤ J * (H - 360 * s) := by
    nlinarith only [hb, hbonus, hsq, hH]
  have hid : (J / 576 - (J * s / (16 * H)) * 10) * (576 * H) =
      J * (H - 360 * s) := by field_simp [ne_of_gt hH0] <;> ring
  rw [←hid] at hpoly
  have hh := le_of_mul_le_mul_right hpoly (by positivity : 0 < 576 * H)
  linarith

end KLSConstantImprovement.SyntheticEightDegreeBudget

#print axioms KLSConstantImprovement.SyntheticEightDegreeBudget.synthetic_generator_nonpositive
#print axioms KLSConstantImprovement.SyntheticEightDegreeBudget.synthetic_budget_lt
#print axioms KLSConstantImprovement.SyntheticEightDegreeBudget.current_barrier_corner
