import Mathlib

/-! An elementary proof of the vector-state Jensen inequality for
`g_a(t)=t/(1+a*t)`, using a positive inverse and a quadratic form.
No spectral-measure or Jensen hypothesis is assumed. -/
noncomputable section
namespace KLSBelow25
open ContinuousLinearMap InnerProductSpace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

section Real
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The inverse quadratic form is at least the reciprocal quadratic form.
This proof is the positivity test at `v - q * Uv`. -/
theorem inverse_quadratic_lower_bound
    (Q U : H →L[ℝ] H) (hQ : Q.IsPositive) (hQU : Q * U = 1)
    (v : H) (hv : ‖v‖ = 1) (hq : 0 < ⟪Q v, v⟫_ℝ) :
    1 / ⟪Q v, v⟫_ℝ ≤ ⟪U v, v⟫_ℝ := by
  have hQu : Q (U v) = v := by
    have he := congrArg (fun A : H →L[ℝ] H => A v) hQU
    simpa using he
  have hnorm : ⟪v, v⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hsym : ⟪Q v, U v⟫_ℝ = 1 := by
    rw [hQ.inner_left_eq_inner_right, hQu, hnorm]
  have hpos := hQ.re_inner_nonneg_left (v - ⟪Q v, v⟫_ℝ • U v)
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, RCLike.re_to_real, hQu,
    hsym, hnorm] at hpos
  rw [← real_inner_comm v (U v)] at hpos
  apply (div_le_iff₀ hq).mpr
  have hprod : 0 ≤ ⟪Q v, v⟫_ℝ * (⟪Q v, v⟫_ℝ * ⟪U v, v⟫_ℝ - 1) := by nlinarith
  have := (mul_nonneg_iff_of_pos_left hq).mp hprod
  linarith

variable [CompleteSpace H]

theorem positive_resolvent_isUnit
    (T : H →L[ℝ] H) (hT : T.IsPositive) {a : ℝ} (ha : 0 ≤ a) :
    IsUnit (1 + a • T) := by
  apply isUnit_of_forall_le_norm_inner_map (c := 1) _ (by norm_num)
  intro v
  have hnonneg := hT.re_inner_nonneg_left v
  have hreal : ‖v‖ ^ 2 ≤ ⟪(1 + a • T) v, v⟫_ℝ := by
    simp only [add_apply, one_apply_eq_self, smul_apply, inner_add_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [RCLike.re_to_real] at hnonneg
    nlinarith
  simpa only [NNReal.coe_one, mul_one, Real.norm_eq_abs] using
    hreal.trans (le_abs_self _)

/-- The rational resolvent form satisfies the actual Jensen bound. -/
theorem resolvent_quadratic_jensen
    (T U : H →L[ℝ] H) (hT : T.IsPositive) {a : ℝ} (ha : 0 < a)
    (hU : (1 + a • T) * U = 1) (v : H) (hv : ‖v‖ = 1) :
    ⟪(a⁻¹ • (1 - U)) v, v⟫_ℝ ≤
      ⟪T v, v⟫_ℝ / (1 + a * ⟪T v, v⟫_ℝ) := by
  have hp := hT.re_inner_nonneg_left v
  simp only [RCLike.re_to_real] at hp
  have hden : 0 < 1 + a * ⟪T v, v⟫_ℝ := by positivity
  have hnorm : ⟪v, v⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hq : ⟪(1 + a • T) v, v⟫_ℝ = 1 + a * ⟪T v, v⟫_ℝ := by
    simp only [add_apply, one_apply_eq_self, smul_apply, inner_add_left, real_inner_smul_left, hnorm]
  have hQ : (1 + a • T).IsPositive := isPositive_one.add (hT.smul_of_nonneg ha.le)
  have hi := inverse_quadratic_lower_bound (1 + a • T) U hQ hU v hv (by rwa [hq])
  rw [hq] at hi
  simp only [smul_apply, sub_apply, one_apply_eq_self, real_inner_smul_left,
    inner_sub_left, hnorm]
  have hi' := (div_le_iff₀ hden).mp hi
  apply (le_div_iff₀ hden).mpr
  calc
    a⁻¹ * (1 - ⟪U v, v⟫_ℝ) * (1 + a * ⟪T v, v⟫_ℝ)
        = a⁻¹ * ((1 + a * ⟪T v, v⟫_ℝ) -
            ⟪U v, v⟫_ℝ * (1 + a * ⟪T v, v⟫_ℝ)) := by ring
    _ ≤ a⁻¹ * ((1 + a * ⟪T v, v⟫_ℝ) - 1) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha.le)
      linarith
    _ = ⟪T v, v⟫_ℝ := by field_simp <;> ring

/-- The rational resolvent is bounded above by its positive argument on
all quadratic forms, without a unit-vector restriction. -/
theorem resolvent_quadratic_le_argument
    (T U : H →L[ℝ] H) (hT : T.IsPositive) {a : ℝ} (ha : 0 < a)
    (hU : (1 + a • T) * U = 1) (v : H) :
    ⟪(a⁻¹ • (1 - U)) v, v⟫_ℝ ≤ ⟪T v, v⟫_ℝ := by
  let Q : H →L[ℝ] H := 1 + a • T
  have hQ : Q.IsPositive := isPositive_one.add (hT.smul_of_nonneg ha.le)
  have hQu : Q (U v) = v := by
    exact congrArg (fun A : H →L[ℝ] H => A v) hU
  have hcross : ⟪Q v, U v⟫_ℝ = ⟪v, v⟫_ℝ := by
    rw [hQ.inner_left_eq_inner_right, hQu]
  have hpos := hQ.re_inner_nonneg_left (v - U v)
  simp only [map_sub, inner_sub_left, inner_sub_right, RCLike.re_to_real,
    hQu, hcross] at hpos
  rw [← real_inner_comm v (U v)] at hpos
  have hq : ⟪Q v, v⟫_ℝ = ⟪v, v⟫_ℝ + a * ⟪T v, v⟫_ℝ := by
    simp only [Q, add_apply, one_apply_eq_self, smul_apply, inner_add_left,
      real_inner_smul_left]
  rw [hq] at hpos
  simp only [smul_apply, sub_apply, one_apply_eq_self, real_inner_smul_left, inner_sub_left]
  calc
    a⁻¹ * (⟪v, v⟫_ℝ - ⟪U v, v⟫_ℝ) ≤ a⁻¹ * (a * ⟪T v, v⟫_ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha.le)
      linarith
    _ = ⟪T v, v⟫_ℝ := by field_simp <;> ring

end Real

section Complex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The same genuine rational Jensen inequality on a complex Hilbert space. -/
theorem complex_resolvent_quadratic_jensen
    (T U : H →L[ℂ] H) (hT : T.IsPositive) {a : ℝ} (ha : 0 < a)
    (hU : (1 + a • T) * U = 1) (v : H) (hv : ‖v‖ = 1) :
    Complex.re ⟪(a⁻¹ • (1 - U)) v, v⟫_ℂ ≤
      Complex.re ⟪T v, v⟫_ℂ / (1 + a * Complex.re ⟪T v, v⟫_ℂ) := by
  letI := InnerProductSpace.rclikeToReal ℂ H
  have hp : (T.restrictScalars ℝ).IsPositive := by
    refine ⟨hT.isSymmetric.restrictScalars, ?_⟩
    intro x
    exact hT.re_inner_nonneg_left x
  have hu : (1 + a • T.restrictScalars ℝ) * U.restrictScalars ℝ = 1 := by
    ext x
    have he := congrArg (fun A : H →L[ℂ] H => A x) hU
    exact he
  exact resolvent_quadratic_jensen (T.restrictScalars ℝ) (U.restrictScalars ℝ)
    hp ha hu v hv
theorem complex_resolvent_quadratic_le_argument
    (T U : H →L[ℂ] H) (hT : T.IsPositive) {a : ℝ} (ha : 0 < a)
    (hU : (1 + a • T) * U = 1) (v : H) :
    Complex.re ⟪(a⁻¹ • (1 - U)) v, v⟫_ℂ ≤ Complex.re ⟪T v, v⟫_ℂ := by
  letI := InnerProductSpace.rclikeToReal ℂ H
  have hp : (T.restrictScalars ℝ).IsPositive := by
    refine ⟨hT.isSymmetric.restrictScalars, ?_⟩
    intro x
    exact hT.re_inner_nonneg_left x
  have hu : (1 + a • T.restrictScalars ℝ) * U.restrictScalars ℝ = 1 := by
    ext x
    exact congrArg (fun A : H →L[ℂ] H => A x) hU
  exact resolvent_quadratic_le_argument (T.restrictScalars ℝ)
    (U.restrictScalars ℝ) hp ha hu v

end Complex

#print axioms complex_resolvent_quadratic_jensen

#print axioms resolvent_quadratic_le_argument
#print axioms complex_resolvent_quadratic_le_argument
#print axioms inverse_quadratic_lower_bound
#print axioms positive_resolvent_isUnit
#print axioms resolvent_quadratic_jensen
end KLSBelow25
