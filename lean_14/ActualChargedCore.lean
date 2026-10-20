import ExponentialMoments

/-!
# Charged Poincaré inequality on the actual scalar exponential compact core

This module proves a theorem about `ProbabilityTheory.expMeasure 1`, not a
formal moment model. The test function is C¹ with compact support. The
extension to a weighted Sobolev completion and tensor products is not asserted.
-/

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set

noncomputable section
set_option maxHeartbeats 1200000
namespace KLSImprovement.Exponential

open KLSImprovement.ExponentialMoments

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

abbrev law : Measure ℝ := expMeasure 1

/-- The weighted integration-by-parts identity follows from the actual density
and the improper fundamental theorem of calculus. -/
theorem integral_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    (∫ y, deriv f y ∂law) = (∫ y, f y ∂law) - f 0 := by
  let F : ℝ → ℝ := fun y => Real.exp (-y) * f y
  have hF : ContDiff ℝ 1 F := by dsimp [F]; fun_prop
  have hcF : HasCompactSupport F := hc.mul_left
  have hderiv : deriv F = fun y =>
      Real.exp (-y) * deriv f y - Real.exp (-y) * f y := by
    funext y
    dsimp [F]
    have he : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-y)) y := by
      simpa using ((hasDerivAt_id y).neg.exp)
    convert (he.mul ((hf.differentiable one_ne_zero y).hasDerivAt)).deriv using 1
    ring
  have hi₁ : IntegrableOn (fun y => Real.exp (-y) * deriv f y) (Ioi 0) := by
    exact ((hf.continuous_deriv le_rfl).mul (by fun_prop :
      Continuous (fun y : ℝ => Real.exp (-y)))).integrable_of_hasCompactSupport
        (hc.deriv.mul_right) |>.integrableOn |>.congr_fun
          (fun y _ => mul_comm _ _) measurableSet_Ioi
  have hi₂ : IntegrableOn F (Ioi 0) :=
    hF.continuous.integrable_of_hasCompactSupport hcF |>.integrableOn
  have hFTC := hcF.integral_Ioi_deriv_eq hF 0
  rw [hderiv, integral_sub hi₁ hi₂] at hFTC
  rw [integral_expMeasure_one, integral_expMeasure_one,
    integral_Ici_eq_integral_Ioi, integral_Ici_eq_integral_Ioi]
  simp only [F, neg_zero, Real.exp_zero, one_mul] at hFTC
  linarith

/-- Bessel's two charges for the actual centered variance-one coordinate. -/
theorem two_charges_le (r : ℝ → ℝ) (hr : MemLp r 2 law) :
    (∫ y, r y ∂law) ^ 2 + (∫ y, (y - 1) * r y ∂law) ^ 2 ≤
      ∫ y, (r y) ^ 2 ∂law := by
  let c : ℝ := ∫ y, (y - 1) * r y ∂law
  have hX : MemLp (fun y : ℝ => y - 1) 2 law := expMeasure_one_memLp_centered
  have hn := variance_nonneg (fun y => r y - c * (y - 1)) law
  rw [variance_fun_sub hr (hX.const_mul c), variance_const_mul,
    covariance_const_mul_right, variance_eq_sub hr,
    covariance_eq_sub hr hX,
    expMeasure_one_variance_centered, expMeasure_one_integral_centered] at hn
  simp only [Pi.mul_apply, Pi.pow_apply] at hn
  have hcomm : (∫ y, r y * (y - 1) ∂law) = c := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun _ => mul_comm _ _
  rw [hcomm] at hn
  dsimp [c] at hn ⊢
  nlinarith

/-- Every C¹ compactly supported scalar test satisfies the stronger
exponential inequality retaining both affine charges. -/
theorem charged_core (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    variance f law +
        ((∫ y, (y - 1) * f y ∂law) - 2 * (∫ y, deriv f y ∂law)) ^ 2 +
        2 * (∫ y, deriv f y ∂law) ^ 2 ≤
      4 * (∫ y, (deriv f y) ^ 2 ∂law) := by
  let b : ℝ := ∫ y, deriv f y ∂law
  let c : ℝ := ∫ y, f y ∂law
  let m : ℝ := ∫ y, (y - 1) * f y ∂law
  let r : ℝ → ℝ := fun y => deriv f y - (1 / 2 : ℝ) * f y
  have hF : MemLp f 2 law := hf.continuous.memLp_of_hasCompactSupport hc
  have hdF : MemLp (deriv f) 2 law :=
    (hf.continuous_deriv le_rfl).memLp_of_hasCompactSupport hc.deriv
  have hFi : Integrable f law := hF.integrable (by norm_num)
  have hdFi : Integrable (deriv f) law := hdF.integrable (by norm_num)
  have hX : MemLp (fun y : ℝ => y - 1) 2 law := expMeasure_one_memLp_centered
  have hXf : Integrable (fun y => (y - 1) * f y) law := hX.integrable_mul hF
  have hXdf : Integrable (fun y => (y - 1) * deriv f y) law :=
    hX.integrable_mul hdF
  have hdf_f : Integrable (fun y => deriv f y * f y) law := hdF.integrable_mul hF
  have hb : b = c - f 0 := by
    dsimp [b]
    exact integral_deriv f hf hc
  have hsqIBP : 2 * (∫ y, deriv f y * f y ∂law) =
      (∫ y, (f y) ^ 2 ∂law) - (f 0) ^ 2 := by
    have he := integral_deriv (fun y => f y * f y) (hf.mul hf) hc.mul_right
    have hde : deriv (fun y => f y * f y) = fun y => 2 * (deriv f y * f y) := by
      funext y
      convert (((hf.differentiable one_ne_zero y).hasDerivAt).mul
        ((hf.differentiable one_ne_zero y).hasDerivAt)).deriv using 1
      ring
    rw [hde, integral_const_mul] at he
    simpa only [pow_two] using he
  have hXIBP : (∫ y, (y - 1) * deriv f y ∂law) = m - b := by
    have hg : ContDiff ℝ 1 (fun y : ℝ => (y - 1) * f y) := by fun_prop
    have he := integral_deriv (fun y => (y - 1) * f y) hg hc.mul_left
    have hde : deriv (fun y : ℝ => (y - 1) * f y) =
        fun y => f y + (y - 1) * deriv f y := by
      funext y
      have hd : HasDerivAt (fun z : ℝ => z - 1) 1 y := by
        simpa only [id_eq] using (hasDerivAt_id y).sub_const (1 : ℝ)
      have he := (hd.mul ((hf.differentiable one_ne_zero y).hasDerivAt)).deriv
      convert he using 1
      simp only [one_mul]
    rw [hde, integral_add hFi hXdf] at he
    dsimp [m, c] at hb ⊢
    norm_num only [zero_sub, neg_one_mul] at he
    linarith [hb]
  have hr : MemLp r 2 law := hdF.sub (hF.const_mul (1 / 2 : ℝ))
  have hrmean : (∫ y, r y ∂law) = b - c / 2 := by
    dsimp [r, b, c]
    rw [integral_sub hdFi (hFi.const_mul _), integral_const_mul]
    ring
  have hrcharge : (∫ y, (y - 1) * r y ∂law) = m / 2 - b := by
    have he : (fun y => (y - 1) * r y) =
        (fun y => (y - 1) * deriv f y - (1 / 2 : ℝ) * ((y - 1) * f y)) := by
      funext y; dsimp [r]; ring
    rw [he, integral_sub hXdf (hXf.const_mul _), integral_const_mul, hXIBP]
    dsimp [m]
    ring
  have hrsq : (∫ y, (r y) ^ 2 ∂law) =
      (∫ y, (deriv f y) ^ 2 ∂law) -
      (∫ y, deriv f y * f y ∂law) +
      (1 / 4 : ℝ) * (∫ y, (f y) ^ 2 ∂law) := by
    have he : (fun y => (r y) ^ 2) =
        (fun y => (deriv f y) ^ 2 - deriv f y * f y +
          (1 / 4 : ℝ) * (f y) ^ 2) := by
      funext y; dsimp [r]; ring
    have hsub : Integrable (fun y => (deriv f y) ^ 2 - deriv f y * f y) law := by
      convert hdF.integrable_sq.sub hdf_f using 1
    have hquart : Integrable (fun y => (1 / 4 : ℝ) * (f y) ^ 2) law :=
      hF.integrable_sq.const_mul (1 / 4 : ℝ)
    rw [he, integral_add (f := fun y => (deriv f y) ^ 2 - deriv f y * f y)
      (g := fun y => (1 / 4 : ℝ) * (f y) ^ 2)
      hsub hquart,
      integral_sub (f := fun y => (deriv f y) ^ 2)
        (g := fun y => deriv f y * f y) hdF.integrable_sq hdf_f,
      integral_const_mul]
  have hproj := two_charges_le r hr
  rw [hrmean, hrcharge, hrsq] at hproj
  rw [variance_eq_sub hF]
  have hbsq : (f 0) ^ 2 = (c - b) ^ 2 := by
    have he : f 0 = c - b := by linarith [hb]
    rw [he]
  dsimp [b, m, c] at hb hproj hbsq ⊢
  nlinarith [hsqIBP, hbsq]

/-- The sharp scalar constant four on the actual exponential compact core. -/
theorem poincare_core (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    variance f law ≤ 4 * (∫ y, (deriv f y) ^ 2 ∂law) := by
  have he := charged_core f hf hc
  nlinarith [sq_nonneg ((∫ y, (y - 1) * f y ∂law) - 2 * (∫ y, deriv f y ∂law)),
    sq_nonneg (∫ y, deriv f y ∂law)]

/-- On the mean-gradient-zero core the covariance charge has coefficient one,
stronger than the coefficient one third needed by the affine Schur interface. -/
theorem charged_core_of_mean_deriv_zero (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (hb : (∫ y, deriv f y ∂law) = 0) :
    variance f law + (∫ y, (y - 1) * f y ∂law) ^ 2 ≤
      4 * (∫ y, (deriv f y) ^ 2 ∂law) := by
  simpa only [hb, mul_zero, sub_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero]
    using charged_core f hf hc

theorem schur_core_of_mean_deriv_zero (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (hb : (∫ y, deriv f y ∂law) = 0) :
    variance f law + (1 / 3 : ℝ) * (∫ y, (y - 1) * f y ∂law) ^ 2 ≤
      4 * (∫ y, (deriv f y) ^ 2 ∂law) := by
  have he := charged_core_of_mean_deriv_zero f hf hc hb
  nlinarith [sq_nonneg (∫ y, (y - 1) * f y ∂law)]

end KLSImprovement.Exponential

#print axioms KLSImprovement.Exponential.integral_deriv
#print axioms KLSImprovement.Exponential.two_charges_le
#print axioms KLSImprovement.Exponential.charged_core
#print axioms KLSImprovement.Exponential.poincare_core
#print axioms KLSImprovement.Exponential.charged_core_of_mean_deriv_zero
#print axioms KLSImprovement.Exponential.schur_core_of_mean_deriv_zero
