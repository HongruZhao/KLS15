import KLS.TensorIntegralCauchySchwarz

/-! A true global boundary limit from its paid square domination. This
lemma preserves both positive energy integrals and assumes no pointwise
uniform cutoff-gradient bound. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace KLSConstantImprovement.ActualSquareDominatedBoundaryLimit405
open KLS.TensorEnergy
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

theorem integral_abs_le_sqrt_of_square_bound {b e q : X → ℝ}
    (hb : Integrable b ν) (he : Integrable e ν) (hq : Integrable q ν)
    (hs : ∀ᵐ x ∂ν, b x ^ 2 ≤ e x * q x) :
    (∫ x, |b x| ∂ν) ≤ Real.sqrt (∫ x, |e x| ∂ν) * Real.sqrt (∫ x, |q x| ∂ν) := by
  obtain ⟨hprod, hcs⟩ := integral_sqrt_mul_le he.abs hq.abs
    (fun x => abs_nonneg (e x)) (fun x => abs_nonneg (q x))
  apply (integral_mono_ae hb.abs hprod ?_).trans hcs
  filter_upwards [hs] with x hx
  have hp : e x * q x ≤ |e x| * |q x| := by simpa only [abs_mul] using le_abs_self (e x * q x)
  have hroot : (Real.sqrt |e x| * Real.sqrt |q x|) ^ 2 = |e x| * |q x| := by
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _), Real.sq_sqrt (abs_nonneg _)]
  nlinarith [sq_abs (b x), abs_nonneg (b x),
    mul_nonneg (Real.sqrt_nonneg |e x|) (Real.sqrt_nonneg |q x|)]

theorem integral_tendsto_zero_of_square_domination {b e : ℕ → X → ℝ} {q : X → ℝ}
    (hb : ∀ k, Integrable (b k) ν) (he : ∀ k, Integrable (e k) ν) (hq : Integrable q ν)
    (he0 : ∀ k, ∀ᵐ x ∂ν, 0 ≤ e k x) (hq0 : ∀ᵐ x ∂ν, 0 ≤ q x)
    (hs : ∀ k, ∀ᵐ x ∂ν, b k x ^ 2 ≤ e k x * q x)
    (helim : Tendsto (fun k => ∫ x, e k x ∂ν) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, |b k x| ∂ν) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ x, b k x ∂ν) atTop (𝓝 0) := by
  have heq (k : ℕ) : (∫ x, |e k x| ∂ν) = ∫ x, e k x ∂ν :=
    integral_congr_ae ((he0 k).mono fun _ hx => abs_of_nonneg hx)
  have hqe : (∫ x, |q x| ∂ν) = ∫ x, q x ∂ν :=
    integral_congr_ae (hq0.mono fun _ hx => abs_of_nonneg hx)
  have hbound (k : ℕ) : (∫ x, |b k x| ∂ν) ≤
      Real.sqrt (∫ x, e k x ∂ν) * Real.sqrt (∫ x, q x ∂ν) := by
    have hh := integral_abs_le_sqrt_of_square_bound (hb k) (he k) hq (hs k)
    rwa [heq k, hqe] at hh
  have hright : Tendsto (fun k => Real.sqrt (∫ x, e k x ∂ν) * Real.sqrt (∫ x, q x ∂ν))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero, zero_mul] using
      ((Real.continuous_sqrt.continuousAt.tendsto.comp helim).mul_const (Real.sqrt (∫ x, q x ∂ν)))
  have habs : Tendsto (fun k => ∫ x, |b k x| ∂ν) atTop (𝓝 0) :=
    squeeze_zero (fun k => integral_nonneg fun x => abs_nonneg (b k x)) hbound hright
  refine ⟨habs, squeeze_zero_norm (fun k => ?_) habs⟩
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f := b k) (μ := ν)

end KLSConstantImprovement.ActualSquareDominatedBoundaryLimit405
#print axioms KLSConstantImprovement.ActualSquareDominatedBoundaryLimit405.integral_abs_le_sqrt_of_square_bound
#print axioms KLSConstantImprovement.ActualSquareDominatedBoundaryLimit405.integral_tendsto_zero_of_square_domination
