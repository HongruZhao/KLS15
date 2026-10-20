import KLS.WeakGradientExtraction
import KLS.WeightedFaithfulCutoff

/-! Uniformly bounded actual coefficient limits give strong L2 test
coefficients on a fixed measure. Used after compact localization. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace KLSConstantImprovement.ActualBoundedCoefficientL2Passage405
open KLS
variable {n : ℕ} {ν : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false

theorem tendsto_toLp_of_eLpNorm_sub_tendsto_zero_weighted
    {f : ℕ → Space n → ℝ} {u : Space n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 ν) (hu : MemLp u 2 ν)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun k => (hf k).toLp (f k)) atTop (𝓝 (hu.toLp u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm (k : ℕ) : ‖(hf k).toLp (f k) - hu.toLp u‖ =
      (eLpNorm (f k - u) 2 ν).toReal := by
    rw [← MemLp.toLp_sub, Lp.norm_toLp]
  simp_rw [hnorm]
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hconv

theorem bounded_coefficient_mul_tendsto_L2
    {a : ℕ → Space n → ℝ} {b f : Space n → ℝ} {B : ℝ}
    (ha : ∀ k, AEStronglyMeasurable (a k) ν) (hb : AEStronglyMeasurable b ν)
    (hB : 0 ≤ B) (hbound : ∀ k, ∀ᵐ x ∂ν, ‖a k x‖ ≤ B)
    (hbnd : ∀ᵐ x ∂ν, ‖b x‖ ≤ B)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun k => a k x) atTop (𝓝 (b x)))
    (hf : MemLp f 2 ν) :
    ∃ (hprod : ∀ k, MemLp (fun x => a k x * f x) 2 ν)
      (hlimit : MemLp (fun x => b x * f x) 2 ν),
      Tendsto (fun k => (hprod k).toLp (fun x => a k x * f x))
        atTop (𝓝 (hlimit.toLp (fun x => b x * f x))) := by
  have haTop (k : ℕ) : MemLp (a k) ∞ ν := memLp_top_of_bound (ha k) B (hbound k)
  have hbTop : MemLp b ∞ ν := memLp_top_of_bound hb B hbnd
  have hprod (k : ℕ) : MemLp (fun x => a k x * f x) 2 ν := (haTop k).mul hf
  have hlimit : MemLp (fun x => b x * f x) 2 ν := hbTop.mul hf
  have hdiff (k : ℕ) : MemLp (fun x => a k x * f x - b x * f x) 2 ν := (hprod k).sub hlimit
  have hf2 : Integrable (fun x => f x ^ 2) ν := by
    have hm := hf.integrable_mul hf
    change Integrable (fun x => f x * f x) ν at hm
    simpa only [pow_two] using hm
  have hmeas (k : ℕ) : AEStronglyMeasurable (fun x => (a k x * f x - b x * f x) ^ 2) ν :=
    (((ha k).mul hf.aestronglyMeasurable).sub (hb.mul hf.aestronglyMeasurable)).pow 2
  have hdom (k : ℕ) : ∀ᵐ x ∂ν,
      ‖(a k x * f x - b x * f x) ^ 2‖ ≤ (2 * B) ^ 2 * f x ^ 2 := by
    filter_upwards [hbound k, hbnd] with x hx hy
    have hn : ‖a k x - b x‖ ≤ 2 * B := (norm_sub_le _ _).trans (by linarith)
    have hs : (a k x - b x) ^ 2 ≤ (2 * B) ^ 2 := by
      have hh := (sq_le_sq₀ (norm_nonneg (a k x - b x)) (by positivity : 0 ≤ 2 * B)).mpr hn
      simpa only [Real.norm_eq_abs, sq_abs] using hh
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ = (a k x - b x) ^ 2 * f x ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hs (sq_nonneg (f x))
  have ht := tendsto_integral_of_dominated_convergence (fun x => (2 * B) ^ 2 * f x ^ 2)
    hmeas (hf2.const_mul ((2 * B) ^ 2)) hdom
    (show ∀ᵐ x ∂ν, Tendsto (fun k => (a k x * f x - b x * f x) ^ 2) atTop (𝓝 (0 : ℝ)) by
      filter_upwards [hlim] with x hx
      simpa only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        ((hx.mul_const (f x)).sub_const (b x * f x)).pow 2)
  have hsq : Tendsto (fun k => ∫ x, (a k x * f x - b x * f x) ^ 2 ∂ν) atTop (𝓝 0) := by
    simpa only [integral_zero] using ht
  have he := tendsto_eLpNorm_zero_of_integral_sq hdiff hsq
  refine ⟨hprod, hlimit, ?_⟩
  apply tendsto_toLp_of_eLpNorm_sub_tendsto_zero_weighted hprod hlimit
  change Tendsto (fun k => eLpNorm (fun x => a k x * f x - b x * f x) 2 ν) atTop (𝓝 0)
  exact he

end KLSConstantImprovement.ActualBoundedCoefficientL2Passage405
#print axioms KLSConstantImprovement.ActualBoundedCoefficientL2Passage405.tendsto_toLp_of_eLpNorm_sub_tendsto_zero_weighted
#print axioms KLSConstantImprovement.ActualBoundedCoefficientL2Passage405.bounded_coefficient_mul_tendsto_L2
