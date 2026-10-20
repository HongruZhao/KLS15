import KLSConstantImprovement.ActualDensityGradientCoefficient405
import KLSConstantImprovement.ActualWeakPositivePart405
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Literal compact masks and strong compact square-root densities in the
fixed Lebesgue L2 ambient.  These are the tests used to pass actual inverse
excess estimates; no strong convergence of the inverse is required. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ENNReal
namespace KLSConstantImprovement.ActualCompactDensityHalf405
open KLS ActualDensityWeightedL2405 ActualBoundedCoefficientL2Passage405
open ActualHilbertWeakPassage405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ}

def maskLp {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (E : Set α) (hE : MeasurableSet E) (f : Lp ℝ 2 ν) : Lp ℝ 2 ν :=
  ((Lp.memLp f).indicator hE.nullMeasurableSet).toLp (E.indicator f)

theorem maskLp_ae {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (E : Set α) (hE : MeasurableSet E) (f : Lp ℝ 2 ν) :
    (maskLp E hE f : α → ℝ) =ᵐ[ν] E.indicator f :=
  ((Lp.memLp f).indicator hE.nullMeasurableSet).coeFn_toLp

theorem inner_maskLp {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (E : Set α) (hE : MeasurableSet E) (f z : Lp ℝ 2 ν) :
    inner ℝ (maskLp E hE f) z = inner ℝ f (maskLp E hE z) := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [maskLp_ae E hE f, maskLp_ae E hE z] with x hx hy
  simp only [RCLike.inner_apply, conj_trivial, hx, hy]
  by_cases h : x ∈ E
  · simp only [indicator_of_mem h]
  · simp only [indicator_of_notMem h, zero_mul, mul_zero]

theorem maskLp_weak_tendsto {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (E : Set α) (hE : MeasurableSet E)
    {f : ℕ → Lp ℝ 2 ν} {u : Lp ℝ 2 ν}
    (hw : ∀ z, Tendsto (fun k => inner ℝ (f k) z) atTop (𝓝 (inner ℝ u z))) :
    ∀ z, Tendsto (fun k => inner ℝ (maskLp E hE (f k)) z) atTop
      (𝓝 (inner ℝ (maskLp E hE u) z)) := by
  intro z
  simpa only [inner_maskLp] using hw (maskLp E hE z)

theorem memLp_compactDensityHalf (φ : Space n → ℝ) (hφ : Continuous φ)
    (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (E.indicator (densityHalf φ)) 2 (volume : Measure (Space n)) := by
  apply (memLp_indicator_iff_restrict hE.measurableSet.nullMeasurableSet).mpr
  exact memLp_two_on_compacts_of_top
    (fun K hK => memLp_top_restrict_compact_of_continuous
      (Real.continuous_exp.comp (hφ.neg.div_const 2)) hK) E hE

def compactDensityHalf (φ : Space n → ℝ) (hφ : Continuous φ)
    (E : Set (Space n)) (hE : IsCompact E) : Lp ℝ 2 (volume : Measure (Space n)) :=
  (memLp_compactDensityHalf φ hφ E hE).toLp (E.indicator (densityHalf φ))

theorem compactDensityHalf_ae (φ : Space n → ℝ) (hφ : Continuous φ)
    (E : Set (Space n)) (hE : IsCompact E) :
    (compactDensityHalf φ hφ E hE : Space n → ℝ) =ᵐ[volume]
      E.indicator (densityHalf φ) :=
  (memLp_compactDensityHalf φ hφ E hE).coeFn_toLp

theorem compact_densityHalf_tendsto_L2
    {φ : ℕ → Space n → ℝ} {φ₀ : Space n → ℝ}
    (hφ : ∀ k, Continuous (φ k)) (hφ₀ : Continuous φ₀)
    (hlim : ∀ x, Tendsto (fun k => φ k x) atTop (𝓝 (φ₀ x)))
    {A : ℝ} (ha : ∀ k x, A ≤ φ k x)
    (E : Set (Space n)) (hE : IsCompact E) :
    Tendsto (fun k => compactDensityHalf (φ k) (hφ k) E hE) atTop
      (𝓝 (compactDensityHalf φ₀ hφ₀ E hE)) := by
  let f : Space n → ℝ := E.indicator (fun _ => 1)
  have hf : MemLp f 2 (volume : Measure (Space n)) :=
    memLp_indicator_const 2 hE.measurableSet.nullMeasurableSet 1
      (Or.inr hE.measure_lt_top.ne)
  have hm (k : ℕ) : AEStronglyMeasurable (densityHalf (φ k)) volume :=
    (Real.continuous_exp.comp ((hφ k).neg.div_const 2)).aestronglyMeasurable
  have hm₀ : AEStronglyMeasurable (densityHalf φ₀) volume :=
    (Real.continuous_exp.comp (hφ₀.neg.div_const 2)).aestronglyMeasurable
  have hb (k : ℕ) : ∀ᵐ x ∂(volume : Measure (Space n)),
      ‖densityHalf (φ k) x‖ ≤ Real.exp (-A/2) := Eventually.of_forall fun x => by
    rw [densityHalf, Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr (by linarith [ha k x])
  have ht : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto
      (fun k => densityHalf (φ k) x) atTop (𝓝 (densityHalf φ₀ x)) :=
    Eventually.of_forall fun x =>
      (Real.continuous_exp.tendsto _).comp ((hlim x).neg.div_const 2)
  have hb₀ : ∀ᵐ x ∂(volume : Measure (Space n)),
      ‖densityHalf φ₀ x‖ ≤ Real.exp (-A/2) := by
    filter_upwards [ht, ae_all_iff.mpr hb] with x hx hy
    exact le_of_tendsto hx.norm (Eventually.of_forall hy)
  obtain ⟨hp, hl, hh⟩ := bounded_coefficient_mul_tendsto_L2 hm hm₀
    (Real.exp_nonneg _) hb hb₀ ht hf
  have he {ψ : Space n → ℝ} (hψ : Continuous ψ)
      (hprod : MemLp (fun x => densityHalf ψ x * f x) 2 volume) :
      hprod.toLp (fun x => densityHalf ψ x * f x) = compactDensityHalf ψ hψ E hE := by
    apply Lp.ext
    filter_upwards [hprod.coeFn_toLp, compactDensityHalf_ae ψ hψ E hE] with x hx hy
    rw [hx, hy]
    by_cases hs : x ∈ E
    · simp only [f, indicator_of_mem hs, mul_one]
    · simp only [f, indicator_of_notMem hs, mul_zero]
  rw [← he hφ₀ hl]
  exact hh.congr fun k => he (hφ k) (hp k)

end KLSConstantImprovement.ActualCompactDensityHalf405
#print axioms KLSConstantImprovement.ActualCompactDensityHalf405.maskLp_ae
#print axioms KLSConstantImprovement.ActualCompactDensityHalf405.inner_maskLp
#print axioms KLSConstantImprovement.ActualCompactDensityHalf405.maskLp_weak_tendsto
#print axioms KLSConstantImprovement.ActualCompactDensityHalf405.memLp_compactDensityHalf
#print axioms KLSConstantImprovement.ActualCompactDensityHalf405.compactDensityHalf_ae
#print axioms KLSConstantImprovement.ActualCompactDensityHalf405.compact_densityHalf_tendsto_L2
