import KLSConstantImprovement.ActualDensityWeightedL2405
import KLSConstantImprovement.ActualBoundedCoefficientL2Passage405
import KLSConstantImprovement.ActualHilbertWeakPassage405

/-! Actual local scalar pairings pass through the common density-weighted
Hilbert limit. The varying compact coefficients are paid by their true
potential convergence and a common compact upper bound. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ENNReal
namespace KLSConstantImprovement.ActualDensityWeakScalarPair405
open KLS ActualDensityWeightedL2405 ActualBoundedCoefficientL2Passage405 ActualHilbertWeakPassage405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ}

def compactInverseDensityHalf (φ : Space n → ℝ) (E : Set (Space n)) : Space n → ℝ :=
  E.indicator (inverseDensityHalf φ)

theorem compact_inverse_density_test_tendsto
    {φ : ℕ → Space n → ℝ} {φ₀ ψ : Space n → ℝ}
    (hφ : ∀ k, Continuous (φ k)) (hφ₀ : Continuous φ₀)
    (hlim : ∀ x, Tendsto (fun k => φ k x) atTop (𝓝 (φ₀ x)))
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    {P : ℝ} (hp : ∀ k x, x ∈ tsupport ψ → φ k x ≤ P) :
    ∃ (ha : ∀ k, MemLp (fun x => compactInverseDensityHalf (φ k) (tsupport ψ) x * ψ x) 2 volume)
      (hb : MemLp (fun x => compactInverseDensityHalf φ₀ (tsupport ψ) x * ψ x) 2 volume),
      Tendsto (fun k => (ha k).toLp
        (fun x => compactInverseDensityHalf (φ k) (tsupport ψ) x * ψ x)) atTop
        (𝓝 (hb.toLp (fun x => compactInverseDensityHalf φ₀ (tsupport ψ) x * ψ x))) := by
  have hm (k : ℕ) : AEStronglyMeasurable (compactInverseDensityHalf (φ k) (tsupport ψ))
      (volume : Measure (Space n)) := by
    exact ((Real.continuous_exp.comp ((hφ k).div_const 2)).aestronglyMeasurable).indicator hc.measurableSet
  have hm₀ : AEStronglyMeasurable (compactInverseDensityHalf φ₀ (tsupport ψ))
      (volume : Measure (Space n)) := by
    exact ((Real.continuous_exp.comp (hφ₀.div_const 2)).aestronglyMeasurable).indicator hc.measurableSet
  have hb (k : ℕ) : ∀ᵐ x ∂(volume : Measure (Space n)),
      ‖compactInverseDensityHalf (φ k) (tsupport ψ) x‖ ≤ Real.exp (P/2) :=
    Eventually.of_forall fun x => by
      by_cases hx : x ∈ tsupport ψ
      · rw [compactInverseDensityHalf, indicator_of_mem hx, inverseDensityHalf,
          Real.norm_of_nonneg (Real.exp_nonneg _)]
        exact Real.exp_le_exp.mpr (by linarith [hp k x hx])
      · rw [compactInverseDensityHalf, indicator_of_notMem hx, norm_zero]
        exact Real.exp_nonneg _
  have ht : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto
      (fun k => compactInverseDensityHalf (φ k) (tsupport ψ) x) atTop
      (𝓝 (compactInverseDensityHalf φ₀ (tsupport ψ) x)) := Eventually.of_forall fun x => by
    by_cases hx : x ∈ tsupport ψ
    · simp only [compactInverseDensityHalf, indicator_of_mem hx, inverseDensityHalf]
      exact (Real.continuous_exp.tendsto _).comp ((hlim x).div_const 2)
    · simp only [compactInverseDensityHalf, indicator_of_notMem hx]
      exact tendsto_const_nhds
  have hb₀ : ∀ᵐ x ∂(volume : Measure (Space n)),
      ‖compactInverseDensityHalf φ₀ (tsupport ψ) x‖ ≤ Real.exp (P/2) := by
    filter_upwards [ht, ae_all_iff.mpr hb] with x hx hy
    exact le_of_tendsto hx.norm (Eventually.of_forall hy)
  exact bounded_coefficient_mul_tendsto_L2 hm hm₀ (Real.exp_nonneg _) hb hb₀ ht
    (hψ.memLp_of_hasCompactSupport hc)

theorem integral_raw_pair_eq_density_inner {φ ψ : Space n → ℝ}
    (hφ : Continuous φ) (f : Lp ℝ 2 (potentialMeasure φ))
    (hψ : HasCompactSupport ψ)
    (hc : MemLp (fun x => compactInverseDensityHalf φ (tsupport ψ) x * ψ x) 2 volume) :
    (∫ x, f x * ψ x) = inner ℝ (toVolumeL2 hφ f)
      (hc.toLp (fun x => compactInverseDensityHalf φ (tsupport ψ) x * ψ x)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [toVolumeL2_ae hφ f, hc.coeFn_toLp] with x hx hy
  simp only [RCLike.inner_apply, conj_trivial, hx, hy]
  by_cases hs : x ∈ tsupport ψ
  · rw [compactInverseDensityHalf, indicator_of_mem hs]
    symm
    calc
      _ = (densityHalf φ x * inverseDensityHalf φ x) * (f x * ψ x) := by ring
      _ = _ := by rw [densityHalf_inverseDensityHalf, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hs]
    ring

theorem raw_scalar_pair_tendsto_of_density_weak
    {φ : ℕ → Space n → ℝ} {φ₀ ψ : Space n → ℝ}
    (hφ : ∀ k, Continuous (φ k)) (hφ₀ : Continuous φ₀)
    (hlim : ∀ x, Tendsto (fun k => φ k x) atTop (𝓝 (φ₀ x)))
    (f : ∀ k, Lp ℝ 2 (potentialMeasure (φ k)))
    (U : Lp ℝ 2 (volume : Measure (Space n)))
    {C P : ℝ} (hf : ∀ k, ‖f k‖ ≤ C)
    (hw : ∀ Y : Lp ℝ 2 (volume : Measure (Space n)),
      Tendsto (fun k => inner ℝ (toVolumeL2 (hφ k) (f k)) Y) atTop (𝓝 (inner ℝ U Y)))
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hp : ∀ k x, x ∈ tsupport ψ → φ k x ≤ P) :
    Tendsto (fun k => ∫ x, f k x * ψ x) atTop
      (𝓝 (∫ x, fromVolumeL2 hφ₀ U x * ψ x)) := by
  obtain ⟨ha, hb, ht⟩ := compact_inverse_density_test_tendsto hφ hφ₀ hlim hψ hc hp
  have hnorm (k : ℕ) : ‖toVolumeL2 (hφ k) (f k)‖ ≤ C := by rw [toVolumeL2_norm]; exact hf k
  have hh := inner_tendsto_of_weak_and_strong hnorm hw ht
  rw [integral_raw_pair_eq_density_inner hφ₀ (fromVolumeL2 hφ₀ U) hc hb,
    toVolumeL2_fromVolumeL2]
  exact hh.congr fun k => (integral_raw_pair_eq_density_inner (hφ k) (f k) hc (ha k)).symm

end KLSConstantImprovement.ActualDensityWeakScalarPair405
#print axioms KLSConstantImprovement.ActualDensityWeakScalarPair405.compact_inverse_density_test_tendsto
#print axioms KLSConstantImprovement.ActualDensityWeakScalarPair405.integral_raw_pair_eq_density_inner
#print axioms KLSConstantImprovement.ActualDensityWeakScalarPair405.raw_scalar_pair_tendsto_of_density_weak
