import KLSConstantImprovement.ActualDensityFluxCoefficient405
import KLSConstantImprovement.ActualDensityGradientPair405

/-! Actual compact divergence-flux pairings through the common inverse
weak limit. All varying metric and density multipliers are the actual
ones; their strong compact-test convergence was proved separately. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
namespace KLSConstantImprovement.ActualDensityFluxPair405
open KLS ActualBoundedCanonicalSource ActualDensityWeightedL2405 ActualDensityInverseWeakCompactness405
open ActualDensityFluxCoefficient405 ActualDensityLimitInverseIdentification405
open ActualFiniteFamilyWeakPassage405 ActualHilbertWeakPassage405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricInverse
open ActualSourceNaturalGaffney405 ActualSourceLimitFluxDomains405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem source_flux_entry_density_pair (d : SourceData μ)
    (q : Lp ℝ 2 (potentialMeasure d.potential)) (i a : Fin n)
    {ψ : Space n → ℝ} (hc : HasCompactSupport ψ)
    (hcoef : MemLp (fun x => densityFluxCoefficient d (tsupport ψ) i a x * ψ x) 2 volume) :
    Integrable (fun x => canonicalMetricRoot d.potential x i a * q x * ψ x)
      (potentialMeasure d.potential) ∧
      (∫ x, canonicalMetricRoot d.potential x i a * q x * ψ x ∂potentialMeasure d.potential) =
        inner ℝ (toVolumeL2 d.source_C1.continuous q)
          (hcoef.toLp (fun x => densityFluxCoefficient d (tsupport ψ) i a x * ψ x)) := by
  have he (x : Space n) : (densityHalf d.potential x * q x) *
      (densityFluxCoefficient d (tsupport ψ) i a x * ψ x) =
      (canonicalMetricRoot d.potential x i a * q x * ψ x) * Real.exp (-d.potential x) := by
    by_cases hs : x ∈ tsupport ψ
    · rw [densityFluxCoefficient, indicator_of_mem hs]
      calc
        _ = densityHalf d.potential x ^ 2 * (canonicalMetricRoot d.potential x i a * q x * ψ x) := by ring
        _ = _ := by rw [densityHalf_square]; ring
    · rw [image_eq_zero_of_notMem_tsupport hs]
      ring
  have hi := (memLp_densityHalf_mul d.source_C1.continuous (Lp.memLp q)).integrable_mul hcoef
  refine ⟨(integrable_potentialMeasure_iff d.source_C1.continuous.measurable).mpr
    (hi.congr (Eventually.of_forall he)), ?_⟩
  rw [integral_potentialMeasure d.source_C1.continuous.measurable, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [toVolumeL2_ae d.source_C1.continuous q, hcoef.coeFn_toLp] with x hx hy
  simp only [RCLike.inner_apply, conj_trivial, hx, hy]
  nlinarith only [he x]

theorem source_flux_sum_density_pair (d : SourceData μ)
    (q : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) (i : Fin n)
    {ψ : Space n → ℝ} (hc : HasCompactSupport ψ)
    (hcoef : ∀ a, MemLp (fun x => densityFluxCoefficient d (tsupport ψ) i a x * ψ x) 2 volume) :
    (∫ x, (∑ a : Fin n, canonicalMetricRoot d.potential x i a * q a x) * ψ x
      ∂potentialMeasure d.potential) =
      ∑ a : Fin n, inner ℝ (toVolumeL2 d.source_C1.continuous (q a))
        ((hcoef a).toLp (fun x => densityFluxCoefficient d (tsupport ψ) i a x * ψ x)) := by
  have he : (fun x => (∑ a : Fin n, canonicalMetricRoot d.potential x i a * q a x) * ψ x) =
      fun x => ∑ a : Fin n, canonicalMetricRoot d.potential x i a * q a x * ψ x := by
    funext x
    rw [Finset.sum_mul]
  rw [he, integral_finsetSum _ (fun a _ => (source_flux_entry_density_pair d (q a) i a hc (hcoef a)).1)]
  exact Finset.sum_congr rfl fun a _ => (source_flux_entry_density_pair d (q a) i a hc (hcoef a)).2

theorem actual_natural_flux_pair_tendsto
    {ν : ℕ → Measure (Space n)} (d : ∀ k, SourceData (ν k)) (d₀ : SourceData μ)
    (g : ∀ k, Lp ℝ 2 (potentialMeasure (d k).potential))
    (W : DensityInverseAmbient n) {C κ L P A : ℝ}
    (hκ : 0 < κ) (hk : ∀ k, κ ≤ (d k).targetConvexityConstant)
    (hV : ∀ k p, L ≤ (d k).targetPotential p) (hA : ∀ k x, A ≤ (d k).potential x)
    (hφ : ∀ x, Tendsto (fun k => (d k).potential x) atTop (𝓝 (d₀.potential x)))
    (hH : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto
      (fun k => coordinateHessian (d k).potential x) atTop (𝓝 (coordinateHessian d₀.potential x)))
    (hb : ∀ k, ‖actualDensityInverseField (d k) (g k)‖ ≤ C)
    (hw : ∀ Y : DensityInverseAmbient n,
      Tendsto (fun k => inner ℝ (actualDensityInverseField (d k) (g k)) Y)
        atTop (𝓝 (inner ℝ W Y)))
    {ψ : Space n → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hp : ∀ k x, x ∈ tsupport ψ → (d k).potential x ≤ P) (i : Fin n) :
    Tendsto (fun k => ∫ x, naturalCanonicalFlux (d k) (g k) i x * ψ x ∂potentialMeasure (d k).potential)
      atTop (𝓝 (∫ x, energyLimitFlux d₀ (densityLimitMetricBlock d₀ W) i x * ψ x
        ∂potentialMeasure d₀.potential)) := by
  have htests (a : Fin n) := density_flux_coefficient_mul_tendsto_L2 d d₀ hκ hk hV hA hφ hH hc hp i a
    (hψ.memLp_of_hasCompactSupport hc)
  choose ha hl ht using htests
  have hpair (a : Fin n) : Tendsto (fun k => inner ℝ
      (toVolumeL2 (d k).source_C1.continuous
        (canonicalMetricGradient (d k).potential a (sourceMetricInverseH1 (d k) (g k))))
      ((ha a k).toLp (fun x => densityFluxCoefficient (d k) (tsupport ψ) i a x * ψ x))) atTop
      (𝓝 (inner ℝ (W a.succ)
        ((hl a).toLp (fun x => densityFluxCoefficient d₀ (tsupport ψ) i a x * ψ x)))) := by
    have hb' (k : ℕ) : ‖toVolumeL2 (d k).source_C1.continuous
        (canonicalMetricGradient (d k).potential a (sourceMetricInverseH1 (d k) (g k)))‖ ≤ C :=
      (PiLp.norm_apply_le (actualDensityInverseField (d k) (g k)) a.succ).trans (hb k)
    exact inner_tendsto_of_weak_and_strong hb'
      (fun Y => finite_family_weak_coordinate_tendsto hw a.succ Y) (ht a)
  have hlim := tendsto_finsetSum Finset.univ fun a _ => hpair a
  have hleft (k : ℕ) : (∫ x, naturalCanonicalFlux (d k) (g k) i x * ψ x
      ∂potentialMeasure (d k).potential) =
      ∑ a : Fin n, inner ℝ (toVolumeL2 (d k).source_C1.continuous
        (canonicalMetricGradient (d k).potential a (sourceMetricInverseH1 (d k) (g k))))
        ((ha a k).toLp (fun x => densityFluxCoefficient (d k) (tsupport ψ) i a x * ψ x)) :=
    source_flux_sum_density_pair (d k) (fun a => canonicalMetricGradient (d k).potential a
      (sourceMetricInverseH1 (d k) (g k))) i hc (fun a => ha a k)
  have hright : (∫ x, energyLimitFlux d₀ (densityLimitMetricBlock d₀ W) i x * ψ x
      ∂potentialMeasure d₀.potential) =
      ∑ a : Fin n, inner ℝ (W a.succ)
        ((hl a).toLp (fun x => densityFluxCoefficient d₀ (tsupport ψ) i a x * ψ x)) := by
    have he := source_flux_sum_density_pair d₀
      (fun a => fromVolumeL2 d₀.source_C1.continuous (W a.succ)) i hc hl
    simpa only [energyLimitFlux, densityLimitMetricBlock, PiLp.toLp_apply,
      Sum.elim_inl, toVolumeL2_fromVolumeL2] using he
  rw [hright]
  exact hlim.congr fun k => (hleft k).symm

end KLSConstantImprovement.ActualDensityFluxPair405
#print axioms KLSConstantImprovement.ActualDensityFluxPair405.source_flux_entry_density_pair
#print axioms KLSConstantImprovement.ActualDensityFluxPair405.source_flux_sum_density_pair
#print axioms KLSConstantImprovement.ActualDensityFluxPair405.actual_natural_flux_pair_tendsto
