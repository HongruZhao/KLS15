import KLSConstantImprovement.ActualDensityGradientCoefficient405
import KLSConstantImprovement.ActualDensityLimitInverseIdentification405
import KLSConstantImprovement.ActualFiniteFamilyWeakPassage405
import KLSConstantImprovement.ActualSourceNaturalHessian405

/-! The actual raw inverse-gradient compact pairings pass through the
common density-weighted weak limit.  Strong coefficients come from the
genuine source-family Hessians and potentials; no inverse equation is a
free input to this passage. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
namespace KLSConstantImprovement.ActualDensityGradientPair405
open KLS ActualBoundedCanonicalSource ActualDensityWeightedL2405 ActualDensityInverseWeakCompactness405
open ActualDensityGradientCoefficient405 ActualDensityLimitInverseIdentification405
open ActualFiniteFamilyWeakPassage405 ActualHilbertWeakPassage405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricInverse
open ActualWeakCanonicalMetricOrdinaryGraph
open ActualSourceNaturalTargetCurvatureDomain405 ActualSourceNaturalHessian405
open ActualSourceLimitFluxDomains405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem raw_gradient_entry_density_pair (d : SourceData μ)
    (q : Lp ℝ 2 (potentialMeasure d.potential)) (i a : Fin n)
    {ψ : Space n → ℝ} (hc : HasCompactSupport ψ)
    (hcoef : MemLp (fun x => densityGradientCoefficient d (tsupport ψ) i a x * ψ x) 2 volume) :
    Integrable (fun x => canonicalMetricUnroot d.potential x i a * q x * ψ x) volume ∧
      (∫ x, canonicalMetricUnroot d.potential x i a * q x * ψ x) =
        inner ℝ (toVolumeL2 d.source_C1.continuous q)
          (hcoef.toLp (fun x => densityGradientCoefficient d (tsupport ψ) i a x * ψ x)) := by
  have he (x : Space n) : (densityHalf d.potential x * q x) *
      (densityGradientCoefficient d (tsupport ψ) i a x * ψ x) =
      canonicalMetricUnroot d.potential x i a * q x * ψ x := by
    by_cases hs : x ∈ tsupport ψ
    · rw [densityGradientCoefficient, indicator_of_mem hs]
      calc
        _ = (densityHalf d.potential x * inverseDensityHalf d.potential x) *
          (canonicalMetricUnroot d.potential x i a * q x * ψ x) := by ring
        _ = _ := by rw [densityHalf_inverseDensityHalf, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hs]
      ring
  refine ⟨((memLp_densityHalf_mul d.source_C1.continuous (Lp.memLp q)).integrable_mul hcoef).congr
    (Eventually.of_forall he), ?_⟩
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [toVolumeL2_ae d.source_C1.continuous q, hcoef.coeFn_toLp] with x hx hy
  simp only [RCLike.inner_apply, conj_trivial, hx, hy]
  nlinarith only [he x]

theorem raw_gradient_sum_density_pair (d : SourceData μ)
    (q : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) (i : Fin n)
    {ψ : Space n → ℝ} (hc : HasCompactSupport ψ)
    (hcoef : ∀ a, MemLp (fun x => densityGradientCoefficient d (tsupport ψ) i a x * ψ x) 2 volume) :
    (∫ x, (∑ a : Fin n, canonicalMetricUnroot d.potential x i a * q a x) * ψ x) =
      ∑ a : Fin n, inner ℝ (toVolumeL2 d.source_C1.continuous (q a))
        ((hcoef a).toLp (fun x => densityGradientCoefficient d (tsupport ψ) i a x * ψ x)) := by
  have he : (fun x => (∑ a : Fin n, canonicalMetricUnroot d.potential x i a * q a x) * ψ x) =
      fun x => ∑ a : Fin n, canonicalMetricUnroot d.potential x i a * q a x * ψ x := by
    funext x
    rw [Finset.sum_mul]
  rw [he, integral_finsetSum _ (fun a _ => (raw_gradient_entry_density_pair d (q a) i a hc (hcoef a)).1)]
  exact Finset.sum_congr rfl fun a _ => (raw_gradient_entry_density_pair d (q a) i a hc (hcoef a)).2

theorem actual_raw_gradient_pair_tendsto
    {ν : ℕ → Measure (Space n)} (d : ∀ k, SourceData (ν k)) (d₀ : SourceData μ)
    (g : ∀ k, Lp ℝ 2 (potentialMeasure (d k).potential))
    (W : DensityInverseAmbient n) {C κ P : ℝ}
    (hκ : 0 < κ) (hk : ∀ k, κ ≤ (d k).targetConvexityConstant)
    (hφ : ∀ x, Tendsto (fun k => (d k).potential x) atTop (𝓝 (d₀.potential x)))
    (hH : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto
      (fun k => coordinateHessian (d k).potential x) atTop (𝓝 (coordinateHessian d₀.potential x)))
    (hb : ∀ k, ‖actualDensityInverseField (d k) (g k)‖ ≤ C)
    (hw : ∀ Y : DensityInverseAmbient n,
      Tendsto (fun k => inner ℝ (actualDensityInverseField (d k) (g k)) Y)
        atTop (𝓝 (inner ℝ W Y)))
    {ψ : Space n → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hp : ∀ k x, x ∈ tsupport ψ → (d k).potential x ≤ P) (i : Fin n) :
    Tendsto (fun k => ∫ x, naturalCanonicalRawGradient (d k) (g k) i x * ψ x) atTop
      (𝓝 (∫ x, densityLimitRawGradient d₀ W i x * ψ x)) := by
  have htests (a : Fin n) := density_gradient_coefficient_mul_tendsto_L2 d d₀ hκ hk hφ hH hc hp i a
    (hψ.memLp_of_hasCompactSupport hc)
  choose ha hl ht using htests
  have hpair (a : Fin n) : Tendsto (fun k => inner ℝ
      (toVolumeL2 (d k).source_C1.continuous
        (canonicalMetricGradient (d k).potential a (sourceMetricInverseH1 (d k) (g k))))
      ((ha a k).toLp (fun x => densityGradientCoefficient (d k) (tsupport ψ) i a x * ψ x))) atTop
      (𝓝 (inner ℝ (W a.succ)
        ((hl a).toLp (fun x => densityGradientCoefficient d₀ (tsupport ψ) i a x * ψ x)))) := by
    have hb' (k : ℕ) : ‖toVolumeL2 (d k).source_C1.continuous
        (canonicalMetricGradient (d k).potential a (sourceMetricInverseH1 (d k) (g k)))‖ ≤ C :=
      (PiLp.norm_apply_le (actualDensityInverseField (d k) (g k)) a.succ).trans (hb k)
    have hw' (Y : Lp ℝ 2 (volume : Measure (Space n))) : Tendsto (fun k => inner ℝ
        (toVolumeL2 (d k).source_C1.continuous
          (canonicalMetricGradient (d k).potential a (sourceMetricInverseH1 (d k) (g k)))) Y) atTop
        (𝓝 (inner ℝ (W a.succ) Y)) :=
      finite_family_weak_coordinate_tendsto hw a.succ Y
    exact inner_tendsto_of_weak_and_strong hb' hw' (ht a)
  have hlim := tendsto_finsetSum Finset.univ fun a _ => hpair a
  have hleft (k : ℕ) : (∫ x, naturalCanonicalRawGradient (d k) (g k) i x * ψ x) =
      ∑ a : Fin n, inner ℝ (toVolumeL2 (d k).source_C1.continuous
        (canonicalMetricGradient (d k).potential a (sourceMetricInverseH1 (d k) (g k))))
        ((ha a k).toLp (fun x => densityGradientCoefficient (d k) (tsupport ψ) i a x * ψ x)) :=
    raw_gradient_sum_density_pair (d k) (fun a => canonicalMetricGradient (d k).potential a
      (sourceMetricInverseH1 (d k) (g k))) i hc (fun a => ha a k)
  have hright : (∫ x, densityLimitRawGradient d₀ W i x * ψ x) =
      ∑ a : Fin n, inner ℝ (W a.succ)
        ((hl a).toLp (fun x => densityGradientCoefficient d₀ (tsupport ψ) i a x * ψ x)) := by
    have he := raw_gradient_sum_density_pair d₀
      (fun a => fromVolumeL2 d₀.source_C1.continuous (W a.succ)) i hc hl
    simpa only [densityLimitRawGradient, energyLimitScalarGradient, densityLimitMetricBlock,
      PiLp.toLp_apply, Sum.elim_inl, toVolumeL2_fromVolumeL2] using he
  rw [hright]
  exact hlim.congr fun k => (hleft k).symm

end KLSConstantImprovement.ActualDensityGradientPair405
#print axioms KLSConstantImprovement.ActualDensityGradientPair405.raw_gradient_entry_density_pair
#print axioms KLSConstantImprovement.ActualDensityGradientPair405.raw_gradient_sum_density_pair
#print axioms KLSConstantImprovement.ActualDensityGradientPair405.actual_raw_gradient_pair_tendsto
