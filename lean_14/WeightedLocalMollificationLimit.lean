import KLS.WeightedCompactSmoothing
import KLS.WeightedAnnihilatorEnergy
import KLS.PoincareGraphLimit

/-! Local L² approximation with the actual potential weight. Compact
localization requires no global unweighted L² assumption. -/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ}

theorem memLp_potentialMeasure_of_memLp_volume_compact {φ f : Space n → ℝ}
    (hφ : Continuous φ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    MemLp f 2 (potentialMeasure φ) := by
  obtain ⟨χ, hχ, hχc, hone⟩ := exists_smooth_compact_one_on_compact hc
  have hm := memLp_compact_mul_volume_to_weighted hφ hχ.continuous hχc (hf.toLp f)
  apply (memLp_congr_ae ?_).mp hm
  filter_upwards [(withDensity_absolutelyContinuous volume
    (fun x => ENNReal.ofReal (Real.exp (-φ x)))).ae_eq hf.coeFn_toLp] with x hx
  rw [hx]
  by_cases hxf : x ∈ tsupport f
  · rw [hone x hxf, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hxf, mul_zero]

theorem memLp_compact_mul_local_potential {φ χ f : Space n → ℝ}
    (hφ : Continuous φ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hf : ∀ K : Set (Space n), IsCompact K → MemLp f 2 (volume.restrict K)) :
    MemLp (fun x => χ x * f x) 2 (potentialMeasure φ) :=
  memLp_potentialMeasure_of_memLp_volume_compact hφ
    (memLp_compact_mul_of_local hχ hc hf) hc.mul_right

/-- Genuine compactly localized mollification converges in weighted L²,
even when the input is only locally Lebesgue L². -/
theorem eLpNorm_compact_mul_mollify_sub_potential_tendsto_zero
    {φ χ f : Space n → ℝ} (hφ : Continuous φ)
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hf : ∀ K : Set (Space n), IsCompact K → MemLp f 2 (volume.restrict K)) :
    Tendsto (fun k => eLpNorm (fun x => χ x * mollify k f x - χ x * f x)
      2 (potentialMeasure φ)) atTop (𝓝 0) := by
  have hfloc := locallyIntegrable_of_memLp_two_on_compacts hf
  have hmk (k : ℕ) : Continuous (mollify k f) := (mollify_contDiff hfloc k).continuous
  exact eLpNorm_potentialMeasure_sub_tendsto_zero_of_compact_support hφ hc
    (fun _ => tsupport_mul_subset_left) tsupport_mul_subset_left
    (fun k => (hχ.mul (hmk k)).memLp_of_hasCompactSupport hc.mul_right)
    (memLp_compact_mul_of_local hχ hc hf)
    (fun k => memLp_of_continuous_hasCompactSupport hφ
      (hχ.mul (hmk k)) hc.mul_right)
    (memLp_compact_mul_local_potential hφ hχ hc hf)
    (eLpNorm_compact_mul_mollify_sub_tendsto_zero hχ hc hf)

/-- Strong L² convergence controls actual squared-integral energies. -/
theorem tendsto_integral_sq_of_eLpNorm_sub_tendsto_zero
    {μ : Measure (Space n)} {f : ℕ → Space n → ℝ} {g : Space n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : MemLp g 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, (f k x) ^ 2 ∂μ) atTop (𝓝 (∫ x, (g x) ^ 2 ∂μ)) := by
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mpr hconv
  have hn := ht.norm.pow 2
  simpa only [← integral_sq_eq_norm_toLp_sq] using hn

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.eLpNorm_compact_mul_mollify_sub_potential_tendsto_zero
#print axioms KLS.DeterministicBridgeIntegration.tendsto_integral_sq_of_eLpNorm_sub_tendsto_zero
