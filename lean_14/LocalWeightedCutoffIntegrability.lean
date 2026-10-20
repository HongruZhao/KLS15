import PoweredCutoffCaccioppoli
import KLS.WeightedCompactL2Maps

/-! Compact multiplication of literal locally square-integrable functions
into the actual potential measure. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n : ℕ} {φ χ f : Space n → ℝ}
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

lemma memLp_compact_mul_local_volume_to_weighted
    (hφ : Continuous φ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hf : ∀ K : Set (Space n), IsCompact K → MemLp f 2 (volume.restrict K)) :
    MemLp (fun x => χ x*f x) 2 (potentialMeasure φ) := by
  have hfi : MemLp ((tsupport χ).indicator f) 2 volume :=
    (memLp_indicator_iff_restrict hc.measurableSet.nullMeasurableSet).mpr (hf _ hc)
  let u := hfi.toLp ((tsupport χ).indicator f)
  have hm := memLp_compact_mul_volume_to_weighted hφ hχ hc u
  refine MemLp.ae_eq (hf_Lp := hm) ?_
  have he : (u : Space n → ℝ) =ᵐ[potentialMeasure φ] (tsupport χ).indicator f :=
    (withDensity_absolutelyContinuous _ _).ae_eq hfi.coeFn_toLp
  filter_upwards [he] with x hx
  rw [hx]
  by_cases hxK : x ∈ tsupport χ
  · simp [hxK]
  · simp [hxK,image_eq_zero_of_notMem_tsupport hxK]

lemma smoothCutoff_pow_hasCompactSupport (q : ℕ) (hq : q ≠ 0) (k : ℕ) :
    HasCompactSupport (fun x : Space n => (smoothCutoff n k x)^q) :=
  (smoothCutoff_hasCompactSupport k).comp_left (zero_pow hq)

lemma memLp_powered_top_of_local_volume
    (hφ : Continuous φ) (q : ℕ) (hq : q ≠ 0) (k : ℕ)
    (hf : ∀ K : Set (Space n), IsCompact K → MemLp f 2 (volume.restrict K)) :
    MemLp (fun x => (smoothCutoff n k x)^q*f x) 2 (potentialMeasure φ) :=
  memLp_compact_mul_local_volume_to_weighted hφ ((smoothCutoff_contDiff k).continuous.pow q)
    (smoothCutoff_pow_hasCompactSupport q hq k) hf

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.memLp_powered_top_of_local_volume
