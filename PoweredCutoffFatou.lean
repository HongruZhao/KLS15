import LocalWeightedCutoffIntegrability
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! The literal Fatou endpoint of the powered-cutoff Caccioppoli argument.
No global L² premise is imposed on the top derivative. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators ENNReal
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n q : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

lemma aestronglyMeasurable_of_local_volume_memLp {f : Space n → ℝ}
    (hf : ∀ K : Set (Space n), IsCompact K → MemLp f 2 (volume.restrict K)) :
    AEStronglyMeasurable f volume := by
  have hm := AEStronglyMeasurable.iUnion (fun k : ℕ =>
    (hf (closedBall 0 (k : ℝ)) (isCompact_closedBall _ _)).aestronglyMeasurable)
  simpa only [iUnion_closedBall_nat,Measure.restrict_univ] using hm

lemma ae_eq_zero_of_powered_cutoff_norm_tendsto_zero
    {f : Space n → ℝ} (hf : AEStronglyMeasurable f μ) (q : ℕ)
    (hcut : ∀ k, MemLp (fun x => (smoothCutoff n k x)^q*f x) 2 μ)
    (hnorm : Tendsto (fun k => ‖(hcut k).toLp
      (fun x => (smoothCutoff n k x)^q*f x)‖) atTop (𝓝 0)) : f =ᵐ[μ] 0 := by
  have he : Tendsto (fun k => eLpNorm (fun x => (smoothCutoff n k x)^q*f x) 2 μ)
      atTop (𝓝 0) := by
    have hh := ENNReal.tendsto_ofReal hnorm
    simpa only [ENNReal.ofReal_zero,ofReal_norm,Lp.enorm_toLp] using hh
  have hp : ∀ᵐ x ∂μ, Tendsto (fun k => (smoothCutoff n k x)^q*f x) atTop (𝓝 (f x)) :=
    Eventually.of_forall fun x => by
      simpa only [one_pow,one_mul] using ((smoothCutoff_tendsto_one x).pow q).mul_const (f x)
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2)
    (fun k => (hcut k).aestronglyMeasurable) f hf hp
  rw [he.liminf_eq] at hfatou
  exact (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp (le_antisymm hfatou bot_le)

/-- The actual cutoff test and lower-jet L² bounds force every highest
ordered derivative to vanish almost everywhere. -/
theorem poweredCutoff_top_ae_zero
    (J : List (Fin n) → Space n → ℝ)
    (hJ : ∀ L, L.length < q → MemLp (J L) 2 μ)
    (hmeas : ∀ I : Fin q → Fin n, AEStronglyMeasurable (J (List.ofFn I)) μ)
    (hTop : ∀ k (I : Fin q → Fin n),
      MemLp (fun x => (smoothCutoff n k x)^q*J (List.ofFn I) x) 2 μ)
    (htest : ∀ k, (∑ I : Fin q → Fin n, ∫ x,
      J (List.ofFn I) x*poweredTensorCutoffJet J q k I x ∂μ)=0)
    (I : Fin q → Fin n) : J (List.ofFn I) =ᵐ[μ] 0 := by
  have hn := poweredCutoffTopTensor_norm_tendsto_zero J hJ hTop htest
  apply ae_eq_zero_of_powered_cutoff_norm_tendsto_zero (hmeas I) q (fun k => hTop k I)
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k =>
    PiLp.norm_apply_le (poweredCutoffTopTensor J q k (hTop k)) I) hn

/-- For an actual continuous potential, top local Lebesgue L² supplies
both measurability and compact weighted integrability internally. -/
theorem poweredCutoff_top_ae_zero_of_local_volume
    {φ : Space n → ℝ} (hφ : Continuous φ) (hq : q ≠ 0)
    (J : List (Fin n) → Space n → ℝ)
    (hJ : ∀ L, L.length < q → MemLp (J L) 2 (potentialMeasure φ))
    (hlocal : ∀ (I : Fin q → Fin n) (K : Set (Space n)), IsCompact K →
      MemLp (J (List.ofFn I)) 2 (volume.restrict K))
    (htest : ∀ k, (∑ I : Fin q → Fin n, ∫ x,
      J (List.ofFn I) x*poweredTensorCutoffJet J q k I x ∂potentialMeasure φ)=0)
    (I : Fin q → Fin n) : J (List.ofFn I) =ᵐ[potentialMeasure φ] 0 := by
  apply poweredCutoff_top_ae_zero J hJ
    (fun I => (aestronglyMeasurable_of_local_volume_memLp (hlocal I)).mono_ac
      (withDensity_absolutelyContinuous _ _))
    (fun k I => memLp_powered_top_of_local_volume hφ q hq k (hlocal I)) htest I

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.poweredCutoff_top_ae_zero
#print axioms KLS.DeterministicBridgeIntegration.poweredCutoff_top_ae_zero_of_local_volume
