import KLSConstantImprovement.ActualPotentialWeakTests405

/-! Compact raw H1 tests need no value bound when the actual divergence
right hand side is locally L2. Both the value and derivative pairings pass
through the same actual compact mollifiers. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualCompactRawH1L2Tests405
open KLS ActualBoundedCanonicalSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {n : ℕ} {μ : Measure (Space n)}

theorem compact_raw_value_localL2_pairing_mollify
    {f b : Space n → ℝ} (hf : MemLp f 2 volume) (hc : HasCompactSupport f)
    (hb : ∀ E, IsCompact E → MemLp b 2 (volume.restrict E)) :
    Integrable (fun x => b x * f x) volume ∧
      Tendsto (fun k => ∫ x, b x * mollify k f x) atTop (𝓝 (∫ x, b x * f x)) := by
  let S := mollifierEnlargement (tsupport f)
  have hS : IsCompact S := isCompact_mollifierEnlargement hc
  have hb2 : MemLp (S.indicator b) 2 volume :=
    (memLp_indicator_iff_restrict hS.measurableSet.nullMeasurableSet).mpr (hb S hS)
  have heq {v : Space n → ℝ} (hvs : tsupport v ⊆ S) :
      (fun x => S.indicator b x * v x) =ᵐ[volume] (fun x => b x * v x) := by
    exact Eventually.of_forall fun x => by
      change S.indicator b x * v x = b x * v x
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
      · have hz : v x = 0 := image_eq_zero_of_notMem_tsupport fun ht => hx (hvs ht)
        rw [hz, mul_zero, mul_zero]
  have hi := (hb2.integrable_mul hf).congr (heq (subset_mollifierEnlargement (tsupport f)))
  have ht := tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero (fun k => memLp_mollify hf k)
    hf hb2 (eLpNorm_mollify_sub_tendsto_zero hf)
  have he (k : ℕ) : (∫ x, S.indicator b x * mollify k f x) =
      ∫ x, b x * mollify k f x := integral_congr_ae (heq (tsupport_mollify_subset hc k))
  exact ⟨hi, by simpa only [he, integral_congr_ae (heq (subset_mollifierEnlargement (tsupport f)))] using ht⟩

theorem integral_divergence_compact_raw_H1_L2_test
    {A : Fin n → Space n → ℝ} {b f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hA : ∀ i E, IsCompact E → MemLp (A i) 2 (volume.restrict E))
    (hb : ∀ E, IsCompact E → MemLp b 2 (volume.restrict E))
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∑ i, ∫ x, A i x * coordinateDerivative ψ i x) = ∫ x, b x * ψ x)
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E))
    (hc : HasCompactSupport f)
    (hFloc : ∀ i E, IsCompact E → MemLp (F i) 2 (volume.restrict E))
    (hF : ∀ i, HasLocalWeakCoordinateDerivative f (F i) i) :
    (∀ i, Integrable (fun x => A i x * F i x)) ∧ Integrable (fun x => b x * f x) ∧
      (∑ i, ∫ x, A i x * F i x) = ∫ x, b x * f x := by
  have hf2 := memLp_compact_of_localL2 hf hc
  have hp (i : Fin n) := (hF i).localL2_pairing_mollify hf2 hc (hFloc i) (hA i)
  have hr := compact_raw_value_localL2_pairing_mollify hf2 hc hb
  refine ⟨fun i => (hp i).1, hr.1, ?_⟩
  have hl := tendsto_finsetSum Finset.univ fun i _ => (hp i).2
  have he : (fun k => ∑ i, ∫ x, A i x * coordinateDerivative (mollify k f) i x) =
      fun k => ∫ x, b x * mollify k f x := by
    funext k
    exact hdiv _ ((mollify_contDiff (hf2.locallyIntegrable (by norm_num)) k).of_le (by simp))
      (hasCompactSupport_mollify hc k)
  rw [he] at hl
  exact tendsto_nhds_unique hl hr.2

theorem potential_divergence_compact_raw_H1_L2_test (d : SourceData μ)
    {A : Fin n → Space n → ℝ} {b f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hA : ∀ i E, IsCompact E → MemLp (A i) 2 (volume.restrict E))
    (hb : ∀ E, IsCompact E → MemLp b 2 (volume.restrict E))
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∑ i, ∫ x, A i x * coordinateDerivative ψ i x ∂potentialMeasure d.potential) =
        ∫ x, b x * ψ x ∂potentialMeasure d.potential)
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E))
    (hc : HasCompactSupport f)
    (hFloc : ∀ i E, IsCompact E → MemLp (F i) 2 (volume.restrict E))
    (hF : ∀ i, HasLocalWeakCoordinateDerivative f (F i) i) :
    (∀ i, Integrable (fun x => A i x * F i x) (potentialMeasure d.potential)) ∧
      Integrable (fun x => b x * f x) (potentialMeasure d.potential) ∧
      (∑ i, ∫ x, A i x * F i x ∂potentialMeasure d.potential) =
        ∫ x, b x * f x ∂potentialMeasure d.potential := by
  have hρ : Continuous (fun x => Real.exp (-d.potential x)) :=
    Real.continuous_exp.comp d.source_C1.continuous.neg
  have hρA (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => Real.exp (-d.potential x) * A i x) 2 (volume.restrict E) :=
    memLp_continuous_mul_on_compact hE (hA i E hE) hρ
  have hρb (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => Real.exp (-d.potential x) * b x) 2 (volume.restrict E) :=
    memLp_continuous_mul_on_compact hE (hb E hE) hρ
  have he := integral_divergence_compact_raw_H1_L2_test hρA hρb
    (fun ψ hψ hψc => by
      have ht := hdiv ψ hψ hψc
      simp_rw [integral_potentialMeasure d.source_C1.continuous.measurable] at ht
      simpa only [mul_assoc, mul_left_comm, mul_comm] using ht) hf hc hFloc hF
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply (integrable_potentialMeasure_iff d.source_C1.continuous.measurable).mpr
    exact (he.1 i).congr (Eventually.of_forall fun x => by dsimp only; ring)
  · apply (integrable_potentialMeasure_iff d.source_C1.continuous.measurable).mpr
    exact he.2.1.congr (Eventually.of_forall fun x => by dsimp only; ring)
  · simp_rw [integral_potentialMeasure d.source_C1.continuous.measurable]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using he.2.2

end KLSConstantImprovement.ActualCompactRawH1L2Tests405
#print axioms KLSConstantImprovement.ActualCompactRawH1L2Tests405.compact_raw_value_localL2_pairing_mollify
#print axioms KLSConstantImprovement.ActualCompactRawH1L2Tests405.integral_divergence_compact_raw_H1_L2_test
#print axioms KLSConstantImprovement.ActualCompactRawH1L2Tests405.potential_divergence_compact_raw_H1_L2_test
