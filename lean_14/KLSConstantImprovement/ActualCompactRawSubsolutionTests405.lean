import KLSConstantImprovement.ActualBoundedCanonicalSource
import KLS.CompactRawWeakDerivative
import KLS.MollifiedCompactTests
import KLS.LocalL2CompactPairings

/-! A compact nonnegative raw-H1 test is valid in a genuine weak
subsolution with locally L2 flux and RHS.  The test need not be bounded:
positive convolution preserves its sign, and actual strong L2 pairings
pay the limit.  This permits the full excess test without an invalid
gradient absorption outside a capped positive-part level. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualCompactRawSubsolutionTests405
open KLS ActualBoundedCanonicalSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem compact_raw_value_localL2_pairing_mollify
    {f b : Space n → ℝ} (hf : MemLp f 2 volume) (hc : HasCompactSupport f)
    (hb : ∀ E : Set (Space n), IsCompact E → MemLp b 2 (volume.restrict E)) :
    Integrable (fun x => b x*f x) ∧
      Tendsto (fun k => ∫ x, b x*mollify k f x) atTop (𝓝 (∫ x, b x*f x)) := by
  let E := mollifierEnlargement (tsupport f)
  have hE : IsCompact E := isCompact_mollifierEnlargement hc
  have hb2 : MemLp (E.indicator b) 2 volume :=
    (memLp_indicator_iff_restrict hE.measurableSet.nullMeasurableSet).mpr (hb E hE)
  have heq {q : Space n → ℝ} (hq : tsupport q ⊆ E) :
      (fun x => E.indicator b x*q x) = (fun x => b x*q x) := by
    funext x
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hq h)), mul_zero, mul_zero]
  have hef : (fun x => E.indicator b x*f x) = (fun x => b x*f x) :=
    heq (subset_mollifierEnlargement (tsupport f))
  have hIf : Integrable (fun x => b x*f x) := by
    have hi : Integrable (fun x => E.indicator b x*f x) := hb2.integrable_mul hf
    rwa [hef] at hi
  have ht := tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero
    (fun k => memLp_mollify hf k) hf hb2 (eLpNorm_mollify_sub_tendsto_zero hf)
  have hem (k : ℕ) : (∫ x, E.indicator b x*mollify k f x) = ∫ x, b x*mollify k f x :=
    congrArg (fun q : Space n → ℝ => ∫ x, q x) (heq (tsupport_mollify_subset hc k))
  have hei : (∫ x, E.indicator b x*f x) = ∫ x, b x*f x :=
    congrArg (fun q : Space n → ℝ => ∫ x, q x) hef
  exact ⟨hIf, by simpa only [hem, hei] using ht⟩

theorem compact_nonnegative_raw_H1_subsolution_test
    {A : Fin n → Space n → ℝ} {b f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hA : ∀ i E, IsCompact E → MemLp (A i) 2 (volume.restrict E))
    (hb : ∀ E, IsCompact E → MemLp b 2 (volume.restrict E))
    (hweak : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∀ x, 0 ≤ ψ x) → (∑ i, ∫ x, A i x*coordinateDerivative ψ i x) ≤ ∫ x, b x*ψ x)
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E))
    (hc : HasCompactSupport f) (hnonneg : ∀ x, 0 ≤ f x)
    (hFloc : ∀ i E, IsCompact E → MemLp (F i) 2 (volume.restrict E))
    (hw : ∀ i, HasLocalWeakCoordinateDerivative f (F i) i) :
    (∀ i, Integrable (fun x => A i x*F i x)) ∧ Integrable (fun x => b x*f x) ∧
      (∑ i, ∫ x, A i x*F i x) ≤ ∫ x, b x*f x := by
  have hf2 := memLp_compact_of_localL2 hf hc
  have hpair (i : Fin n) := (hw i).localL2_pairing_mollify hf2 hc (hFloc i) (hA i)
  have hval := compact_raw_value_localL2_pairing_mollify hf2 hc hb
  have hleft := tendsto_finsetSum Finset.univ fun i _ => (hpair i).2
  have hle (k : ℕ) :
      (∑ i, ∫ x, A i x*coordinateDerivative (mollify k f) i x) ≤ ∫ x, b x*mollify k f x :=
    hweak _ ((mollify_contDiff (hf2.locallyIntegrable (by norm_num)) k).of_le (by simp))
      (hasCompactSupport_mollify hc k) (mollify_nonneg hnonneg k)
  exact ⟨fun i => (hpair i).1, hval.1,
    le_of_tendsto_of_tendsto hleft hval.2 (Eventually.of_forall hle)⟩

theorem potential_compact_nonnegative_raw_H1_subsolution_test
    (d : SourceData μ)
    {A : Fin n → Space n → ℝ} {b f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hA : ∀ i E, IsCompact E → MemLp (A i) 2 (volume.restrict E))
    (hb : ∀ E, IsCompact E → MemLp b 2 (volume.restrict E))
    (hweak : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∀ x, 0 ≤ ψ x) →
        (∑ i, ∫ x, A i x*coordinateDerivative ψ i x ∂potentialMeasure d.potential) ≤
          ∫ x, b x*ψ x ∂potentialMeasure d.potential)
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E))
    (hc : HasCompactSupport f) (hnonneg : ∀ x, 0 ≤ f x)
    (hFloc : ∀ i E, IsCompact E → MemLp (F i) 2 (volume.restrict E))
    (hw : ∀ i, HasLocalWeakCoordinateDerivative f (F i) i) :
    (∀ i, Integrable (fun x => A i x*F i x) (potentialMeasure d.potential)) ∧
      Integrable (fun x => b x*f x) (potentialMeasure d.potential) ∧
      (∑ i, ∫ x, A i x*F i x ∂potentialMeasure d.potential) ≤
        ∫ x, b x*f x ∂potentialMeasure d.potential := by
  have hρ : Continuous (fun x => Real.exp (-d.potential x)) :=
    Real.continuous_exp.comp d.source_C1.continuous.neg
  have hρA (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => Real.exp (-d.potential x)*A i x) 2 (volume.restrict E) :=
    memLp_continuous_mul_on_compact hE (hA i E hE) hρ
  have hρb (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => Real.exp (-d.potential x)*b x) 2 (volume.restrict E) :=
    memLp_continuous_mul_on_compact hE (hb E hE) hρ
  have hvol (ψ : Space n → ℝ) (hψ : ContDiff ℝ 3 ψ) (hcψ : HasCompactSupport ψ)
      (hn : ∀ x, 0 ≤ ψ x) :
      (∑ i, ∫ x, (Real.exp (-d.potential x)*A i x)*coordinateDerivative ψ i x) ≤
        ∫ x, (Real.exp (-d.potential x)*b x)*ψ x := by
    have he := hweak ψ hψ hcψ hn
    simp_rw [integral_potentialMeasure d.source_C1.continuous.measurable] at he
    simpa only [mul_assoc, mul_left_comm, mul_comm] using he
  have he := compact_nonnegative_raw_H1_subsolution_test hρA hρb hvol hf hc hnonneg hFloc hw
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply (integrable_potentialMeasure_iff d.source_C1.continuous.measurable).mpr
    exact (he.1 i).congr (Eventually.of_forall fun x => by dsimp only; ring)
  · apply (integrable_potentialMeasure_iff d.source_C1.continuous.measurable).mpr
    exact he.2.1.congr (Eventually.of_forall fun x => by dsimp only; ring)
  · simp_rw [integral_potentialMeasure d.source_C1.continuous.measurable]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using he.2.2

end KLSConstantImprovement.ActualCompactRawSubsolutionTests405
#print axioms KLSConstantImprovement.ActualCompactRawSubsolutionTests405.compact_raw_value_localL2_pairing_mollify
#print axioms KLSConstantImprovement.ActualCompactRawSubsolutionTests405.compact_nonnegative_raw_H1_subsolution_test
#print axioms KLSConstantImprovement.ActualCompactRawSubsolutionTests405.potential_compact_nonnegative_raw_H1_subsolution_test
