import KLSConstantImprovement.ActualNaturalFluxAdjoint405
import KLS.BoundedCompactH1Tests

/-! Genuine compact weak test extensions by simultaneous local L2
mollifier pairings. Only the smooth tests actually available for the
constructed natural inverse are used; no operator-core assertion occurs. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualLocalDivergenceTests405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405
open ActualSourceRegularizedLocalEquation405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem integral_divergence_of_C3_locallyLipschitz_test
    {A : Fin n → Space n → ℝ} {b : Space n → ℝ}
    (hA : ∀ i E, IsCompact E → MemLp (A i) 2 (volume.restrict E))
    (hb : ∀ E, IsCompact E → MemLp b 2 (volume.restrict E))
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∑ i, ∫ x, A i x * coordinateDerivative ψ i x) = ∫ x, b x * ψ x)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (hc : HasCompactSupport f) :
    (∑ i, ∫ x, A i x * coordinateDerivative f i x) = ∫ x, b x * f x := by
  have hl := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_integral_mul_coordinateDerivative_mollify_of_localL2 hf hc (hA i) i
  have hr := tendsto_integral_mul_mollify_of_localL2 hf.continuous hc hb
  have he : (fun k => ∑ i, ∫ x, A i x * coordinateDerivative (mollify k f) i x) =
      fun k => ∫ x, b x * mollify k f x := by
    funext k
    exact hdiv _ ((mollify_contDiff hf.continuous.locallyIntegrable k).of_le (by simp))
      (hasCompactSupport_mollify hc k)
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

theorem integral_divergence_of_C3_bounded_compact_H1_test
    {A : Fin n → Space n → ℝ} {b f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hA : ∀ i E, IsCompact E → MemLp (A i) 2 (volume.restrict E))
    (hb : LocallyIntegrable b volume)
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∑ i, ∫ x, A i x * coordinateDerivative ψ i x) = ∫ x, b x * ψ x)
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E))
    (hc : HasCompactSupport f) {B : ℝ} (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ B)
    (hFloc : ∀ i E, IsCompact E → MemLp (F i) 2 (volume.restrict E))
    (hF : ∀ i, HasLocalWeakCoordinateDerivative f (F i) i) :
    (∀ i, Integrable (fun x => A i x * F i x)) ∧ Integrable (fun x => b x * f x) ∧
      (∑ i, ∫ x, A i x * F i x) = ∫ x, b x * f x := by
  have hf2 := memLp_compact_of_localL2 hf hc
  have hfloc := hf2.locallyIntegrable (by norm_num)
  have hp (i : Fin n) := (hF i).localL2_pairing_mollify hf2 hc (hFloc i) (hA i)
  have hr := bounded_compact_mollify_localL1_pairing hfloc hc hbound hb
  refine ⟨fun i => (hp i).1, hr.1, ?_⟩
  have hl := tendsto_finsetSum Finset.univ fun i _ => (hp i).2
  have he : (fun k => ∑ i, ∫ x, A i x * coordinateDerivative (mollify k f) i x) =
      fun k => ∫ x, b x * mollify k f x := by
    funext k
    exact hdiv _ ((mollify_contDiff hfloc k).of_le (by simp)) (hasCompactSupport_mollify hc k)
  rw [he] at hl
  exact tendsto_nhds_unique hl hr.2

theorem naturalCanonicalFlux_locallyLipschitz_test (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (hc : HasCompactSupport f) :
    (∑ i : Fin n, ∫ x, naturalCanonicalFlux d g i x * coordinateDerivative f i x
      ∂potentialMeasure d.potential) = ∫ x, g x * f x ∂potentialMeasure d.potential := by
  obtain ⟨Du, hu, _, _, _, _, _, _, hdiv⟩ := exists_naturalCanonicalFlux_gaffney d hn g hg
  have hA (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => Real.exp (-d.potential x) * naturalCanonicalFlux d g i x) 2 (volume.restrict E) :=
    memLp_continuous_mul_on_compact hE (hu i E hE)
      (Real.continuous_exp.comp d.source_C1.continuous.neg)
  have he := integral_divergence_of_C3_locallyLipschitz_test hA
    (fun E hE => regularizedDensityForcing_local_L2 d g hE) (fun ψ hψ hψc => by
      have ht := hdiv ψ hψ hψc
      simp_rw [integral_potentialMeasure d.source_C1.continuous.measurable] at ht
      simpa only [mul_assoc, mul_left_comm, mul_comm] using ht) hf hc
  simp_rw [integral_potentialMeasure d.source_C1.continuous.measurable]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using he

end KLSConstantImprovement.ActualLocalDivergenceTests405

#print axioms KLSConstantImprovement.ActualLocalDivergenceTests405.integral_divergence_of_C3_locallyLipschitz_test
#print axioms KLSConstantImprovement.ActualLocalDivergenceTests405.integral_divergence_of_C3_bounded_compact_H1_test
#print axioms KLSConstantImprovement.ActualLocalDivergenceTests405.naturalCanonicalFlux_locallyLipschitz_test
