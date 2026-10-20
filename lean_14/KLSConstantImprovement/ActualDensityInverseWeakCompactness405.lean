import KLSConstantImprovement.ActualDensityWeightedL2405
import KLSConstantImprovement.ActualWeakCanonicalMetricInverse
import KLSConstantImprovement.ActualSourceRegularizedWeakCompactness405

/-! A single fixed Hilbert ambient for actual inverse fields from varying
canonical sources. Multiplication by each source's true square-root density
preserves its L2 norm. No inverse-field limiting equation is assumed here. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ENNReal BigOperators RealInnerProductSpace
namespace KLSConstantImprovement.ActualDensityInverseWeakCompactness405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualWeakCanonicalMetricInverse ActualDensityWeightedL2405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

abbrev DensityInverseAmbient (n : ℕ) :=
  WithLp 2 (∀ _a : Fin (n+1), Lp ℝ 2 (volume : Measure (Space n)))

def actualDensityInverseField (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) : DensityInverseAmbient n :=
  WithLp.toLp 2 (Fin.cases (toVolumeL2 d.source_C1.continuous (sourceMetricInverse d g))
    (fun a => toVolumeL2 d.source_C1.continuous
      (canonicalMetricGradient d.potential a (sourceMetricInverseH1 d g))))

theorem actualDensityInverseField_norm_sq (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    ‖actualDensityInverseField d g‖ ^ 2 ≤ 2 * ‖g‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  simp only [actualDensityInverseField, PiLp.toLp_apply, Fin.cases_zero, Fin.cases_succ,
    toVolumeL2_norm]
  have hv := sourceMetricInverse_norm_le d g
  have he := sourceMetricInverse_energy_identity d g
  have hi := real_inner_le_norm g (sourceMetricInverse d g)
  have hv2 := (sq_le_sq₀ (norm_nonneg (sourceMetricInverse d g)) (norm_nonneg g)).mpr hv
  have hm := mul_le_mul_of_nonneg_left hv (norm_nonneg g)
  nlinarith

theorem exists_actual_densityInverse_weak_subsequence
    {ν : ℕ → Measure (Space n)} (d : ∀ k, SourceData (ν k))
    (g : ∀ k, Lp ℝ 2 (potentialMeasure (d k).potential))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ k, ‖g k‖ ≤ C) :
    ∃ (W : DensityInverseAmbient n) (σ : ℕ → ℕ),
      StrictMono σ ∧ ‖W‖ ≤ 2 * C ∧
      ∀ Y : DensityInverseAmbient n,
        Tendsto (fun k => inner ℝ (actualDensityInverseField (d (σ k)) (g (σ k))) Y)
          atTop (𝓝 (inner ℝ W Y)) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  letI : TopologicalSpace.SeparableSpace (Lp ℝ 2 (volume : Measure (Space n))) := inferInstance
  letI : TopologicalSpace.SeparableSpace (DensityInverseAmbient n) := inferInstance
  have hnorm (k : ℕ) : ‖actualDensityInverseField (d k) (g k)‖ ≤ 2 * C := by
    have hh := actualDensityInverseField_norm_sq (d k) (g k)
    have hsq := (sq_le_sq₀ (norm_nonneg (g k)) hC).mpr (hb k)
    nlinarith [norm_nonneg (actualDensityInverseField (d k) (g k))]
  obtain ⟨W, σ, hσ, hW, hw⟩ := exists_weak_limit_of_bounded_hilbert hnorm
  exact ⟨W, σ, hσ, hW, hw⟩

end KLSConstantImprovement.ActualDensityInverseWeakCompactness405
#print axioms KLSConstantImprovement.ActualDensityInverseWeakCompactness405.actualDensityInverseField_norm_sq
#print axioms KLSConstantImprovement.ActualDensityInverseWeakCompactness405.exists_actual_densityInverse_weak_subsequence
