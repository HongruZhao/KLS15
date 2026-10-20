import KLSConstantImprovement.ActualSourceCompactMetricCondition405

/-! On each fixed compact source support, actual inverse-metric cutoff
energy is essentially bounded. This pays its product with the genuine
natural mass L1, without a mass-infinity assumption. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualSourceCompactCutoffBound405
open KLS ActualBoundedCanonicalSource ActualSourceCompactMetricCondition405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_compact_inverse_cutoff_energy_memLp_top (d : SourceData μ)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    MemLp (inverseHessianGradientForm d.potential χ) ∞ (potentialMeasure d.potential) := by
  obtain ⟨α, β, hα, _hβ, hmetric⟩ := actual_compact_metric_quadratic_bounds d (tsupport χ) hc
  have hmet := (ae_restrict_iff' hc.measurableSet).mp hmetric
  have hcont : Continuous (fun x => ∑ i : Fin n, coordinateDerivative χ i x ^ 2) := by
    apply continuous_finsetSum
    intro i _
    exact ((contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous).pow 2
  obtain ⟨C, hC⟩ := hc.bddAbove_image hcont.continuousOn
  let D : ℝ := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  apply memLp_top_of_bound (d.compact_inverse_energy_integrable hχ hc).aestronglyMeasurable (α⁻¹ * D)
  filter_upwards [hmet, d.hessian_ae_source] with x hx hp
  have hn : 0 ≤ inverseHessianGradientForm d.potential χ x :=
    inverseHessianGradientForm_nonneg_at χ hp.1
  rw [Real.norm_of_nonneg hn]
  by_cases hxE : x ∈ tsupport χ
  · have hb := (hx hxE (fun i => coordinateDerivative χ i x)).2.2
    have hsum : (∑ i : Fin n, coordinateDerivative χ i x ^ 2) ≤ D :=
      (hC (mem_image_of_mem _ hxE)).trans (le_max_left _ _)
    have hq : inverseHessianGradientForm d.potential χ x ≤
        α⁻¹ * (∑ i : Fin n, coordinateDerivative χ i x ^ 2) := by
      rw [inverseHessianGradientForm, matrix_quadratic_sum_eq_dotProduct]
      simpa only [dotProduct, ← pow_two] using hb
    exact hq.trans (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hα.le))
  · have hd (i : Fin n) : coordinateDerivative χ i x = 0 :=
      image_eq_zero_of_notMem_tsupport fun ht => hxE (tsupport_coordinateDerivative_subset χ i ht)
    have hz : inverseHessianGradientForm d.potential χ x = 0 := by
      simp only [inverseHessianGradientForm, hd, mul_zero, Finset.sum_const_zero]
    rw [hz]
    exact mul_nonneg (inv_nonneg.mpr hα.le) hD

theorem actual_compact_mass_cutoff_integrable (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hM : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g))
      (potentialMeasure d.potential))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    Integrable (fun x => sourceVectorMass d.potential (naturalCanonicalFlux d g) x *
      inverseHessianGradientForm d.potential χ x) (potentialMeasure d.potential) :=
  hM.mul_of_top_left (actual_compact_inverse_cutoff_energy_memLp_top d hχ hc)

end KLSConstantImprovement.ActualSourceCompactCutoffBound405
#print axioms KLSConstantImprovement.ActualSourceCompactCutoffBound405.actual_compact_inverse_cutoff_energy_memLp_top
#print axioms KLSConstantImprovement.ActualSourceCompactCutoffBound405.actual_compact_mass_cutoff_integrable
