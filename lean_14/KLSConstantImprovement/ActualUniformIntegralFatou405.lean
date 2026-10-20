import KLS.HessianMetricIntegrationExtension

/-! Uniform localized integral bounds pay a global integrability domain
before any limiting integration by parts is used. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace KLSConstantImprovement.ActualUniformIntegralFatou405

theorem integrable_and_integral_norm_le_of_tendsto_uniform_bound
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {F : ℕ → α → ℝ} {f : α → ℝ} {C : ℝ}
    (hf : AEStronglyMeasurable f ν) (hF : ∀ k, Integrable (F k) ν)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun k => F k x) atTop (𝓝 (f x)))
    (hC : 0 ≤ C) (hbound : ∀ k, (∫ x, ‖F k x‖ ∂ν) ≤ C) :
    Integrable f ν ∧ (∫ x, ‖f x‖ ∂ν) ≤ C := by
  have hfatou : (∫⁻ x, ‖f x‖ₑ ∂ν) ≤
      liminf (fun k => ∫⁻ x, ‖F k x‖ₑ ∂ν) atTop := by
    calc
      (∫⁻ x, ‖f x‖ₑ ∂ν) = ∫⁻ x, liminf (fun k => ‖F k x‖ₑ) atTop ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact hx.enorm.liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le' (fun k => (hF k).aestronglyMeasurable.aemeasurable.enorm)
  have hle (k : ℕ) : (∫⁻ x, ‖F k x‖ₑ ∂ν) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hF k)]
    exact ENNReal.ofReal_le_ofReal (hbound k)
  have hliminf : liminf (fun k => ∫⁻ x, ‖F k x‖ₑ ∂ν) atTop ≤ ENNReal.ofReal C :=
    liminf_le_of_frequently_le' (Eventually.of_forall hle).frequently
  have hnorm := hfatou.trans hliminf
  have hfi : Integrable f ν :=
    ⟨hf, hasFiniteIntegral_iff_enorm.mpr (hnorm.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hfi, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ofReal_integral_norm_eq_lintegral_enorm hfi]
  exact hnorm

end KLSConstantImprovement.ActualUniformIntegralFatou405
#print axioms KLSConstantImprovement.ActualUniformIntegralFatou405.integrable_and_integral_norm_le_of_tendsto_uniform_bound
