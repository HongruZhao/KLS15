import KLSConstantImprovement.ActualNaturalWeakKato405
import KLSConstantImprovement.Raw405ReusedBellmanConditionalEndpoint
import KLSConstantImprovement.AffineSameTestIncrementalEndpoint

/-! Original admissible laws: actual local weak Kato, source approximation,
inverse limiting identification and mass/variance transfer discharge raw405.
The exact Poincare endpoint reuses the existing all-rank weighted profile.
The exponential CP4/raw216 benchmark remains in the imported proof chain. -/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal ContDiff
namespace KLSConstantImprovement.OriginalCubic405Endpoint
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open ActualNaturalWeakKato405 OriginalCubic405OfWeakKato
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

def bound : ℝ := 14008424347707971725017/976562500000000000000

theorem actual_mass_source_gate405 : OriginalCubic405MassSourceGate.BoundedStrongMassSourceGate405 :=
  mass_source_gate_of_actual_weak_Kato actual_natural_weak_Kato_gate405

theorem original_literal_raw405 :
    LiteralCubicVarianceObservationTransfer.UniversalLiteralCubicVarianceBound 405 :=
  original_literal_raw405_of_actual_weak_Kato actual_natural_weak_Kato_gate405

theorem original_observation_raw405 : RawCubicWeightedBudget.UniversalRawCubicBound 405 :=
  original_observation_raw405_of_actual_weak_Kato actual_natural_weak_Kato_gate405

theorem best_current_original_class {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (14008424347707971725017/976562500000000000000 : ℝ≥0∞)*energy μ f :=
  Raw405ReusedBellmanConditionalEndpoint.original_poincare original_observation_raw405 hn hμ hf

theorem current_universal_interval :
    (4 : ℝ≥0∞) ≤ universalPoincareConstant ∧
      universalPoincareConstant ≤ (14008424347707971725017/976562500000000000000 : ℝ≥0∞) :=
  ⟨KLS4Research.ExponentialOriginalSharpness.universal_poincareConstant_lower_four,
    Raw405ReusedBellmanConditionalEndpoint.universal_poincare_upper original_observation_raw405⟩

theorem current_openai_poincare {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ)
      ((14008424347707971725017 : ℝ)/976562500000000000000) :=
  Raw405ReusedBellmanConditionalEndpoint.openai_poincare original_observation_raw405 hn hρ hiso

theorem exponential_benchmark_original_class {n : ℕ} {f : Space n → ℝ}
    (hf : LocallyLipschitzTests (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f) :
    variance (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f ≤
      (4 : ℝ≥0∞)*energy (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f :=
  AffineSameTestIncrementalEndpoint.exponential_benchmark_original_class hf

theorem current_bound_lt_previous : bound < AffineSameTestIncrementalEndpoint.bound := by
  norm_num [bound, AffineSameTestIncrementalEndpoint.bound]

theorem current_bound_gap_fourteen : bound-14 = 336549347707971725017/976562500000000000000 := by
  norm_num [bound]

end KLSConstantImprovement.OriginalCubic405Endpoint
#print axioms KLSConstantImprovement.OriginalCubic405Endpoint.actual_mass_source_gate405
#print axioms KLSConstantImprovement.OriginalCubic405Endpoint.original_literal_raw405
#print axioms KLSConstantImprovement.OriginalCubic405Endpoint.original_observation_raw405
#print axioms KLSConstantImprovement.OriginalCubic405Endpoint.best_current_original_class
#print axioms KLSConstantImprovement.OriginalCubic405Endpoint.current_universal_interval
#print axioms KLSConstantImprovement.OriginalCubic405Endpoint.current_openai_poincare
#print axioms KLSConstantImprovement.OriginalCubic405Endpoint.exponential_benchmark_original_class
#print axioms KLSConstantImprovement.OriginalCubic405Endpoint.current_bound_lt_previous
#print axioms KLSConstantImprovement.OriginalCubic405Endpoint.current_bound_gap_fourteen
