import KLSConstantImprovement.OriginalCubic40147
import KLSConstantImprovement.ResumeRaw40147BellmanConditionalEndpoint
import KLSConstantImprovement.OriginalCubic4047255OptimizedEndpoint

/-! Original admissible laws: actual local weak Kato, source approximation,
inverse limiting identification and mass/variance transfer discharge raw405.
The exact Poincare endpoint optimizes observation multipliers and finite Bellman stages on the existing all-rank weighted profile.
The exponential CP4/raw216 benchmark remains in the imported proof chain. -/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal ContDiff
namespace KLSConstantImprovement.OriginalCubic40147OptimizedEndpoint
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open OriginalCubic40147
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

def bound : ℝ := 280166652540873008809/19531250000000000000

theorem original_literal_raw40147 :
    LiteralCubicVarianceObservationTransfer.UniversalLiteralCubicVarianceBound (40147/100) :=
  @OriginalCubic40147.original_literal_raw40147

theorem original_observation_raw40147 : RawCubicWeightedBudget.UniversalRawCubicBound (40147/100) :=
  @OriginalCubic40147.original_observation_raw40147

theorem best_current_original_class {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (280166652540873008809/19531250000000000000 : ℝ≥0∞)*energy μ f :=
  ResumeRaw40147BellmanConditionalEndpoint.original_poincare original_observation_raw40147 hn hμ hf

theorem current_universal_interval :
    (4 : ℝ≥0∞) ≤ universalPoincareConstant ∧
      universalPoincareConstant ≤ (280166652540873008809/19531250000000000000 : ℝ≥0∞) :=
  ⟨KLS4Research.ExponentialOriginalSharpness.universal_poincareConstant_lower_four,
    ResumeRaw40147BellmanConditionalEndpoint.universal_poincare_upper original_observation_raw40147⟩

theorem current_openai_poincare {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ)
      ((280166652540873008809 : ℝ)/19531250000000000000) :=
  ResumeRaw40147BellmanConditionalEndpoint.openai_poincare original_observation_raw40147 hn hρ hiso

theorem exponential_benchmark_original_class {n : ℕ} {f : Space n → ℝ}
    (hf : LocallyLipschitzTests (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f) :
    variance (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f ≤
      (4 : ℝ≥0∞)*energy (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f :=
  OriginalCubic405Endpoint.exponential_benchmark_original_class hf

theorem current_bound_lt_previous : bound < OriginalCubic4047255OptimizedEndpoint.bound := by
  norm_num [bound, OriginalCubic4047255OptimizedEndpoint.bound]

theorem current_bound_gap_fourteen : bound-14 = 6729152540873008809/19531250000000000000 := by
  norm_num [bound]

end KLSConstantImprovement.OriginalCubic40147OptimizedEndpoint
#print axioms KLSConstantImprovement.OriginalCubic40147OptimizedEndpoint.original_literal_raw40147
#print axioms KLSConstantImprovement.OriginalCubic40147OptimizedEndpoint.original_observation_raw40147
#print axioms KLSConstantImprovement.OriginalCubic40147OptimizedEndpoint.best_current_original_class
#print axioms KLSConstantImprovement.OriginalCubic40147OptimizedEndpoint.current_universal_interval
#print axioms KLSConstantImprovement.OriginalCubic40147OptimizedEndpoint.current_openai_poincare
#print axioms KLSConstantImprovement.OriginalCubic40147OptimizedEndpoint.exponential_benchmark_original_class
#print axioms KLSConstantImprovement.OriginalCubic40147OptimizedEndpoint.current_bound_lt_previous
#print axioms KLSConstantImprovement.OriginalCubic40147OptimizedEndpoint.current_bound_gap_fourteen
