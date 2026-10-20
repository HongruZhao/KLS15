import KLSConstantImprovement.OriginalCubic4047255
import KLSConstantImprovement.ResumeRaw4047255BellmanConditionalEndpoint
import KLSConstantImprovement.OriginalCubic405Endpoint

/-! Original admissible laws: actual local weak Kato, source approximation,
inverse limiting identification and mass/variance transfer discharge raw404.7255.
The exact Poincare endpoint optimizes observation multipliers and finite Bellman stages on the existing all-rank weighted profile.
The exponential CP4/raw216 benchmark remains in the imported proof chain. -/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal ContDiff
namespace KLSConstantImprovement.OriginalCubic4047255OptimizedEndpoint
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open OriginalCubic4047255
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

def bound : ℝ := 1400840517562834548357/97656250000000000000

theorem original_literal_raw4047255 :
    LiteralCubicVarianceObservationTransfer.UniversalLiteralCubicVarianceBound (809451/2000) :=
  by
    have he : (4047255/10000:ℝ) = 809451/2000 := by norm_num
    rw [←he]
    exact @OriginalCubic4047255.original_literal_raw4047255

theorem original_observation_raw4047255 : RawCubicWeightedBudget.UniversalRawCubicBound (809451/2000) :=
  by
    have he : (4047255/10000:ℝ) = 809451/2000 := by norm_num
    rw [←he]
    exact @OriginalCubic4047255.original_observation_raw4047255

theorem best_current_original_class {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (1400840517562834548357/97656250000000000000 : ℝ≥0∞)*energy μ f :=
  ResumeRaw4047255BellmanConditionalEndpoint.original_poincare original_observation_raw4047255 hn hμ hf

theorem current_universal_interval :
    (4 : ℝ≥0∞) ≤ universalPoincareConstant ∧
      universalPoincareConstant ≤ (1400840517562834548357/97656250000000000000 : ℝ≥0∞) :=
  ⟨KLS4Research.ExponentialOriginalSharpness.universal_poincareConstant_lower_four,
    ResumeRaw4047255BellmanConditionalEndpoint.universal_poincare_upper original_observation_raw4047255⟩

theorem current_openai_poincare {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ)
      ((1400840517562834548357 : ℝ)/97656250000000000000) :=
  ResumeRaw4047255BellmanConditionalEndpoint.openai_poincare original_observation_raw4047255 hn hρ hiso

theorem exponential_benchmark_original_class {n : ℕ} {f : Space n → ℝ}
    (hf : LocallyLipschitzTests (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f) :
    variance (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f ≤
      (4 : ℝ≥0∞)*energy (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f :=
  OriginalCubic405Endpoint.exponential_benchmark_original_class hf

theorem current_bound_lt_previous : bound < OriginalCubic405Endpoint.bound := by
  norm_num [bound, OriginalCubic405Endpoint.bound]

theorem current_bound_gap_fourteen : bound-14 = 33653017562834548357/97656250000000000000 := by
  norm_num [bound]

end KLSConstantImprovement.OriginalCubic4047255OptimizedEndpoint
#print axioms KLSConstantImprovement.OriginalCubic4047255OptimizedEndpoint.original_literal_raw4047255
#print axioms KLSConstantImprovement.OriginalCubic4047255OptimizedEndpoint.original_observation_raw4047255
#print axioms KLSConstantImprovement.OriginalCubic4047255OptimizedEndpoint.best_current_original_class
#print axioms KLSConstantImprovement.OriginalCubic4047255OptimizedEndpoint.current_universal_interval
#print axioms KLSConstantImprovement.OriginalCubic4047255OptimizedEndpoint.current_openai_poincare
#print axioms KLSConstantImprovement.OriginalCubic4047255OptimizedEndpoint.exponential_benchmark_original_class
#print axioms KLSConstantImprovement.OriginalCubic4047255OptimizedEndpoint.current_bound_lt_previous
#print axioms KLSConstantImprovement.OriginalCubic4047255OptimizedEndpoint.current_bound_gap_fourteen
