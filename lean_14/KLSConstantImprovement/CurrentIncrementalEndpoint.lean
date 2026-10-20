import KLSConstantImprovement.Seed2388BellmanEndpoint
import KLSConstantImprovement.UpperBoundMergeAudit
import ActualCubicSeedObstruction

/-! Current endpoint wrapper, separate from the frozen 24-module merge audit.
This source is registered only after the complete seed2388 original-law
endpoint and this wrapper compile successfully. Fourteen remains open. -/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal
namespace KLSConstantImprovement.CurrentIncrementalEndpoint
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration

def bound : ℝ := 280181408857940687/19531250000000000

theorem best_current_original_class {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (280181408857940687/19531250000000000 : ℝ≥0∞)*energy μ f :=
  Seed2388BellmanEndpoint.original_poincare hn hμ hf

theorem current_universal_interval :
    (4 : ℝ≥0∞) ≤ universalPoincareConstant ∧
      universalPoincareConstant ≤ (280181408857940687/19531250000000000 : ℝ≥0∞) :=
  ⟨KLS4Research.ExponentialOriginalSharpness.universal_poincareConstant_lower_four,
    Seed2388BellmanEndpoint.universal_poincare_upper⟩

theorem current_bound_lt_frozen : bound<LongPrefixCubicBellmanEndpoint.bound := by
  norm_num [bound,LongPrefixCubicBellmanEndpoint.bound]

theorem current_bound_gt_fourteen : (14 : ℝ)<bound := by norm_num [bound]

theorem current_openai_poincare {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ)
      ((280181408857940687 : ℝ)/19531250000000000) :=
  Seed2388BellmanEndpoint.openai_poincare hn hρ hiso

theorem exponential_benchmark_original_class {n : ℕ} {f : Space n → ℝ}
    (hf : LocallyLipschitzTests (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f) :
    variance (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f ≤
      (4 : ℝ≥0∞)*energy (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f :=
  UpperBoundMergeAudit.exponential_benchmark_original_class hf

end KLSConstantImprovement.CurrentIncrementalEndpoint
#print axioms KLSConstantImprovement.CurrentIncrementalEndpoint.best_current_original_class
#print axioms KLSConstantImprovement.CurrentIncrementalEndpoint.current_universal_interval
#print axioms KLSConstantImprovement.CurrentIncrementalEndpoint.current_bound_lt_frozen
#print axioms KLSConstantImprovement.CurrentIncrementalEndpoint.current_bound_gt_fourteen
#print axioms KLSConstantImprovement.CurrentIncrementalEndpoint.current_openai_poincare
#print axioms KLSConstantImprovement.CurrentIncrementalEndpoint.exponential_benchmark_original_class
#print axioms KLSImprovement.CubicSeedObstruction.unitWitness_energy_three
