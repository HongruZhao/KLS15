import KLSConstantImprovement.CurrentIncrementalEndpoint
import KLSConstantImprovement.RefinedSeed2388BellmanEndpoint
import KLSConstantImprovement.UpperBoundMergeAudit
import ActualCubicSeedObstruction

/-! Current endpoint wrapper, separate from the frozen 24-module merge audit.
This source is registered only after the complete seed2388 original-law
endpoint and this wrapper compile successfully. Fourteen remains open. -/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal
namespace KLSConstantImprovement.RefinedIncrementalEndpoint
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration

def bound : ℝ := 2801814054094494174377/195312500000000000000

theorem best_current_original_class {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (2801814054094494174377/195312500000000000000 : ℝ≥0∞)*energy μ f :=
  RefinedSeed2388BellmanEndpoint.original_poincare hn hμ hf

theorem current_universal_interval :
    (4 : ℝ≥0∞) ≤ universalPoincareConstant ∧
      universalPoincareConstant ≤ (2801814054094494174377/195312500000000000000 : ℝ≥0∞) :=
  ⟨KLS4Research.ExponentialOriginalSharpness.universal_poincareConstant_lower_four,
    RefinedSeed2388BellmanEndpoint.universal_poincare_upper⟩

theorem current_bound_lt_frozen : bound<LongPrefixCubicBellmanEndpoint.bound := by
  norm_num [bound,LongPrefixCubicBellmanEndpoint.bound]

theorem current_bound_gt_fourteen : (14 : ℝ)<bound := by norm_num [bound]

theorem current_openai_poincare {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ)
      ((2801814054094494174377 : ℝ)/195312500000000000000) :=
  RefinedSeed2388BellmanEndpoint.openai_poincare hn hρ hiso

theorem exponential_benchmark_original_class {n : ℕ} {f : Space n → ℝ}
    (hf : LocallyLipschitzTests (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f) :
    variance (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f ≤
      (4 : ℝ≥0∞)*energy (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f :=
  UpperBoundMergeAudit.exponential_benchmark_original_class hf

theorem current_bound_lt_previous : bound < CurrentIncrementalEndpoint.bound := by
  norm_num [bound,CurrentIncrementalEndpoint.bound]

end KLSConstantImprovement.RefinedIncrementalEndpoint
#print axioms KLSConstantImprovement.RefinedIncrementalEndpoint.best_current_original_class
#print axioms KLSConstantImprovement.RefinedIncrementalEndpoint.current_universal_interval
#print axioms KLSConstantImprovement.RefinedIncrementalEndpoint.current_bound_lt_frozen
#print axioms KLSConstantImprovement.RefinedIncrementalEndpoint.current_bound_gt_fourteen
#print axioms KLSConstantImprovement.RefinedIncrementalEndpoint.current_openai_poincare
#print axioms KLSConstantImprovement.RefinedIncrementalEndpoint.exponential_benchmark_original_class
#print axioms KLSImprovement.CubicSeedObstruction.unitWitness_energy_three
#print axioms KLSConstantImprovement.RefinedIncrementalEndpoint.current_bound_lt_previous
#print axioms KLSImprovement.CubicSeedObstruction.cubicWitness_square
