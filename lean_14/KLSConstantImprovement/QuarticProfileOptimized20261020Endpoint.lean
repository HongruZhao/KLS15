import KLSConstantImprovement.QuarticProfileOptimized20261020Operator
import ActualKLS149963Endpoints
import KLSConstantImprovement.OriginalQuartic13999Endpoint
import KLSConstantImprovement.OriginalCubic40147OptimizedEndpoint

/-! Original-class bound699554753913826189069703199/50000000000000000000000000. The universal cubic theorem, actual same-test
quartic support, all-rank generator, eleven Bellman stages, actual operator
and regular-to-original transfer are proved by the imported chain. -/
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff ENNReal NNReal
namespace KLSConstantImprovement.QuarticProfileOptimized20261020Endpoint
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.Raw401317Quartic13999ProfileData hiding p
open KLSConstantImprovement.QuarticProfileOptimized20261020Data
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

def bound : ℝ := 699554753913826189069703199/50000000000000000000000000

theorem regular_poincare
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hn : 0 < n) (hμ : admissibleMeasure (potentialMeasure φ)) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal bound := by
  have hnorm := QuarticProfileOptimized20261020Operator.operator_norm_sq_le hφ hκ hlower hμ
  have hb : 1+‖gradedTensorIntegration hφ hκ hlower‖^2 ≤ bound := by
    calc
      _ ≤ 1+K*p := by linarith
      _ = bound := by norm_num [K,p,bound]
  exact (poincareConstant_le_one_add_graded_norm_sq hφ hκ hlower hn hμ.isotropic).trans
    (ENNReal.ofReal_le_ofReal hb)

theorem original_poincare_mem
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (699554753913826189069703199/50000000000000000000000000 : ℝ≥0) ∈ poincareConstants μ := by
  apply mem_poincareConstants_of_paperRegularDensity hμ (by norm_num)
  intro ν hν hregular
  obtain ⟨V,κ,hV,hκ,hstrong,hupper,hgrowth,heq⟩ := hregular
  subst ν
  let : IsProbabilityMeasure (potentialMeasure V) := hν.isProb
  let hlower := coordinateHessian_lower_of_strongConvexOn (hV.of_le (by simp)) hstrong
  have hc := regular_poincare hV hκ hlower (by omega) hν
  have hfin : poincareConstant (potentialMeasure V) < ⊤ := hc.trans_lt ENNReal.ofReal_lt_top
  apply (poincareConstants_iff_optimal_le (poincareConstants_nonempty_iff.mpr hfin)
    (hν.poincareConstant_pos hn)).mpr
  convert hc using 1
  unfold bound
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 50000000000000000000000000)]
  norm_num

theorem original_poincare
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (699554753913826189069703199/50000000000000000000000000 : ℝ≥0∞)*energy μ f := by
  simpa using original_poincare_mem hn hμ f hf

theorem universal_poincare_upper
    :
    universalPoincareConstant ≤ (699554753913826189069703199/50000000000000000000000000 : ℝ≥0∞) := by
  apply universal_le_iff.mpr
  intro n hn μ hμ
  simpa using poincareConstant_le_of_mem (original_poincare_mem hn hμ)

theorem bound_lt_fourteen : bound < 14 := by norm_num [bound]

theorem universal_poincare_lt_fourteen
    :
    universalPoincareConstant < 14 := by
  refine (universal_poincare_upper).trans_lt ?_
  apply (ENNReal.toReal_lt_toReal
    (ENNReal.div_ne_top (by norm_num) (by norm_num)) (by norm_num)).mp
  norm_num

theorem openai_poincare
    {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) (699554753913826189069703199/50000000000000000000000000) :=
  OpenAIBridge.poincareBound_of_mem hρ
    (original_poincare_mem hn (OpenAIBridge.admissible hρ hiso))

theorem best_current_original_class {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (699554753913826189069703199/50000000000000000000000000 : ℝ≥0∞)*energy μ f := original_poincare hn hμ hf

theorem current_universal_interval :
    (4 : ℝ≥0∞) ≤ universalPoincareConstant ∧ universalPoincareConstant ≤ (699554753913826189069703199/50000000000000000000000000 : ℝ≥0∞) :=
  ⟨KLS4Research.ExponentialOriginalSharpness.universal_poincareConstant_lower_four,universal_poincare_upper⟩

theorem current_openai_poincare {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) (699554753913826189069703199/50000000000000000000000000) := openai_poincare hn hρ hiso

theorem exponential_benchmark_original_class {n : ℕ} {f : Space n → ℝ}
    (hf : LocallyLipschitzTests (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f) :
    variance (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f ≤
      (4 : ℝ≥0∞)*energy (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f :=
  OriginalCubic40147OptimizedEndpoint.exponential_benchmark_original_class hf

theorem current_bound_lt_previous : bound < OriginalQuartic13999Endpoint.bound := by
  norm_num [bound,OriginalQuartic13999Endpoint.bound]

theorem current_bound_gap_fourteen : 14-bound=(445246086173810930296801/50000000000000000000000000:ℝ) := by norm_num [bound]

end KLSConstantImprovement.QuarticProfileOptimized20261020Endpoint
#check KLSConstantImprovement.QuarticProfileOptimized20261020Endpoint.universal_poincare_lt_fourteen
#print axioms KLSConstantImprovement.QuarticProfileOptimized20261020Endpoint.regular_poincare
#print axioms KLSConstantImprovement.QuarticProfileOptimized20261020Endpoint.original_poincare_mem
#print axioms KLSConstantImprovement.QuarticProfileOptimized20261020Endpoint.original_poincare
#print axioms KLSConstantImprovement.QuarticProfileOptimized20261020Endpoint.universal_poincare_upper
#print axioms KLSConstantImprovement.QuarticProfileOptimized20261020Endpoint.bound_lt_fourteen
#print axioms KLSConstantImprovement.QuarticProfileOptimized20261020Endpoint.universal_poincare_lt_fourteen
#print axioms KLSConstantImprovement.QuarticProfileOptimized20261020Endpoint.openai_poincare

#print axioms KLSConstantImprovement.QuarticProfileOptimized20261020Endpoint.best_current_original_class

#print axioms KLSConstantImprovement.QuarticProfileOptimized20261020Endpoint.current_universal_interval

#print axioms KLSConstantImprovement.QuarticProfileOptimized20261020Endpoint.current_openai_poincare

#print axioms KLSConstantImprovement.QuarticProfileOptimized20261020Endpoint.exponential_benchmark_original_class

#print axioms KLSConstantImprovement.QuarticProfileOptimized20261020Endpoint.current_bound_lt_previous

#print axioms KLSConstantImprovement.QuarticProfileOptimized20261020Endpoint.current_bound_gap_fourteen
