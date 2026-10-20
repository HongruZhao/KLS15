import KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightOperator
import ActualKLS149963Endpoints
import KLSConstantImprovement.QuarticM20Bellman20261020Endpoint

/-! Original-class bound13810833/1000000. The universal cubic theorem, actual same-test
quartic support and all-rank weightedbudgets, their positive mixture, 95 Bellman stages, actual operator
and regular-to-original transfer are proved by the imported chain. -/
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff ENNReal NNReal
namespace KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.AcceptedMix96Data
open KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightData
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

def bound : ℝ := 13810833/1000000

theorem regular_poincare
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hn : 0 < n) (hμ : admissibleMeasure (potentialMeasure φ)) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal bound := by
  have hnorm := QuarticM96MixTrueCapBellman20261020TightOperator.operator_norm_sq_le hφ hκ hlower hμ
  have hb : 1+‖gradedTensorIntegration hφ hκ hlower‖^2 ≤ bound := by
    calc
      _ ≤ 1+K*q := by linarith
      _ = bound := QuarticM96MixTrueCapBellman20261020TightData.exact_endpoint
  exact (poincareConstant_le_one_add_graded_norm_sq hφ hκ hlower hn hμ.isotropic).trans
    (ENNReal.ofReal_le_ofReal hb)

theorem original_poincare_mem
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (13810833/1000000 : ℝ≥0) ∈ poincareConstants μ := by
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
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1000000)]
  norm_num

theorem original_poincare
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (13810833/1000000 : ℝ≥0∞)*energy μ f := by
  simpa using original_poincare_mem hn hμ f hf

theorem universal_poincare_upper
    :
    universalPoincareConstant ≤ (13810833/1000000 : ℝ≥0∞) := by
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
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) (13810833/1000000) :=
  OpenAIBridge.poincareBound_of_mem hρ
    (original_poincare_mem hn (OpenAIBridge.admissible hρ hiso))

theorem best_current_original_class {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (13810833/1000000 : ℝ≥0∞)*energy μ f := original_poincare hn hμ hf

theorem current_universal_interval :
    (4 : ℝ≥0∞) ≤ universalPoincareConstant ∧ universalPoincareConstant ≤ (13810833/1000000 : ℝ≥0∞) :=
  ⟨KLS4Research.ExponentialOriginalSharpness.universal_poincareConstant_lower_four,universal_poincare_upper⟩

theorem current_openai_poincare {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) (13810833/1000000) := openai_poincare hn hρ hiso

theorem exponential_benchmark_original_class {n : ℕ} {f : Space n → ℝ}
    (hf : LocallyLipschitzTests (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f) :
    variance (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f ≤
      (4 : ℝ≥0∞)*energy (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f :=
  QuarticM20Bellman20261020Endpoint.exponential_benchmark_original_class hf

theorem current_bound_lt_previous : bound < QuarticM20Bellman20261020Endpoint.bound := by
  norm_num [bound,QuarticM20Bellman20261020Endpoint.bound]

theorem current_bound_gap_fourteen : 14-bound=(189167/1000000:ℝ) := by norm_num [bound]

end KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint
#check KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.universal_poincare_lt_fourteen
#print axioms KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.regular_poincare
#print axioms KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.original_poincare_mem
#print axioms KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.original_poincare
#print axioms KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.universal_poincare_upper
#print axioms KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.bound_lt_fourteen
#print axioms KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.universal_poincare_lt_fourteen
#print axioms KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.openai_poincare

#print axioms KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.best_current_original_class

#print axioms KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.current_universal_interval

#print axioms KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.current_openai_poincare

#print axioms KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.exponential_benchmark_original_class

#print axioms KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.current_bound_lt_previous

#print axioms KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.current_bound_gap_fourteen
