import KLSConstantImprovement.RawCubic336OperatorEndgame
import ActualKLS149963Endpoints

/-! The sole additional law-dependent premise is UniversalRawCubicBound 336.
All generator, scalar, actual operator, and regularization steps are proved
by this chain. The premise is not discharged by this module. -/
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff ENNReal NNReal
namespace KLSConstantImprovement.RawCubic336ConditionalEndpoint
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.RawCubic336WeightedProfileData
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

def bound : ℝ := 13999/1000

theorem regular_poincare
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound 336)
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hn : 0 < n) (hμ : admissibleMeasure (potentialMeasure φ)) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal bound := by
  have hnorm := RawCubic336OperatorEndgame.operator_norm_sq_le hφ hκ hlower hμ hraw
  have hb : 1+‖gradedTensorIntegration hφ hκ hlower‖^2 ≤ bound := by
    calc
      _ ≤ 1+K*p := by linarith
      _ = bound := RawCubic336WeightedProfile.exact_endpoint
  exact (poincareConstant_le_one_add_graded_norm_sq hφ hκ hlower hn hμ.isotropic).trans
    (ENNReal.ofReal_le_ofReal hb)

theorem original_poincare_mem
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound 336)
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (13999/1000 : ℝ≥0) ∈ poincareConstants μ := by
  apply mem_poincareConstants_of_paperRegularDensity hμ (by norm_num)
  intro ν hν hregular
  obtain ⟨V,κ,hV,hκ,hstrong,hupper,hgrowth,heq⟩ := hregular
  subst ν
  let : IsProbabilityMeasure (potentialMeasure V) := hν.isProb
  let hlower := coordinateHessian_lower_of_strongConvexOn (hV.of_le (by simp)) hstrong
  have hc := regular_poincare hraw hV hκ hlower (by omega) hν
  have hfin : poincareConstant (potentialMeasure V) < ⊤ := hc.trans_lt ENNReal.ofReal_lt_top
  apply (poincareConstants_iff_optimal_le (poincareConstants_nonempty_iff.mpr hfin)
    (hν.poincareConstant_pos hn)).mpr
  convert hc using 1
  unfold bound
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1000)]
  norm_num

theorem original_poincare
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound 336)
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (13999/1000 : ℝ≥0∞)*energy μ f := by
  simpa using original_poincare_mem hraw hn hμ f hf

theorem universal_poincare_upper
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound 336) :
    universalPoincareConstant ≤ (13999/1000 : ℝ≥0∞) := by
  apply universal_le_iff.mpr
  intro n hn μ hμ
  simpa using poincareConstant_le_of_mem (original_poincare_mem hraw hn hμ)

theorem bound_lt_fourteen : bound < 14 := by norm_num [bound]

theorem universal_poincare_lt_fourteen
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound 336) :
    universalPoincareConstant < 14 := by
  refine (universal_poincare_upper hraw).trans_lt ?_
  apply (ENNReal.toReal_lt_toReal
    (ENNReal.div_ne_top (by norm_num) (by norm_num)) (by norm_num)).mp
  norm_num

theorem openai_poincare
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound 336)
    {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) (13999/1000) :=
  OpenAIBridge.poincareBound_of_mem hρ
    (original_poincare_mem hraw hn (OpenAIBridge.admissible hρ hiso))

end KLSConstantImprovement.RawCubic336ConditionalEndpoint
#check KLSConstantImprovement.RawCubic336ConditionalEndpoint.universal_poincare_lt_fourteen
#print axioms KLSConstantImprovement.RawCubic336ConditionalEndpoint.regular_poincare
#print axioms KLSConstantImprovement.RawCubic336ConditionalEndpoint.original_poincare_mem
#print axioms KLSConstantImprovement.RawCubic336ConditionalEndpoint.original_poincare
#print axioms KLSConstantImprovement.RawCubic336ConditionalEndpoint.universal_poincare_upper
#print axioms KLSConstantImprovement.RawCubic336ConditionalEndpoint.bound_lt_fourteen
#print axioms KLSConstantImprovement.RawCubic336ConditionalEndpoint.universal_poincare_lt_fourteen
#print axioms KLSConstantImprovement.RawCubic336ConditionalEndpoint.openai_poincare
