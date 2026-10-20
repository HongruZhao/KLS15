import KLSConstantImprovement.RefinedTripleThreeHeadOperatorEndgame
import ActualKLS149963Endpoints
import KLSConstantImprovement.RefinedTripleWeightedProfile

/-! Unconditional original-class endpoint from the exact all-rank profile.
Every scalar and actual analytic premise is discharged by the imported chain.
The bound is 14.365931903, strictly below 14.366; fourteen remains open. -/
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff ENNReal NNReal
namespace KLSConstantImprovement.RefinedTripleUniversalEndpoint
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.RefinedTripleThreeHeadOperatorEndgame
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def bound : ℝ := 14365931903/1000000000

theorem regular_poincare
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hn : 0 < n) (hμ : admissibleMeasure (potentialMeasure φ)) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal bound := by
  have hnorm := actual_refined_triple_three_head_operator_norm_sq_le hφ hκ hlower hμ
    RefinedTripleWeightedProfileData.t RefinedTripleWeightedProfile.t_floor
    RefinedTripleWeightedProfile.t_two RefinedTripleWeightedProfile.t_three RefinedTripleWeightedProfile.t_four
    (fun N f => RefinedTripleWeightedProfile.raw_budget_norm_sq N hμ f)
  have hb : 1+‖gradedTensorIntegration hφ hκ hlower‖^2 ≤ bound := by
    calc
      _ ≤ 1+KLSConstantImprovement.RefinedTripleThreeHeadNumerics.K*
          KLSConstantImprovement.RefinedTripleThreeHeadNumerics.p := by linarith
      _ = bound := KLSConstantImprovement.RefinedTripleThreeHeadNumerics.endpoint_value
  exact (poincareConstant_le_one_add_graded_norm_sq hφ hκ hlower hn hμ.isotropic).trans
    (ENNReal.ofReal_le_ofReal hb)

theorem original_poincare_mem {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (14365931903/1000000000 : ℝ≥0) ∈ poincareConstants μ := by
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
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1000000000)]
  norm_num

theorem original_poincare {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (14365931903/1000000000 : ℝ≥0∞)*energy μ f := by
  simpa using original_poincare_mem hn hμ f hf

theorem universal_poincare_upper :
    universalPoincareConstant ≤ (14365931903/1000000000 : ℝ≥0∞) := by
  apply universal_le_iff.mpr
  intro n hn μ hμ
  simpa using poincareConstant_le_of_mem (original_poincare_mem hn hμ)

theorem bound_lt_previous : bound < (28742133 : ℝ)/2000000 := by
  norm_num [bound]

theorem bound_lt_14366 : bound < 7183/500 := by
  norm_num [bound]

theorem openai_poincare {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ)
      ((14365931903 : ℝ)/1000000000) :=
  OpenAIBridge.poincareBound_of_mem hρ
    (original_poincare_mem hn (OpenAIBridge.admissible hρ hiso))

end KLSConstantImprovement.RefinedTripleUniversalEndpoint
#print axioms KLSConstantImprovement.RefinedTripleUniversalEndpoint.regular_poincare
#print axioms KLSConstantImprovement.RefinedTripleUniversalEndpoint.original_poincare_mem
#print axioms KLSConstantImprovement.RefinedTripleUniversalEndpoint.original_poincare
#print axioms KLSConstantImprovement.RefinedTripleUniversalEndpoint.universal_poincare_upper
#print axioms KLSConstantImprovement.RefinedTripleUniversalEndpoint.bound_lt_previous
#print axioms KLSConstantImprovement.RefinedTripleUniversalEndpoint.openai_poincare

#print axioms KLSConstantImprovement.RefinedTripleUniversalEndpoint.bound_lt_14366
