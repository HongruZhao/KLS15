import ActualSchurEndpoint
import ActualWeightedAppellViaGram

/-!
Complete endpoint using the replacements on the actual original carriers:
the smaller cubic cap 24.45 from the retained Gram, both individually and in
the coupled Appell induction, and exact affine Schur
in the final rank-zero primitive step.  Constants and all-law hypotheses are
unchanged.  No universal bound at four is claimed.
-/
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff ENNReal NNReal
namespace KLSImprovement.UpdatedEndpoint
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSImprovement.OperatorThreshold14992816
open KLSImprovement.ActualAffineSchur KLSImprovement.ActualSchurEndpoint
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The complete regular endpoint now passes through the exact actual Schur
condition instead of the former primitive triangle estimate. -/
theorem regularPoincareUpdated
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hn : 0 < n) (hμ : admissibleMeasure (potentialMeasure φ)) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal bound := by
  apply poincareConstant_le_of_actual_joint_schur hφ hκ hlower hn hμ.isotropic
    (by norm_num [bound])
  apply actual_joint_schur_of_graded_norm_bound hφ hκ hlower hμ.isotropic
    (by norm_num [bound])
  apply graded_norm_of_unchanged_analytic_bounds hφ hκ hlower hμ
  · intro N f
    exact actual_weighted_appell_energy_thirteen_four_via_gram_norm_sq_le N hμ f
  · intro f
    have hb := actual_appell_energy_three_le_2445_norm_sq hμ f
    nlinarith [sq_nonneg ‖f‖]

theorem poincareUpdated_mem {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (937051 / 62500 : ℝ≥0) ∈ poincareConstants μ := by
  apply mem_poincareConstants_of_paperRegularDensity hμ (by norm_num)
  intro ν hν hregular
  obtain ⟨V, κ, hV, hκ, hstrong, hupper, hgrowth, heq⟩ := hregular
  subst ν
  let : IsProbabilityMeasure (potentialMeasure V) := hν.isProb
  let hlower := coordinateHessian_lower_of_strongConvexOn (hV.of_le (by simp)) hstrong
  have hc := regularPoincareUpdated hV hκ hlower (by omega) hν
  have hfin : poincareConstant (potentialMeasure V) < ⊤ := hc.trans_lt ENNReal.ofReal_lt_top
  apply (poincareConstants_iff_optimal_le (poincareConstants_nonempty_iff.mpr hfin)
    (hν.poincareConstant_pos hn)).mpr
  convert hc using 1
  unfold bound
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 62500)]
  norm_num

theorem poincareUpdated {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (937051 / 62500 : ℝ≥0∞) * energy μ f := by
  simpa using poincareUpdated_mem hn hμ f hf

theorem universalPoincareUpperUpdated :
    universalPoincareConstant ≤ (937051 / 62500 : ℝ≥0∞) := by
  apply universal_le_iff.mpr
  intro n hn μ hμ
  simpa using poincareConstant_le_of_mem (poincareUpdated_mem hn hμ)

theorem openaiPoincareUpdated {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ)
      ((937051 : ℝ) / 62500) :=
  OpenAIBridge.poincareBound_of_mem hρ
    (poincareUpdated_mem hn (OpenAIBridge.admissible hρ hiso))

theorem openaiKLSUpdated : OAI.LeanBlast.KLS.KLSStatement := by
  refine ⟨((937051 : ℝ) / 62500), by norm_num, ?_⟩
  intro n hn ρ hρ hiso
  exact openaiPoincareUpdated hn hρ hiso

end KLSImprovement.UpdatedEndpoint

#print axioms KLSImprovement.UpdatedEndpoint.regularPoincareUpdated
#print axioms KLSImprovement.UpdatedEndpoint.poincareUpdated_mem
#print axioms KLSImprovement.UpdatedEndpoint.poincareUpdated
#print axioms KLSImprovement.UpdatedEndpoint.universalPoincareUpperUpdated
#print axioms KLSImprovement.UpdatedEndpoint.openaiPoincareUpdated
#print axioms KLSImprovement.UpdatedEndpoint.openaiKLSUpdated
