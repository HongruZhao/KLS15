import ActualRegularEndpointSub15
import ActualWeightedAppellInductionSub15
import ActualSymmetricCubicSeed245Cap

/-! Unconditional original-class and unchanged OpenAI KLS endpoints.
The finite coupled Appell estimate, cubic cap, compatible tensor geometry,
and sharpened two-head operator endgame are all discharged by imports. -/
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff ENNReal NNReal
namespace KLS149963
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem regularPoincare149963
    {n : ℕ} {φ : Space n→ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0<κ)
    (hlower : ∀ x (a : Fin n→ℝ),
      κ*(a ⬝ᵥ a)≤a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hn : 0<n) (hμ : admissibleMeasure (potentialMeasure φ)) :
    poincareConstant (potentialMeasure φ)≤ENNReal.ofReal ((149963 : ℝ)/10000) := by
  apply actual_regular_poincare_sub15_of_coupled_and_three hφ hκ hlower hn hμ
  · intro N f
    exact actual_weighted_appell_energy_thirteen_four_norm_sq_le N hμ f
  · intro f
    simpa only [KLSBelow25.SymmetricCenteredSeed245.B] using
      actual_appell_energy_three_symmetric245_le_norm_sq hμ f

theorem poincare149963_mem {n : ℕ} (hn : 1≤n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (149963/10000 : ℝ≥0) ∈ poincareConstants μ := by
  apply mem_poincareConstants_of_paperRegularDensity hμ (by norm_num)
  intro ν hν hregular
  obtain ⟨V,κ,hV,hκ,hstrong,hupper,hgrowth,heq⟩ := hregular
  subst ν
  let : IsProbabilityMeasure (potentialMeasure V) := hν.isProb
  let hlower := coordinateHessian_lower_of_strongConvexOn (hV.of_le (by simp)) hstrong
  have hc := regularPoincare149963 hV hκ hlower (by omega) hν
  have hfin : poincareConstant (potentialMeasure V)<⊤ := hc.trans_lt ENNReal.ofReal_lt_top
  apply (poincareConstants_iff_optimal_le (poincareConstants_nonempty_iff.mpr hfin)
    (hν.poincareConstant_pos hn)).mpr
  convert hc using 1
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ)<10000)]
  norm_num

theorem poincare149963 {n : ℕ} (hn : 1≤n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n→ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f≤(149963/10000 : ℝ≥0∞)*energy μ f := by
  simpa using poincare149963_mem hn hμ f hf

theorem universalPoincareUpper149963 :
    universalPoincareConstant≤(149963/10000 : ℝ≥0∞) := by
  apply universal_le_iff.mpr
  intro n hn μ hμ
  simpa using poincareConstant_le_of_mem (poincare149963_mem hn hμ)

theorem universalPoincareUpper_lt_fifteen : universalPoincareConstant<15 := by
  apply universalPoincareUpper149963.trans_lt
  apply (ENNReal.div_lt_iff (Or.inl (by norm_num : (10000 : ℝ≥0∞)≠0))
    (Or.inl (by simp : (10000 : ℝ≥0∞)≠⊤))).mpr
  norm_num

theorem openaiPoincare149963 {n : ℕ} (hn : 1≤n)
    {ρ : OAI.LeanBlast.KLS.Space n→ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) ((149963 : ℝ)/10000) :=
  OpenAIBridge.poincareBound_of_mem hρ
    (poincare149963_mem hn (OpenAIBridge.admissible hρ hiso))

theorem openaiKLS149963 : OAI.LeanBlast.KLS.KLSStatement := by
  refine ⟨(149963/10000 : ℝ),by norm_num,?_⟩
  intro n hn ρ hρ hiso
  exact openaiPoincare149963 hn hρ hiso

end KLS149963
#check KLS149963.poincare149963_mem
#check KLS149963.poincare149963
#check KLS149963.universalPoincareUpper149963
#check KLS149963.universalPoincareUpper_lt_fifteen
#check KLS149963.openaiPoincare149963
#check KLS149963.openaiKLS149963
#print axioms KLS149963.regularPoincare149963
#print axioms KLS149963.poincare149963_mem
#print axioms KLS149963.poincare149963
#print axioms KLS149963.universalPoincareUpper149963
#print axioms KLS149963.universalPoincareUpper_lt_fifteen
#print axioms KLS149963.openaiPoincare149963
#print axioms KLS149963.openaiKLS149963
