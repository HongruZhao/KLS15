import ActualProjectionThreeHeadRefinedOperatorEndgame

/-! Unconditional original-class and unchanged OpenAI KLS endpoints.
The finite coupled Appell estimate, cubic cap, compatible tensor geometry,
actual shared-resource projection slack and finite conditional-payment bootstrap are all discharged internally. -/
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff ENNReal NNReal
namespace KLS14452512512
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 110000000
set_option backward.isDefEq.respectTransparency false

theorem regularPoincare14452512512
    {n : ℕ} {φ : Space n→ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0<κ)
    (hlower : ∀ x (a : Fin n→ℝ),
      κ*(a ⬝ᵥ a)≤a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hn : 0<n) (hμ : admissibleMeasure (potentialMeasure φ)) :
    poincareConstant (potentialMeasure φ)≤ENNReal.ofReal ((56455127 : ℝ)/3906250) := by
  have hb := actual_projection_three_head_refined_operator_norm_sq_le hφ hκ hlower hμ
  have hh : 1+‖gradedTensorIntegration hφ hκ hlower‖^2 ≤
      (56455127 : ℝ)/3906250 := by
    rw [←KLSBelow25.ProjectionThreeHeadRefinedNumerics.endpoint_value]
    linarith
  exact (poincareConstant_le_one_add_graded_norm_sq hφ hκ hlower hn hμ.isotropic).trans
    (ENNReal.ofReal_le_ofReal hh)

theorem poincare14452512512_mem {n : ℕ} (hn : 1≤n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (56455127/3906250 : ℝ≥0) ∈ poincareConstants μ := by
  apply mem_poincareConstants_of_paperRegularDensity hμ (by norm_num)
  intro ν hν hregular
  obtain ⟨V,κ,hV,hκ,hstrong,hupper,hgrowth,heq⟩ := hregular
  subst ν
  let : IsProbabilityMeasure (potentialMeasure V) := hν.isProb
  let hlower := coordinateHessian_lower_of_strongConvexOn (hV.of_le (by simp)) hstrong
  have hc := regularPoincare14452512512 hV hκ hlower (by omega) hν
  have hfin : poincareConstant (potentialMeasure V)<⊤ := hc.trans_lt ENNReal.ofReal_lt_top
  apply (poincareConstants_iff_optimal_le (poincareConstants_nonempty_iff.mpr hfin)
    (hν.poincareConstant_pos hn)).mpr
  convert hc using 1
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ)<3906250)]
  norm_num

theorem poincare14452512512 {n : ℕ} (hn : 1≤n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n→ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f≤(56455127/3906250 : ℝ≥0∞)*energy μ f := by
  simpa using poincare14452512512_mem hn hμ f hf

theorem universalPoincareUpper14452512512 :
    universalPoincareConstant≤(56455127/3906250 : ℝ≥0∞) := by
  apply universal_le_iff.mpr
  intro n hn μ hμ
  simpa using poincareConstant_le_of_mem (poincare14452512512_mem hn hμ)

theorem universalPoincareUpper_lt_fifteen : universalPoincareConstant<15 := by
  apply universalPoincareUpper14452512512.trans_lt
  apply (ENNReal.div_lt_iff (Or.inl (by norm_num : (3906250 : ℝ≥0∞)≠0))
    (Or.inl (by simp : (3906250 : ℝ≥0∞)≠⊤))).mpr
  norm_num

theorem universalPoincareUpper_lt_fourteen_four_six : universalPoincareConstant<(1446/100 : ℝ≥0∞) := by
  apply universalPoincareUpper14452512512.trans_lt
  have hleft : (56455127/3906250 : ℝ≥0∞)=ENNReal.ofReal ((56455127 : ℝ)/3906250) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ)<3906250)]
    norm_num
  have hright : (1446/100 : ℝ≥0∞)=ENNReal.ofReal ((1446 : ℝ)/100) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ)<100)]
    norm_num
  rw [hleft,hright]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ)<1446/100)).mpr (by norm_num)

theorem openaiPoincare14452512512 {n : ℕ} (hn : 1≤n)
    {ρ : OAI.LeanBlast.KLS.Space n→ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) ((56455127 : ℝ)/3906250) :=
  OpenAIBridge.poincareBound_of_mem hρ
    (poincare14452512512_mem hn (OpenAIBridge.admissible hρ hiso))

theorem openaiKLS14452512512 : OAI.LeanBlast.KLS.KLSStatement := by
  refine ⟨(56455127/3906250 : ℝ),by norm_num,?_⟩
  intro n hn ρ hρ hiso
  exact openaiPoincare14452512512 hn hρ hiso

end KLS14452512512
#check KLS14452512512.poincare14452512512_mem
#check KLS14452512512.poincare14452512512
#check KLS14452512512.universalPoincareUpper14452512512
#check KLS14452512512.universalPoincareUpper_lt_fifteen
#check KLS14452512512.universalPoincareUpper_lt_fourteen_four_six
#check KLS14452512512.openaiPoincare14452512512
#check KLS14452512512.openaiKLS14452512512
#print axioms KLS14452512512.regularPoincare14452512512
#print axioms KLS14452512512.poincare14452512512_mem
#print axioms KLS14452512512.poincare14452512512
#print axioms KLS14452512512.universalPoincareUpper14452512512
#print axioms KLS14452512512.universalPoincareUpper_lt_fifteen
#print axioms KLS14452512512.universalPoincareUpper_lt_fourteen_four_six
#print axioms KLS14452512512.openaiPoincare14452512512
#print axioms KLS14452512512.openaiKLS14452512512

