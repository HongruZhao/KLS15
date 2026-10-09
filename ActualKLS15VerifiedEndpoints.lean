import ActualKLS149963Endpoints

/-! Explicit constant-15 corollaries of the frozen strict sub15 endpoint.
No new analytic input or changed class is introduced. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace KLS15Verified
open KLS

theorem poincare15_mem {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (15 : ℝ≥0) ∈ poincareConstants μ :=
  poincareConstants_mono (KLS149963.poincare149963_mem hn hμ)
    (by exact_mod_cast (by norm_num : (149963/10000 : ℝ) ≤ 15))

theorem poincare15 {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (15 : ℝ≥0∞)*energy μ f := by
  simpa using poincare15_mem hn hμ f hf

theorem universalPoincareUpper15 : universalPoincareConstant ≤ 15 :=
  KLS149963.universalPoincareUpper_lt_fifteen.le

theorem openaiPoincare15 {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) 15 :=
  OpenAIBridge.poincareBound_of_mem hρ
    (poincare15_mem hn (OpenAIBridge.admissible hρ hiso))

theorem openaiKLS15 : OAI.LeanBlast.KLS.KLSStatement := by
  refine ⟨(15 : ℝ),by norm_num,?_⟩
  intro n hn ρ hρ hiso
  exact openaiPoincare15 hn hρ hiso

end KLS15Verified
#check KLS15Verified.poincare15_mem
#check KLS15Verified.poincare15
#check KLS15Verified.universalPoincareUpper15
#check KLS15Verified.openaiPoincare15
#check KLS15Verified.openaiKLS15
#print axioms KLS15Verified.poincare15_mem
#print axioms KLS15Verified.poincare15
#print axioms KLS15Verified.universalPoincareUpper15
#print axioms KLS15Verified.openaiPoincare15
#print axioms KLS15Verified.openaiKLS15
