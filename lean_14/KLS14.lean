import KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint

/-! Public release endpoints. The imported theorem supplies every analytic
input; these wrappers only expose the exact bound and its integer corollary.
The upstream OAI/Analysis/KLS/Model.lean definitions remain unchanged. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace OpenAIModel

/-- Transparent compatibility name for the unchanged upstream proposition. -/
abbrev openaiKLSStatement : Prop := OAI.LeanBlast.KLS.KLSStatement

end OpenAIModel

namespace KLS14
open KLS

def bestBound : ℝ := 13810833 / 1000000

theorem bestBound_lt_fourteen : bestBound < 14 := by
  norm_num [bestBound]

theorem poincareBest_mem {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (13810833 / 1000000 : ℝ≥0) ∈ poincareConstants μ :=
  KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.original_poincare_mem hn hμ

theorem poincareBest {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (13810833 / 1000000 : ℝ≥0∞) * energy μ f :=
  KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.original_poincare hn hμ hf

theorem universalPoincareUpperBest :
    universalPoincareConstant ≤ (13810833 / 1000000 : ℝ≥0∞) :=
  KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.universal_poincare_upper

theorem poincare14_mem {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (14 : ℝ≥0) ∈ poincareConstants μ :=
  poincareConstants_mono (poincareBest_mem hn hμ)
    (by exact_mod_cast (by norm_num : (13810833 / 1000000 : ℝ) ≤ 14))

theorem poincare14 {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (14 : ℝ≥0∞) * energy μ f :=
  poincare14_mem hn hμ f hf

theorem universalPoincareUpper14 : universalPoincareConstant ≤ 14 :=
  KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.universal_poincare_lt_fourteen.le

theorem openaiPoincareBest {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ)
      (13810833 / 1000000) :=
  KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint.openai_poincare hn hρ hiso

theorem openaiPoincare14 {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) 14 :=
  KLS.OpenAIBridge.poincareBound_of_mem hρ
    (poincare14_mem hn (KLS.OpenAIBridge.admissible hρ hiso))

/-- The existential OpenAI statement with the explicit universal witness14. -/
theorem openaiKLS : OAI.LeanBlast.KLS.KLSStatement := by
  refine ⟨14, by norm_num, ?_⟩
  intro n hn ρ hρ hiso
  exact openaiPoincare14 hn hρ hiso

end KLS14
