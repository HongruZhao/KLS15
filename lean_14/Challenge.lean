import KLS14

/-! Separate public statement checks; no strengthened law or test premises. -/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace KLS14Challenge
open KLS

example : universalPoincareConstant ≤ 14 := KLS14.universalPoincareUpper14

example {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ}
    (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (14 : ℝ≥0∞) * energy μ f :=
  KLS14.poincare14 hn hμ hf

example {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ}
    (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (13810833 / 1000000 : ℝ≥0∞) * energy μ f :=
  KLS14.poincareBest hn hμ hf

example : OAI.LeanBlast.KLS.KLSStatement := KLS14.openaiKLS

example : OpenAIModel.openaiKLSStatement := KLS14.openaiKLS

end KLS14Challenge
