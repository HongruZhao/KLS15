import KLS15

/-! Separately compiled statement checks. There are no theorem placeholders. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace KLS15Challenge
open KLS

example {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ}
    (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (15 : ℝ≥0∞)*energy μ f :=
  KLS15.poincare15 hn hμ hf

example : OAI.LeanBlast.KLS.KLSStatement := KLS15.openaiKLS

end KLS15Challenge
#print axioms KLS15.poincare15_mem
#print axioms KLS15.poincare15
#print axioms KLS15.universalPoincareUpper15
#print axioms KLS15.openaiPoincare15
#print axioms KLS15.openaiKLS
