import ActualKLS15VerifiedEndpoints

/-! Public constant-15 endpoint. All analytic hypotheses are discharged by the
imported development; only the intended law and test assumptions remain. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace KLS15
open KLS

theorem poincare15_mem {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (15 : ℝ≥0) ∈ poincareConstants μ :=
  KLS15Verified.poincare15_mem hn hμ

theorem poincare15 {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (15 : ℝ≥0∞)*energy μ f :=
  KLS15Verified.poincare15 hn hμ hf

theorem universalPoincareUpper15 : universalPoincareConstant ≤ 15 :=
  KLS15Verified.universalPoincareUpper15

theorem openaiPoincare15 {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) 15 :=
  KLS15Verified.openaiPoincare15 hn hρ hiso

theorem openaiKLS : OAI.LeanBlast.KLS.KLSStatement :=
  KLS15Verified.openaiKLS15

end KLS15
#print axioms KLS15.poincare15
#print axioms KLS15.openaiKLS
