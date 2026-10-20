import KLSConstantImprovement.CubicVarianceFourthSector
import KLSConstantImprovement.LiteralCubicVarianceObservationTransfer
import KLSConstantImprovement.RawCubic336ConditionalEndpoint

/-! The joint original-law Bessel bound relaxes the sole open universal
curvature premise from 65/2 to 93/2. The literal variance-to-observation
transfer and the existing Bellman/regularization endpoint then give 13.999.
The displayed curvature premise is an explicit theorem argument, not a
proved unconditional estimate. The earlier endpoint is preserved. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace KLSConstantImprovement.ActualDeficitCurvatureRelaxedEndpoint
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitCurvatureConditionalEndpoint LiteralCubicVarianceObservationTransfer
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem literal_cubic_variance_le_336
    (hcurvature : UniversalDeficitCurvatureBound (93/2)) :
    UniversalLiteralCubicVarianceBound 336 := by
  intro n μ hμ T hT12 hT23
  exact CubicVarianceFourthSector.tensorPolynomial_variance_le_336_of_curvature93over2
    hμ T hT12 hT23 (hcurvature hμ T hT12 hT23)

theorem rawCubic336_of_deficit_curvature
    (hcurvature : UniversalDeficitCurvatureBound (93/2)) :
    RawCubicWeightedBudget.UniversalRawCubicBound 336 :=
  rawCubic336_of_tensor_variance (literal_cubic_variance_le_336 hcurvature)

theorem original_poincare_mem (hcurvature : UniversalDeficitCurvatureBound (93/2))
    {n : ℕ} (hn : 1≤n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (13999/1000 : ℝ≥0)∈poincareConstants μ :=
  RawCubic336ConditionalEndpoint.original_poincare_mem
    (rawCubic336_of_deficit_curvature hcurvature) hn hμ

theorem original_poincare (hcurvature : UniversalDeficitCurvatureBound (93/2))
    {n : ℕ} (hn : 1≤n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n→ℝ} (hf : LocallyLipschitzTests μ f) :
    KLS.variance μ f ≤ (13999/1000 : ℝ≥0∞)*energy μ f :=
  RawCubic336ConditionalEndpoint.original_poincare
    (rawCubic336_of_deficit_curvature hcurvature) hn hμ hf

theorem universal_poincare_upper (hcurvature : UniversalDeficitCurvatureBound (93/2)) :
    universalPoincareConstant ≤ (13999/1000 : ℝ≥0∞) :=
  RawCubic336ConditionalEndpoint.universal_poincare_upper
    (rawCubic336_of_deficit_curvature hcurvature)

theorem universal_poincare_lt_fourteen
    (hcurvature : UniversalDeficitCurvatureBound (93/2)) :
    universalPoincareConstant < 14 :=
  RawCubic336ConditionalEndpoint.universal_poincare_lt_fourteen
    (rawCubic336_of_deficit_curvature hcurvature)

theorem openai_poincare (hcurvature : UniversalDeficitCurvatureBound (93/2))
    {n : ℕ} (hn : 1≤n) {ρ : OAI.LeanBlast.KLS.Space n→ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) (13999/1000) :=
  RawCubic336ConditionalEndpoint.openai_poincare
    (rawCubic336_of_deficit_curvature hcurvature) hn hρ hiso

end KLSConstantImprovement.ActualDeficitCurvatureRelaxedEndpoint
#check KLSConstantImprovement.ActualDeficitCurvatureRelaxedEndpoint.original_poincare
#check KLSConstantImprovement.ActualDeficitCurvatureRelaxedEndpoint.universal_poincare_lt_fourteen
#print axioms KLSConstantImprovement.ActualDeficitCurvatureRelaxedEndpoint.literal_cubic_variance_le_336
#print axioms KLSConstantImprovement.ActualDeficitCurvatureRelaxedEndpoint.rawCubic336_of_deficit_curvature
#print axioms KLSConstantImprovement.ActualDeficitCurvatureRelaxedEndpoint.original_poincare_mem
#print axioms KLSConstantImprovement.ActualDeficitCurvatureRelaxedEndpoint.original_poincare
#print axioms KLSConstantImprovement.ActualDeficitCurvatureRelaxedEndpoint.universal_poincare_upper
#print axioms KLSConstantImprovement.ActualDeficitCurvatureRelaxedEndpoint.universal_poincare_lt_fourteen
#print axioms KLSConstantImprovement.ActualDeficitCurvatureRelaxedEndpoint.openai_poincare
