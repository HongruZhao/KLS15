import KLSConstantImprovement.ActualCubicPoincareFourthSector
import KLSConstantImprovement.LiteralCubicVarianceObservationTransfer
import KLSConstantImprovement.RawCubic336ConditionalEndpoint

/-! The proved current Poincare bound pays the low-fourth sector of the literal
cubic polynomial. The sole remaining scientific argument is curvature 48 only
when F>N/2. It implies literal variance/raw cubic 333 and hence the existing
13.999 original-class and universal endpoints. Dimension zero is discharged
directly by the empty tensor sums. The global sector curvature is not proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace KLSConstantImprovement.ActualDeficitCurvatureSectorEndpoint
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualFixedTensorDeficit ActualCubicRepresenter
open ActualDeficitCurvatureConditionalEndpoint LiteralCubicVarianceObservationTransfer
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

def UniversalHighFourthSectorCurvatureBound (k : ℝ) : Prop :=
  ∀ {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j),
      tensorSquare T/2<fourthContraction μ T →
      -k*sliceDeficit μ T≤contractedDeficitHessian μ T

theorem high_sector_curvature_of_global {k : ℝ}
    (hcurvature : UniversalDeficitCurvatureBound k) :
    UniversalHighFourthSectorCurvatureBound k := by
  intro n μ hμ T hT12 hT23 _
  exact hcurvature hμ T hT12 hT23

theorem literal_cubic_variance_le_333
    (hcurvature : UniversalHighFourthSectorCurvatureBound 48) :
    UniversalLiteralCubicVarianceBound 333 := by
  intro n μ hμ T hT12 hT23
  cases n with
  | zero =>
      have hz : tensorPolynomial μ T=(fun _ => 0) := by
        funext x
        simp [tensorPolynomial]
      rw [hz]
      change ProbabilityTheory.variance (0 : Space 0→ℝ) μ≤_
      rw [ProbabilityTheory.variance_zero]
      simp [tensorSquare,square,tripleSum]
  | succ n =>
      exact ActualCubicPoincareFourthSector.tensorPolynomial_variance_le_333_of_high_sector_curvature
        (by omega) hμ T hT12 hT23 (hcurvature hμ T hT12 hT23)

theorem literal_cubic_variance_le_336
    (hcurvature : UniversalHighFourthSectorCurvatureBound 48) :
    UniversalLiteralCubicVarianceBound 336 := by
  intro n μ hμ T hT12 hT23
  exact (literal_cubic_variance_le_333 hcurvature hμ T hT12 hT23).trans
    (mul_le_mul_of_nonneg_right (by norm_num : (333 : ℝ)≤336)
      (CubicVarianceFourthSector.tensorSquare_nonneg T))

theorem rawCubic333_of_high_sector_curvature
    (hcurvature : UniversalHighFourthSectorCurvatureBound 48) :
    RawCubicWeightedBudget.UniversalRawCubicBound 333 :=
  rawCubicBound_of_tensor_variance (by norm_num) (literal_cubic_variance_le_333 hcurvature)

theorem rawCubic336_of_high_sector_curvature
    (hcurvature : UniversalHighFourthSectorCurvatureBound 48) :
    RawCubicWeightedBudget.UniversalRawCubicBound 336 :=
  rawCubic336_of_tensor_variance (literal_cubic_variance_le_336 hcurvature)

theorem original_poincare_mem (hcurvature : UniversalHighFourthSectorCurvatureBound 48)
    {n : ℕ} (hn : 1≤n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (13999/1000 : ℝ≥0)∈poincareConstants μ :=
  RawCubic336ConditionalEndpoint.original_poincare_mem
    (rawCubic336_of_high_sector_curvature hcurvature) hn hμ

theorem original_poincare (hcurvature : UniversalHighFourthSectorCurvatureBound 48)
    {n : ℕ} (hn : 1≤n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n→ℝ} (hf : LocallyLipschitzTests μ f) :
    KLS.variance μ f ≤ (13999/1000 : ℝ≥0∞)*energy μ f :=
  RawCubic336ConditionalEndpoint.original_poincare
    (rawCubic336_of_high_sector_curvature hcurvature) hn hμ hf

theorem universal_poincare_upper (hcurvature : UniversalHighFourthSectorCurvatureBound 48) :
    universalPoincareConstant ≤ (13999/1000 : ℝ≥0∞) :=
  RawCubic336ConditionalEndpoint.universal_poincare_upper
    (rawCubic336_of_high_sector_curvature hcurvature)

theorem universal_poincare_lt_fourteen
    (hcurvature : UniversalHighFourthSectorCurvatureBound 48) :
    universalPoincareConstant < 14 :=
  RawCubic336ConditionalEndpoint.universal_poincare_lt_fourteen
    (rawCubic336_of_high_sector_curvature hcurvature)

theorem openai_poincare (hcurvature : UniversalHighFourthSectorCurvatureBound 48)
    {n : ℕ} (hn : 1≤n) {ρ : OAI.LeanBlast.KLS.Space n→ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) (13999/1000) :=
  RawCubic336ConditionalEndpoint.openai_poincare
    (rawCubic336_of_high_sector_curvature hcurvature) hn hρ hiso

end KLSConstantImprovement.ActualDeficitCurvatureSectorEndpoint
#check KLSConstantImprovement.ActualDeficitCurvatureSectorEndpoint.original_poincare
#check KLSConstantImprovement.ActualDeficitCurvatureSectorEndpoint.universal_poincare_lt_fourteen
#print axioms KLSConstantImprovement.ActualDeficitCurvatureSectorEndpoint.high_sector_curvature_of_global
#print axioms KLSConstantImprovement.ActualDeficitCurvatureSectorEndpoint.literal_cubic_variance_le_333
#print axioms KLSConstantImprovement.ActualDeficitCurvatureSectorEndpoint.literal_cubic_variance_le_336
#print axioms KLSConstantImprovement.ActualDeficitCurvatureSectorEndpoint.rawCubic333_of_high_sector_curvature
#print axioms KLSConstantImprovement.ActualDeficitCurvatureSectorEndpoint.rawCubic336_of_high_sector_curvature
#print axioms KLSConstantImprovement.ActualDeficitCurvatureSectorEndpoint.original_poincare_mem
#print axioms KLSConstantImprovement.ActualDeficitCurvatureSectorEndpoint.original_poincare
#print axioms KLSConstantImprovement.ActualDeficitCurvatureSectorEndpoint.universal_poincare_upper
#print axioms KLSConstantImprovement.ActualDeficitCurvatureSectorEndpoint.universal_poincare_lt_fourteen
#print axioms KLSConstantImprovement.ActualDeficitCurvatureSectorEndpoint.openai_poincare
