import KLSConstantImprovement.ActualCubicVarianceIdentity
import KLSConstantImprovement.RawCubic336ConditionalEndpoint

/-! The complete original-class endpoint from one explicit open scientific
premise: the actual fixed-tensor tilt deficit has curvature at least
−(65/2)d. All polynomial/cumulant identities, signed contraction estimates,
L2 duality, and existing Bellman/regularization steps are proved.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal
namespace KLSConstantImprovement.ActualDeficitCurvatureConditionalEndpoint
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualFixedTensorDeficit ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicVarianceIdentity
variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

def UniversalDeficitCurvatureBound (k : ℝ) : Prop :=
  ∀ {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j),
      -k*sliceDeficit μ T ≤ contractedDeficitHessian μ T

theorem coefficientPolynomial_pairing {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    (∫ x,tensorPolynomial μ (actualCubicNextArray μ f) x*f x ∂μ)=actualAppellEnergy μ f 3 := by
  rw [←actualCubicNextArray_square μ f]
  simpa only [actualCubicNextArray,square,tripleSum,pow_two] using
    tensorPolynomial_pairing hμ (actualCubicNextArray μ f) hf

theorem coefficientPolynomial_covariance {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    covariance (tensorPolynomial μ (actualCubicNextArray μ f)) f μ=actualAppellEnergy μ f 3 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  rw [covariance_eq_sub (tensorPolynomial_memLp hμ _) hf,tensorPolynomial_centered hμ,
    zero_mul,sub_zero]
  simpa only [Pi.mul_apply] using coefficientPolynomial_pairing hμ hf

theorem rawCubic336_of_deficit_curvature (hcurvature : UniversalDeficitCurvatureBound (65/2)) :
    RawCubicWeightedBudget.UniversalRawCubicBound 336 := by
  intro n μ hμ f hf
  letI : IsProbabilityMeasure μ := hμ.isProb
  let T:=actualCubicNextArray μ f
  let N:=actualAppellEnergy μ f 3
  have hN:0≤N := actualAppellEnergy_nonneg _ _ _
  have hT12:=actualCubicNextArray_first_symmetry hμ.logConcave hf
  have hT23:=actualCubicNextArray_last_symmetry hμ.logConcave hf
  have hV:=tensorPolynomial_variance_le_336_of_curvature hμ T hT12 hT23
    (hcurvature hμ T hT12 hT23)
  change ProbabilityTheory.variance (tensorPolynomial μ T) μ ≤ 336*square (actualCubicNextArray μ f) at hV
  rw [actualCubicNextArray_square] at hV
  have hCS:=covariance_sq_le_variance_mul_variance (tensorPolynomial_memLp hμ T) hf
  rw [coefficientPolynomial_covariance hμ hf] at hCS
  change N^2 ≤ ProbabilityTheory.variance (tensorPolynomial μ T) μ*ProbabilityTheory.variance f μ at hCS
  have hp:=mul_le_mul_of_nonneg_right hV (ProbabilityTheory.variance_nonneg f μ)
  have hVF:ProbabilityTheory.variance f μ ≤ ∫ x,(f x)^2 ∂μ := by
    rw [ProbabilityTheory.variance_eq_sub hf]
    exact sub_le_self _ (sq_nonneg _)
  have hq:=mul_le_mul_of_nonneg_left hVF (show 0≤336*N by positivity)
  have hsq:N*N ≤ (336*(∫ x,(f x)^2 ∂μ))*N := by
    nlinarith [hCS.trans (hp.trans hq)]
  by_cases hzero:N=0
  · change N≤_
    rw [hzero]
    exact mul_nonneg (by norm_num) (integral_nonneg fun _=>sq_nonneg _)
  · have hpos:0<N := lt_of_le_of_ne hN (Ne.symm hzero)
    exact (mul_le_mul_iff_of_pos_right hpos).mp hsq

theorem original_poincare_mem (hcurvature : UniversalDeficitCurvatureBound (65/2))
    {n : ℕ} (hn : 1≤n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (13999/1000 : ℝ≥0)∈poincareConstants μ :=
  RawCubic336ConditionalEndpoint.original_poincare_mem (rawCubic336_of_deficit_curvature hcurvature) hn hμ

theorem original_poincare (hcurvature : UniversalDeficitCurvatureBound (65/2))
    {n : ℕ} (hn : 1≤n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n→ℝ} (hf : LocallyLipschitzTests μ f) :
    KLS.variance μ f ≤ (13999/1000 : ℝ≥0∞)*energy μ f :=
  RawCubic336ConditionalEndpoint.original_poincare (rawCubic336_of_deficit_curvature hcurvature) hn hμ hf

theorem universal_poincare_upper (hcurvature : UniversalDeficitCurvatureBound (65/2)) :
    universalPoincareConstant ≤ (13999/1000 : ℝ≥0∞) :=
  RawCubic336ConditionalEndpoint.universal_poincare_upper (rawCubic336_of_deficit_curvature hcurvature)

theorem universal_poincare_lt_fourteen (hcurvature : UniversalDeficitCurvatureBound (65/2)) :
    universalPoincareConstant < 14 :=
  RawCubic336ConditionalEndpoint.universal_poincare_lt_fourteen (rawCubic336_of_deficit_curvature hcurvature)

theorem openai_poincare (hcurvature : UniversalDeficitCurvatureBound (65/2))
    {n : ℕ} (hn : 1≤n) {ρ : OAI.LeanBlast.KLS.Space n→ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) (13999/1000) :=
  RawCubic336ConditionalEndpoint.openai_poincare (rawCubic336_of_deficit_curvature hcurvature) hn hρ hiso

end KLSConstantImprovement.ActualDeficitCurvatureConditionalEndpoint
#check KLSConstantImprovement.ActualDeficitCurvatureConditionalEndpoint.original_poincare
#check KLSConstantImprovement.ActualDeficitCurvatureConditionalEndpoint.universal_poincare_lt_fourteen
#print axioms KLSConstantImprovement.ActualDeficitCurvatureConditionalEndpoint.coefficientPolynomial_pairing
#print axioms KLSConstantImprovement.ActualDeficitCurvatureConditionalEndpoint.coefficientPolynomial_covariance
#print axioms KLSConstantImprovement.ActualDeficitCurvatureConditionalEndpoint.rawCubic336_of_deficit_curvature
#print axioms KLSConstantImprovement.ActualDeficitCurvatureConditionalEndpoint.original_poincare_mem
#print axioms KLSConstantImprovement.ActualDeficitCurvatureConditionalEndpoint.original_poincare
#print axioms KLSConstantImprovement.ActualDeficitCurvatureConditionalEndpoint.universal_poincare_upper
#print axioms KLSConstantImprovement.ActualDeficitCurvatureConditionalEndpoint.universal_poincare_lt_fourteen
#print axioms KLSConstantImprovement.ActualDeficitCurvatureConditionalEndpoint.openai_poincare
