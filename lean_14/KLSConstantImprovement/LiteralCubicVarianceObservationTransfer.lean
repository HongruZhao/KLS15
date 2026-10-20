import KLSConstantImprovement.ActualDeficitCurvatureConditionalEndpoint

/-! General actual literal cubic polynomial variance-to-observation
transfer. This accepts any proved constant for the same original-law
polynomial; it has no tensor curvature or law identification premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSConstantImprovement.LiteralCubicVarianceObservationTransfer
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter ActualDeficitCurvatureConditionalEndpoint
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def UniversalLiteralCubicVarianceBound (H : ℝ) : Prop :=
  ∀ {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j),
      ProbabilityTheory.variance (tensorPolynomial μ T) μ ≤ H*tensorSquare T

theorem rawCubicBound_of_tensor_variance {H : ℝ} (hH : 0≤H)
    (hcap : UniversalLiteralCubicVarianceBound H) : RawCubicWeightedBudget.UniversalRawCubicBound H := by
  intro n μ hμ f hf
  letI : IsProbabilityMeasure μ := hμ.isProb
  let T:=actualCubicNextArray μ f
  let N:=actualAppellEnergy μ f 3
  have hN:0≤N := actualAppellEnergy_nonneg _ _ _
  have hV:=hcap hμ T (actualCubicNextArray_first_symmetry hμ.logConcave hf)
    (actualCubicNextArray_last_symmetry hμ.logConcave hf)
  change ProbabilityTheory.variance (tensorPolynomial μ T) μ ≤ H*square (actualCubicNextArray μ f) at hV
  rw [actualCubicNextArray_square] at hV
  have hCS:=covariance_sq_le_variance_mul_variance (tensorPolynomial_memLp hμ T) hf
  rw [coefficientPolynomial_covariance hμ hf] at hCS
  change N^2 ≤ ProbabilityTheory.variance (tensorPolynomial μ T) μ*ProbabilityTheory.variance f μ at hCS
  have hp:=mul_le_mul_of_nonneg_right hV (ProbabilityTheory.variance_nonneg f μ)
  have hVF:ProbabilityTheory.variance f μ ≤ ∫ x,(f x)^2 ∂μ := by
    rw [ProbabilityTheory.variance_eq_sub hf]
    exact sub_le_self _ (sq_nonneg _)
  have hq:=mul_le_mul_of_nonneg_left hVF (mul_nonneg hH hN)
  have hsq:N*N ≤ (H*(∫ x,(f x)^2 ∂μ))*N := by
    nlinarith [hCS.trans (hp.trans hq)]
  by_cases hzero:N=0
  · change N≤_
    rw [hzero]
    exact mul_nonneg hH (integral_nonneg fun _=>sq_nonneg _)
  · have hpos:0<N := lt_of_le_of_ne hN (Ne.symm hzero)
    exact (mul_le_mul_iff_of_pos_right hpos).mp hsq

theorem rawCubic336_of_tensor_variance (hcap : UniversalLiteralCubicVarianceBound 336) :
    RawCubicWeightedBudget.UniversalRawCubicBound 336 :=
  rawCubicBound_of_tensor_variance (by norm_num) hcap

end KLSConstantImprovement.LiteralCubicVarianceObservationTransfer
#print axioms KLSConstantImprovement.LiteralCubicVarianceObservationTransfer.rawCubicBound_of_tensor_variance
#print axioms KLSConstantImprovement.LiteralCubicVarianceObservationTransfer.rawCubic336_of_tensor_variance
