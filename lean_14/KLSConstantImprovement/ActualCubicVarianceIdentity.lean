import KLSConstantImprovement.ActualCubicMomentJet
import KLSConstantImprovement.CubicCumulantContraction
import KLSConstantImprovement.DeficitCurvatureScalar

/-! Actual cubic variance and fixed-tensor deficit identities on the
entire original admissible-law class. The curvature estimate is explicit
only in the final consequence; neither cumulant identity is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualCubicVarianceIdentity
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open ActualCubicRepresenter ActualCubicMomentJet ActualFixedTensorDeficit
open ActualDeficitTensorBounds ActualDeficitContraction
open KLSBelow25.CubicSymmetricNoise
variable {n : ℕ}
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

theorem cubicGramKernel_eq_momentKernel (μ : Measure (Space n)) (i j k a b c : Fin n) :
    cubicGramKernel μ i j k a b c=CubicCumulantContraction.momentKernel μ i j k a b c := by
  unfold cubicGramKernel rawProductKernel tripleMeanKernel CubicCumulantContraction.momentKernel
  unfold ActualCubicRepresenter.δ CubicCumulantContraction.δ
  ring

theorem integral_six_sum {μ : Measure (Space n)}
    (f : Fin n→Fin n→Fin n→Fin n→Fin n→Fin n→Space n→ℝ)
    (hi : ∀ i j k a b c,Integrable (f i j k a b c) μ) :
    (∫ x,∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,f i j k a b c x ∂μ)=
      ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,∫ x,f i j k a b c x ∂μ := by
  rw [integral_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ fun j _=>integrable_finsetSum Finset.univ fun k _=>integrable_finsetSum Finset.univ fun a _=>integrable_finsetSum Finset.univ fun b _=>integrable_finsetSum Finset.univ fun c _=>hi i j k a b c)]
  apply Finset.sum_congr rfl;intro i _
  rw [integral_finsetSum Finset.univ (fun j _=>integrable_finsetSum Finset.univ fun k _=>integrable_finsetSum Finset.univ fun a _=>integrable_finsetSum Finset.univ fun b _=>integrable_finsetSum Finset.univ fun c _=>hi i j k a b c)]
  apply Finset.sum_congr rfl;intro j _
  rw [integral_finsetSum Finset.univ (fun k _=>integrable_finsetSum Finset.univ fun a _=>integrable_finsetSum Finset.univ fun b _=>integrable_finsetSum Finset.univ fun c _=>hi i j k a b c)]
  apply Finset.sum_congr rfl;intro k _
  rw [integral_finsetSum Finset.univ (fun a _=>integrable_finsetSum Finset.univ fun b _=>integrable_finsetSum Finset.univ fun c _=>hi i j k a b c)]
  apply Finset.sum_congr rfl;intro a _
  rw [integral_finsetSum Finset.univ (fun b _=>integrable_finsetSum Finset.univ fun c _=>hi i j k a b c)]
  apply Finset.sum_congr rfl;intro b _
  rw [integral_finsetSum Finset.univ (fun c _=>hi i j k a b c)]

theorem tensorPolynomial_gram {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ=
      CubicCumulantContraction.contract T (CubicCumulantContraction.momentKernel μ) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  rw [ProbabilityTheory.variance_eq_sub (tensorPolynomial_memLp hμ T),tensorPolynomial_centered hμ T]
  simp only [zero_pow (by decide : 2≠0),sub_zero,Pi.pow_apply,pow_two,Pi.mul_apply]
  have hi (i j k a b c : Fin n) :
      Integrable (fun x=>T i j k*coordinateCubic μ i j k x*(T a b c*coordinateCubic μ a b c x)) μ := by
    have hh:=((coordinateCubic_memLp hμ i j k).integrable_mul
      (coordinateCubic_memLp hμ a b c)).const_mul (T i j k*T a b c)
    convert hh using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  unfold tensorPolynomial
  simp only [Finset.sum_mul,Finset.mul_sum]
  have heSum:(fun x=>∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,
      T a b c*coordinateCubic μ a b c x*(T i j k*coordinateCubic μ i j k x))=
      fun x=>∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,
      T i j k*coordinateCubic μ i j k x*(T a b c*coordinateCubic μ a b c x) := by
    funext x
    apply Finset.sum_congr rfl;intro i _
    apply Finset.sum_congr rfl;intro j _
    apply Finset.sum_congr rfl;intro k _
    apply Finset.sum_congr rfl;intro a _
    apply Finset.sum_congr rfl;intro b _
    apply Finset.sum_congr rfl;intro c _
    ring
  rw [heSum,integral_six_sum _ hi]
  unfold CubicCumulantContraction.contract
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro k _
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro b _
  apply Finset.sum_congr rfl;intro c _
  have he:(fun x=>T i j k*coordinateCubic μ i j k x*(T a b c*coordinateCubic μ a b c x))=
      fun x=>(T i j k*T a b c)*(coordinateCubic μ i j k x*coordinateCubic μ a b c x) := by
    funext x;ring
  rw [he,integral_const_mul,coordinateCubic_pairing hμ (coordinateCubic_memLp hμ a b c),
    coordinate_cubic_coefficient hμ,cubicGramKernel_eq_momentKernel]

theorem tensorPolynomial_variance_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ=sixthContraction μ T+
      9*fourthContraction μ T+9*signedTraceSquare μ T+6*tensorSquare T := by
  rw [tensorPolynomial_gram hμ T]
  exact CubicCumulantContraction.momentKernel_contract_eq hμ T hT12 hT23

theorem variance_add_deficitHessian_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) :
    contractedDeficitHessian μ T+ProbabilityTheory.variance (tensorPolynomial μ T) μ=
      21*fourthContraction μ T+21*signedTraceSquare μ T+6*tensorSquare T :=
  DeficitCurvatureScalar.deficit_variance_identity
    (contractedDeficitHessian_eq hμ T hT12 hT23) (tensorPolynomial_variance_eq hμ T hT12 hT23)

theorem tensorPolynomial_variance_le_336_of_curvature
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j)
    (hcurvature : -(65/2 : ℝ)*sliceDeficit μ T ≤ contractedDeficitHessian μ T) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ ≤ 336*tensorSquare T := by
  exact DeficitCurvatureScalar.curvature_65over2_gives_cubic336
    (variance_add_deficitHessian_eq hμ T hT12 hT23) hcurvature
    (fourthContraction_bounds hμ T hT23).1 (signedTraceSquare_le_sixteen_thirds hμ T hT12 hT23)

end KLSConstantImprovement.ActualCubicVarianceIdentity
#print axioms KLSConstantImprovement.ActualCubicVarianceIdentity.tensorPolynomial_gram
#print axioms KLSConstantImprovement.ActualCubicVarianceIdentity.tensorPolynomial_variance_eq
#print axioms KLSConstantImprovement.ActualCubicVarianceIdentity.variance_add_deficitHessian_eq
#print axioms KLSConstantImprovement.ActualCubicVarianceIdentity.tensorPolynomial_variance_le_336_of_curvature
