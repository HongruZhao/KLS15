import KLSConstantImprovement.ActualDeficitBesselBound
import KLSConstantImprovement.ActualCubicVarianceIdentity
import KLSConstantImprovement.LongPrefixCubicBellmanEndpoint

/-! Exact consequences of the joint Bessel constraint. Curvature remains an
explicit open input. The current proved Poincare constant pays the low-fourth
sector, once the literal cubic gradient bound is supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSConstantImprovement.CubicVarianceFourthSector
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualDeficitBesselBound ActualCubicRepresenter
open ActualCubicVarianceIdentity ActualFixedTensorDeficit
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

theorem joint_curvature_middle {J V F S N k : ℝ}
    (hidentity : J+V=21*F+21*S+6*N) (hcurvature : -k*(6*N-F) ≤ J)
    (hk0 : 21≤k) (hk1 : k≤42) (hS0 : S≤F+2*N) (hS1 : S≤(16/3 : ℝ)*N) :
    V≤(188+(8/3 : ℝ)*k)*N := by
  have hc := DeficitCurvatureScalar.curvature_conversion hidentity hcurvature
  by_cases hF : F≤(10/3 : ℝ)*N
  · have hp := mul_le_mul_of_nonneg_left hF (show 0≤42-k by linarith)
    nlinarith
  · have hp := mul_le_mul_of_nonpos_left (le_of_lt (lt_of_not_ge hF))
      (show 21-k≤0 by linarith)
    nlinarith

theorem joint_curvature_large {J V F S N k : ℝ}
    (hidentity : J+V=21*F+21*S+6*N) (hcurvature : -k*(6*N-F) ≤ J)
    (hN : 0≤N) (hk : 42≤k) (hF0 : -2*N≤F)
    (hS0 : S≤F+2*N) (hS1 : S≤(16/3 : ℝ)*N) : V≤(8*k-36)*N := by
  have hc := DeficitCurvatureScalar.curvature_conversion hidentity hcurvature
  by_cases hF : F≤(10/3 : ℝ)*N
  · have hp := mul_le_mul_of_nonpos_left hF0 (show 42-k≤0 by linarith)
    nlinarith
  · have hp := mul_le_mul_of_nonpos_left (le_of_lt (lt_of_not_ge hF))
      (show 21-k≤0 by linarith)
    have hn := mul_nonneg (show 0≤k-42 by linarith) hN
    nlinarith

theorem joint_curvature_46_gives_332 {J V F S N : ℝ}
    (hidentity : J+V=21*F+21*S+6*N) (hcurvature : -46*(6*N-F)≤J)
    (hN : 0≤N) (hF : -2*N≤F) (hS0 : S≤F+2*N) (hS1 : S≤(16/3 : ℝ)*N) :
    V≤332*N := by
  have hb := joint_curvature_large hidentity hcurvature hN (by norm_num) hF hS0 hS1
  norm_num at hb
  exact hb

theorem joint_curvature_93over2_gives_336 {J V F S N : ℝ}
    (hidentity : J+V=21*F+21*S+6*N) (hcurvature : -(93/2 : ℝ)*(6*N-F)≤J)
    (hN : 0≤N) (hF : -2*N≤F) (hS0 : S≤F+2*N) (hS1 : S≤(16/3 : ℝ)*N) :
    V≤336*N := by
  have hb := joint_curvature_large hidentity hcurvature hN (by norm_num) hF hS0 hS1
  norm_num at hb
  exact hb

theorem joint_curvature_48_gives_348 {J V F S N : ℝ}
    (hidentity : J+V=21*F+21*S+6*N) (hcurvature : -48*(6*N-F)≤J)
    (hN : 0≤N) (hF : -2*N≤F) (hS0 : S≤F+2*N) (hS1 : S≤(16/3 : ℝ)*N) :
    V≤348*N := by
  have hb := joint_curvature_large hidentity hcurvature hN (by norm_num) hF hS0 hS1
  norm_num at hb
  exact hb

theorem current_poincare_low_fourth_sector {V F N : ℝ}
    (hN : 0≤N) (hF : F≤N/2)
    (hV : V≤9*LongPrefixCubicBellmanEndpoint.bound*(F+2*N)) : V≤333*N := by
  have hB : 0≤LongPrefixCubicBellmanEndpoint.bound := by
    norm_num [LongPrefixCubicBellmanEndpoint.bound]
  have hp := mul_le_mul_of_nonneg_left hF (show 0≤9*LongPrefixCubicBellmanEndpoint.bound by positivity)
  have hc : (45/2 : ℝ)*LongPrefixCubicBellmanEndpoint.bound≤333 := by
    norm_num [LongPrefixCubicBellmanEndpoint.bound]
  have hn := mul_le_mul_of_nonneg_right hc hN
  nlinarith

theorem curvature_48_high_fourth_sector {J V F S N : ℝ}
    (hidentity : J+V=21*F+21*S+6*N) (hcurvature : -48*(6*N-F)≤J)
    (hF : N/2≤F) (hS : S≤F+2*N) : V≤333*N := by
  have hc := DeficitCurvatureScalar.curvature_conversion hidentity hcurvature
  nlinarith

theorem current_poincare_and_high_sector_curvature_give_333 {J V F S N : ℝ}
    (hidentity : J+V=21*F+21*S+6*N) (hN : 0≤N) (hS : S≤F+2*N)
    (hV : V≤9*LongPrefixCubicBellmanEndpoint.bound*(F+2*N))
    (hcurvature : N/2<F → -48*(6*N-F)≤J) : V≤333*N := by
  by_cases hF : F≤N/2
  · exact current_poincare_low_fourth_sector hN hF hV
  · exact curvature_48_high_fourth_sector hidentity (hcurvature (lt_of_not_ge hF))
      (le_of_lt (lt_of_not_ge hF)) hS

theorem additive_curvature_gives_336 {J V F S N : ℝ}
    (hidentity : J+V=21*F+21*S+6*N) (hcurvature : 0≤J+21*(6*N-F)+92*N)
    (hS : S≤(16/3 : ℝ)*N) : V≤336*N := by
  nlinarith

theorem tensorSquare_nonneg {n : ℕ} (T : Array3 (Fin n)) : 0≤tensorSquare T := by
  unfold tensorSquare square tripleSum
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem tensorPolynomial_variance_le_332_of_curvature46
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j)
    (hcurvature : -46*sliceDeficit μ T≤contractedDeficitHessian μ T) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ≤332*tensorSquare T :=
  joint_curvature_46_gives_332 (variance_add_deficitHessian_eq hμ T hT12 hT23)
    hcurvature (tensorSquare_nonneg T) (fourthContraction_bounds hμ T hT23).1
    (signedTraceSquare_bounds_by_fourth_add_two hμ T).2
    (signedTraceSquare_le_sixteen_thirds hμ T hT12 hT23)

theorem tensorPolynomial_variance_le_336_of_curvature93over2
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j)
    (hcurvature : -(93/2 : ℝ)*sliceDeficit μ T≤contractedDeficitHessian μ T) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ≤336*tensorSquare T :=
  joint_curvature_93over2_gives_336 (variance_add_deficitHessian_eq hμ T hT12 hT23)
    hcurvature (tensorSquare_nonneg T) (fourthContraction_bounds hμ T hT23).1
    (signedTraceSquare_bounds_by_fourth_add_two hμ T).2
    (signedTraceSquare_le_sixteen_thirds hμ T hT12 hT23)

end KLSConstantImprovement.CubicVarianceFourthSector
#print axioms KLSConstantImprovement.CubicVarianceFourthSector.joint_curvature_middle
#print axioms KLSConstantImprovement.CubicVarianceFourthSector.joint_curvature_large
#print axioms KLSConstantImprovement.CubicVarianceFourthSector.joint_curvature_46_gives_332
#print axioms KLSConstantImprovement.CubicVarianceFourthSector.joint_curvature_93over2_gives_336
#print axioms KLSConstantImprovement.CubicVarianceFourthSector.joint_curvature_48_gives_348
#print axioms KLSConstantImprovement.CubicVarianceFourthSector.current_poincare_low_fourth_sector
#print axioms KLSConstantImprovement.CubicVarianceFourthSector.curvature_48_high_fourth_sector
#print axioms KLSConstantImprovement.CubicVarianceFourthSector.current_poincare_and_high_sector_curvature_give_333
#print axioms KLSConstantImprovement.CubicVarianceFourthSector.additive_curvature_gives_336
#print axioms KLSConstantImprovement.CubicVarianceFourthSector.tensorPolynomial_variance_le_332_of_curvature46
#print axioms KLSConstantImprovement.CubicVarianceFourthSector.tensorPolynomial_variance_le_336_of_curvature93over2
