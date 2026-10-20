import KLSConstantImprovement.ActualDeficitContraction

/-! Identification of the actual fixed-tensor tilt deficit at isotropy. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualDeficitZero
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open ActualFixedTensorDeficit ActualDeficitTensorBounds ActualDeficitContraction
open KLSBelow25.CubicSymmetricNoise
variable {n : ℕ}
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem fixedTensorDeficit_zero {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (B C : Matrix (Fin n) (Fin n) ℝ) :
    fixedTensorDeficit μ B C 0=6*(∑ a,∑ b,B a b*C a b)-
      ∑ a,∑ b,∑ c,∑ d,B a b*C c d*actualFourthCumulantArray μ a b c d := by
  unfold fixedTensorDeficit
  simp_rw [covarianceJet_zero hμ,cumulantJet_four_zero hμ]
  simp only [mul_sub,Finset.sum_sub_distrib]
  congr 1
  simp [mul_ite,ite_mul,Finset.mul_sum,mul_assoc]
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro b _
  ring

theorem diagonal_fixedTensorDeficit_eq_sliceDeficit
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT23 : ∀ i j k,T i j k=T i k j) :
    (∑ i,fixedTensorDeficit μ (T i) (T i) 0)=sliceDeficit μ T := by
  simp_rw [fixedTensorDeficit_zero hμ]
  unfold sliceDeficit
  rw [fourthContraction_expanded hμ T hT23]
  simp only [Finset.sum_sub_distrib]
  congr 1
  unfold tensorSquare square tripleSum
  simp only [Finset.mul_sum,pow_two]

end KLSConstantImprovement.ActualDeficitZero
#print axioms KLSConstantImprovement.ActualDeficitZero.fixedTensorDeficit_zero
#print axioms KLSConstantImprovement.ActualDeficitZero.diagonal_fixedTensorDeficit_eq_sliceDeficit
