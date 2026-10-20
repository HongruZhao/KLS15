import KLSConstantImprovement.ActualQuarticHessianTest405

/-! Literal weak derivative of the quartic matrix-gradient test. This is
the derivative constructed by the proved raw Sobolev algebra; no fderiv
of the actual source Hessian is substituted for it. -/
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators
namespace KLSConstantImprovement.ActualQuarticRawDerivative405
open KLS ActualBoundedCanonicalSource ActualCompactRawMetricGraph
open ActualBoundedRawTestAlgebra405 ActualSourceTensorGramMetricBinding
open ActualQuarticHessianTest405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem quarticEntryTest_derivative (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (a b r : Fin n) (x : Space n) :
    (quarticEntryTest d T a b).derivative r x =
      2 * (∑ i, ∑ j, ∑ q, ∑ p, (T i a p * T j q b) *
        (sourceTensorGramRawDerivative d.potential d.third T i j r x *
          coordinateHessian d.potential x p q +
        sourceTensorGramEntry d.potential T i j x * d.third x r p q)) := by
  dsimp only [quarticEntryTest, BoundedRawTest.mul, BoundedRawTest.const,
    rawTestSum, tensorGramTest, BoundedRawTest.hessian]
  simp only [zero_mul, zero_add]

end KLSConstantImprovement.ActualQuarticRawDerivative405
#print axioms KLSConstantImprovement.ActualQuarticRawDerivative405.quarticEntryTest_derivative
