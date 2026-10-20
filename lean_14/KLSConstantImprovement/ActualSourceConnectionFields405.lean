import KLSConstantImprovement.ActualSourceCurvatureDomains405
import KLSConstantImprovement.ActualSourceNaturalGaffney405

/-! Literal aggregate connection fields used in natural-domain testing.
The third-tensor curvature is retained as one nonnegative contraction. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualSourceConnectionFields405
open KLS ActualBoundedCanonicalSource ActualSourceHessianEvolution405 ActualSourceCurvatureDomains405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def sourceThirdAlong (d : SourceData μ) (u : Fin n → Space n → ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ := ∑ i : Fin n, u i x • sourceThirdMatrix d x i

def sourceConnectionGamma (d : SourceData μ) (u : Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    matrixTraceGram (coordinateHessian d.potential x)⁻¹ (sourceThirdMatrix d x) i j * u i x * u j x

def sourceConnectionTarget (d : SourceData μ) (u : Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, sourceTargetCurvature d x i j * u i x * u j x

def sourceConnectionCross (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (Du : Fin n → Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n,
    ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
      (Du i a x * u j x + u i x * Du j a x)

def sourceConnectionBoundary (d : SourceData μ) (χ : Space n → ℝ)
    (u : Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n,
    ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
      (u i x * u j x) * coordinateDerivative χ a x

theorem sourceThirdAlong_trace_square (d : SourceData μ) (u : Fin n → Space n → ℝ) (x : Space n) :
    ((coordinateHessian d.potential x)⁻¹ * sourceThirdAlong d u x *
      (coordinateHessian d.potential x)⁻¹ * sourceThirdAlong d u x).trace = sourceConnectionGamma d u x := by
  simp only [sourceThirdAlong, sourceConnectionGamma, matrixTraceGram,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sourceConnectionGamma_nonnegative_ae (d : SourceData μ) (u : Fin n → Space n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ sourceConnectionGamma d u x := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le] with x hp hN
  have hg := matrixTraceGram_posSemidef hp.1.posSemidef.inv (sourceThirdMatrix d x)
    (fun k => Matrix.IsSymm.ext fun i j => (hN k j i).2)
  have he := hg.dotProduct_mulVec_nonneg (fun i => u i x)
  simpa only [sourceConnectionGamma, dotProduct, Matrix.mulVec, star_trivial,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using he

theorem sourceConnectionCurvature_contraction (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (x : Space n) :
    (∑ i : Fin n, ∑ j : Fin n, sourceConnectionCurvature d x i j * u i x * u j x) =
      sourceConnectionTarget d u x + sourceConnectionGamma d u x := by
  simp only [sourceConnectionCurvature, sourceConnectionTarget, sourceTargetCurvature,
    sourceConnectionGamma, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

end KLSConstantImprovement.ActualSourceConnectionFields405
#print axioms KLSConstantImprovement.ActualSourceConnectionFields405.sourceThirdAlong_trace_square
#print axioms KLSConstantImprovement.ActualSourceConnectionFields405.sourceConnectionGamma_nonnegative_ae
#print axioms KLSConstantImprovement.ActualSourceConnectionFields405.sourceConnectionCurvature_contraction
