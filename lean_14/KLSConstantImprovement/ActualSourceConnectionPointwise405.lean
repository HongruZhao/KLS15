import KLSConstantImprovement.ActualSourceConnectionFields405
import KLSConstantImprovement.ActualConnectionContractions405
import KLSConstantImprovement.ActualCompatibleConnectionYoung405
import KLSConstantImprovement.ActualCompatibleConnectionBoundary405
import KLSConstantImprovement.ActualCompatibleJacobianCoercivity405

/-! Actual compatible connection absorption, with the full natural mass
factor in the boundary term. No integrability or vanishing is asserted
by these pointwise estimates. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff NNReal ENNReal MatrixOrder
namespace KLSConstantImprovement.ActualSourceConnectionPointwise405
open KLS ActualBoundedCanonicalSource ActualSourceHessianEvolution405 ActualSourceCurvatureDomains405
open ActualSourceConnectionFields405 ActualSourceLocalizedGaffney405
open ActualConnectionContractions405 ActualCompatibleConnectionYoung405
open ActualCompatibleConnectionBoundary405 ActualCompatibleJacobianCoercivity405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem sourceThirdAlong_isSymm_ae (d : SourceData μ) (u : Fin n → Space n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential, (sourceThirdAlong d u x).IsSymm := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.third_symmetric_ae.filter_mono hac.ae_le] with x hx
  apply Matrix.IsSymm.ext
  intro i j
  simp only [sourceThirdAlong, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => congrArg (fun t : ℝ => u k x * t) (hx k j i).2

theorem sourceConnectionCross_eq_trace_ae (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (Du : Fin n → Fin n → Space n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential, sourceConnectionCross d u Du x =
      2 * (Matrix.of (fun i j => Du i j x) * (coordinateHessian d.potential x)⁻¹ * sourceThirdAlong d u x).trace := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.third_symmetric_ae.filter_mono hac.ae_le] with x hx
  exact connection_cross_contraction (coordinateHessian d.potential x)⁻¹
    (Matrix.of (fun i j => Du i j x)) (sourceThirdMatrix d x) hx (fun i => u i x)

theorem sourceConnectionCross_abs_le_ae (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hc : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x)).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential, |sourceConnectionCross d u Du x| ≤
      (1/4 : ℝ) * sourceConnectionGamma d u x + 4 * sourceVectorJacobianEnergy Du x := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, sourceThirdAlong_isSymm_ae d u,
    sourceConnectionCross_eq_trace_ae d u Du, hc.filter_mono hac.ae_le] with x hp hN hX hD
  rw [hX]
  have he := compatible_connection_young (coordinateHessian d.potential x)
    (Matrix.of (fun i j => Du i j x)) (sourceThirdAlong d u x) hp.1 hD hN
  rw [sourceThirdAlong_trace_square] at he
  simpa only [sourceVectorJacobianEnergy, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.of_apply] using he

theorem sourceConnectionBoundary_square_le_ae (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (χ : Space n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential, sourceConnectionBoundary d χ u x ^ 2 ≤
      inverseHessianGradientForm d.potential χ x * sourceVectorMass d.potential u x *
        sourceConnectionGamma d u x := by
  filter_upwards [d.hessian_ae_source, sourceThirdAlong_isSymm_ae d u] with x hp hN
  have he := compatible_connection_boundary_square (coordinateHessian d.potential x)
    (sourceThirdAlong d u x) hp.1 hN (fun a => coordinateDerivative χ a x) (fun i => u i x)
  have hb := connection_boundary_contraction (coordinateHessian d.potential x)⁻¹
    (sourceThirdMatrix d x) (fun i => u i x) (fun a => coordinateDerivative χ a x)
  change sourceConnectionBoundary d χ u x =
    (fun a => coordinateDerivative χ a x) ⬝ᵥ ((coordinateHessian d.potential x)⁻¹ *ᵥ
      (sourceThirdAlong d u x *ᵥ (fun i => u i x))) at hb
  rw [← hb, sourceThirdAlong_trace_square] at he
  rw [← matrix_quadratic_sum_eq_dotProduct (coordinateHessian d.potential x)⁻¹
    (fun a => coordinateDerivative χ a x),
    ← matrix_quadratic_sum_eq_dotProduct (coordinateHessian d.potential x) (fun i => u i x)] at he
  exact he

theorem sourceConnectionTarget_nonnegative_ae (d : SourceData μ) (u : Fin n → Space n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ sourceConnectionTarget d u x := by
  filter_upwards [d.hessian_ae_source] with x hp
  have hV := coordinateHessian_posSemidef_of_convex
    (d.target_smooth.of_le (by simp)) d.target_convex_potential (gradient d.potential x)
  have hP : (sourceTargetCurvature d x).PosSemidef := by
    simpa only [sourceTargetCurvature, hp.1.isHermitian.eq] using
      hV.conjTranspose_mul_mul_same (coordinateHessian d.potential x)
  have he := hP.dotProduct_mulVec_nonneg (fun i => u i x)
  simp only [Pi.star_apply, star_trivial] at he
  rwa [← matrix_quadratic_sum_eq_dotProduct] at he

/-- Scalar Young absorption retains the boundary mass factor exactly. -/
theorem boundary_young_of_square {b e m q c : ℝ}
    (he : 0 ≤ e) (hm : 0 ≤ m) (hq : 0 ≤ q) (hb : b ^ 2 ≤ e * m * q) :
    |2 * (c * b)| ≤ (1/4 : ℝ) * c ^ 2 * q + 4 * (m * e) := by
  let A : ℝ := (1/4 : ℝ) * c ^ 2 * q
  let B : ℝ := 4 * (m * e)
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg c)) hq
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (mul_nonneg hm he)
  have hs : |2 * (c * b)| ^ 2 ≤ 4 * A * B := by
    calc
      _ = 4 * c ^ 2 * b ^ 2 := by rw [sq_abs]; ring
      _ ≤ 4 * c ^ 2 * (e * m * q) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by dsimp only [A, B]; ring
  change |2 * (c * b)| ≤ A + B
  nlinarith [sq_nonneg (A - B), abs_nonneg (2 * (c * b))]

theorem sourceConnectionBoundary_abs_le_ae (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (χ : Space n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential, |2 * (χ x * sourceConnectionBoundary d χ u x)| ≤
      (1/4 : ℝ) * χ x ^ 2 * sourceConnectionGamma d u x +
        4 * (sourceVectorMass d.potential u x * inverseHessianGradientForm d.potential χ x) := by
  filter_upwards [d.hessian_ae_source, sourceConnectionGamma_nonnegative_ae d u,
    sourceConnectionBoundary_square_le_ae d u χ] with x hp hG hb
  have hm : 0 ≤ sourceVectorMass d.potential u x := by
    rw [sourceVectorMass, matrix_quadratic_sum_eq_dotProduct]
    exact hp.1.posSemidef.dotProduct_mulVec_nonneg _
  exact boundary_young_of_square (inverseHessianGradientForm_nonneg_at χ hp.1) hm hG hb

end KLSConstantImprovement.ActualSourceConnectionPointwise405
#print axioms KLSConstantImprovement.ActualSourceConnectionPointwise405.sourceThirdAlong_isSymm_ae
#print axioms KLSConstantImprovement.ActualSourceConnectionPointwise405.sourceConnectionCross_eq_trace_ae
#print axioms KLSConstantImprovement.ActualSourceConnectionPointwise405.sourceConnectionCross_abs_le_ae
#print axioms KLSConstantImprovement.ActualSourceConnectionPointwise405.sourceConnectionBoundary_square_le_ae
#print axioms KLSConstantImprovement.ActualSourceConnectionPointwise405.sourceConnectionTarget_nonnegative_ae
#print axioms KLSConstantImprovement.ActualSourceConnectionPointwise405.boundary_young_of_square
#print axioms KLSConstantImprovement.ActualSourceConnectionPointwise405.sourceConnectionBoundary_abs_le_ae
