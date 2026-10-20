import KLSConstantImprovement.ActualJointMultiplierRowTest405
import KLSConstantImprovement.ActualNaturalMassWeakDerivative405
import KLSConstantImprovement.ActualConnectionContractions405

/-! Literal finite contractions of the SAME compact joint multiplier in
actual row and H-evolution tests. No individual limiting curvature products
are introduced. These equalities precede the nonlinear joint cutoff limit. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualJointBochnerContractions405
open KLS ActualBoundedCanonicalSource ActualIntrinsicJointWeakTests405
open ActualJointMultiplierWeakTests405 ActualJointMultiplierRowTest405
open ActualSourceConnectionFields405 ActualSourceHessianEvolution405
open ActualSourceLocalizedGaffney405 ActualSourceNaturalGaffney405
open ActualSourceNaturalTargetCurvatureDomain405 ActualBoundedRawMetricDomain
open ActualConnectionContractions405 ActualCanonicalConnectionAlgebra405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def jointEffectiveDerivative (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (Du : Fin n → Fin n → Space n → ℝ) (η : (JointIndex n → ℝ) → ℝ)
    (ψ : Space n → ℝ) (a : Fin n) (x : Space n) : ℝ :=
  jointSource d u η x * coordinateDerivative ψ a x + ψ x * jointSourceDerivative d u Du η a x

def rowMassFlux (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    (a : Fin n) (x : Space n) : ℝ := ∑ j : Fin n, Du a j x * u j x

theorem joint_row_test_contraction (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    {η : (JointIndex n → ℝ) → ℝ} (hη : ContDiff ℝ 1 η)
    (ψ : Space n → ℝ) (x : Space n) :
    (∑ j : Fin n, ∑ a : Fin n, Du a j x *
      rawCutoffDerivative ψ (jointSource d u (jointRow η j))
        (jointSourceDerivative d u Du (jointRow η j)) a x) =
      ψ x * jointSource d u η x * sourceVectorJacobianEnergy Du x +
        ∑ a : Fin n, rowMassFlux u Du a x * jointEffectiveDerivative d u Du η ψ a x := by
  have hpoint (j a : Fin n) : Du a j x *
      rawCutoffDerivative ψ (jointSource d u (jointRow η j))
        (jointSourceDerivative d u Du (jointRow η j)) a x =
        (ψ x * jointSource d u η x) * (Du j a x * Du a j x) +
          (Du a j x * u j x) * jointEffectiveDerivative d u Du η ψ a x := by
    dsimp only [rawCutoffDerivative, jointSourceDerivative, jointSource]
    rw [jointRow_differential hη]
    dsimp only [jointRow, sourceJointValue, sourceJointDerivative, Sum.elim_inl]
    change _ = _
    dsimp only [jointSource, jointSourceDerivative, jointEffectiveDerivative,
      sourceJointValue, sourceJointDerivative, Sum.elim_inl]
    ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  congr 1
  · simp only [sourceVectorJacobianEnergy, Finset.mul_sum]
  · rw [Finset.sum_comm]
    simp only [rowMassFlux, Finset.sum_mul]

theorem joint_matrix_test_contraction (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    {η : (JointIndex n → ℝ) → ℝ} (hη : ContDiff ℝ 1 η)
    (ψ : Space n → ℝ) (x : Space n) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n,
      ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
        rawCutoffDerivative ψ (jointSource d u (jointMatrix η i j))
          (jointSourceDerivative d u Du (jointMatrix η i j)) a x) =
      ψ x * jointSource d u η x * sourceConnectionCross d u Du x +
        (fun a => jointEffectiveDerivative d u Du η ψ a x) ⬝ᵥ
          ((coordinateHessian d.potential x)⁻¹ *ᵥ (sourceThirdAlong d u x *ᵥ (fun i => u i x))) := by
  have hpoint (i j a : Fin n) :
      ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
        rawCutoffDerivative ψ (jointSource d u (jointMatrix η i j))
          (jointSourceDerivative d u Du (jointMatrix η i j)) a x =
      (ψ x * jointSource d u η x) *
        (((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
          (Du i a x * u j x + u i x * Du j a x)) +
        (((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
          (u i x * u j x)) * jointEffectiveDerivative d u Du η ψ a x := by
    dsimp only [rawCutoffDerivative, jointSourceDerivative, jointSource]
    rw [jointMatrix_differential hη]
    dsimp only [jointMatrix, sourceJointValue, sourceJointDerivative, Sum.elim_inl]
    dsimp only [jointSource, jointSourceDerivative, jointEffectiveDerivative,
      sourceJointValue, sourceJointDerivative, Sum.elim_inl]
    ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  congr 1
  · simp only [sourceConnectionCross, Finset.mul_sum]
  · have he := connection_boundary_contraction (coordinateHessian d.potential x)⁻¹
      (sourceThirdMatrix d x) (fun i => u i x) (fun a => jointEffectiveDerivative d u Du η ψ a x)
    simpa only [sourceThirdAlong, thirdAlong] using he

theorem joint_matrix_rhs_contraction (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (η : (JointIndex n → ℝ) → ℝ)
    (ψ : Space n → ℝ) (x : Space n) :
    (∑ i : Fin n, ∑ j : Fin n, (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
      (ψ x * jointSource d u (jointMatrix η i j) x)) =
      ψ x * jointSource d u η x * (-sourceVectorMass d.potential u x +
        sourceConnectionTarget d u x + sourceConnectionGamma d u x) := by
  calc
    _ = ψ x * jointSource d u η x * (-sourceVectorMass d.potential u x +
        (∑ i : Fin n, ∑ j : Fin n, sourceConnectionCurvature d x i j * u i x * u j x)) := by
      have hpoint (i j : Fin n) :
          (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
            (ψ x * jointSource d u (jointMatrix η i j) x) =
          (ψ x * jointSource d u η x) *
            (-(coordinateHessian d.potential x i j * u i x * u j x) +
              sourceConnectionCurvature d x i j * u i x * u j x) := by
        dsimp only [jointSource, jointMatrix, sourceJointValue, Sum.elim_inl]
        ring
      simp_rw [hpoint]
      simp only [sourceVectorMass, mul_add, mul_neg, Finset.mul_sum,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = _ := by rw [sourceConnectionCurvature_contraction]; ring

theorem joint_row_rhs_contraction_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (Dg : Fin n → Space n → ℝ)
    (η : (JointIndex n → ℝ) → ℝ) (ψ : Space n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (∑ j : Fin n, (Dg j x - naturalCanonicalRawGradient d g j x) *
        (ψ x * jointSource d (naturalCanonicalFlux d g) (jointRow η j) x)) =
      ψ x * jointSource d (naturalCanonicalFlux d g) η x *
        ((∑ j : Fin n, Dg j x * naturalCanonicalFlux d g j x) -
          sourceVectorMass d.potential (naturalCanonicalFlux d g) x) := by
  let u := naturalCanonicalFlux d g
  let p := naturalCanonicalRawGradient d g
  filter_upwards [hessian_mul_naturalCanonicalFlux_ae d g] with x hx
  have hm : (∑ j : Fin n, p j x * u j x) = sourceVectorMass d.potential u x := by
    have hp (j : Fin n) : p j x = (coordinateHessian d.potential x *ᵥ (fun i => u i x)) j :=
      (congrFun hx j).symm
    simp_rw [hp]
    simp only [sourceVectorMass, Matrix.mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  calc
    _ = ψ x * jointSource d u η x *
        ((∑ j : Fin n, Dg j x * u j x) - ∑ j : Fin n, p j x * u j x) := by
      simp only [jointSource, jointRow, sourceJointValue, Sum.elim_inl,
        mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    _ = _ := by rw [hm]

end KLSConstantImprovement.ActualJointBochnerContractions405
#print axioms KLSConstantImprovement.ActualJointBochnerContractions405.joint_row_test_contraction
#print axioms KLSConstantImprovement.ActualJointBochnerContractions405.joint_matrix_test_contraction
#print axioms KLSConstantImprovement.ActualJointBochnerContractions405.joint_matrix_rhs_contraction
#print axioms KLSConstantImprovement.ActualJointBochnerContractions405.joint_row_rhs_contraction_ae
