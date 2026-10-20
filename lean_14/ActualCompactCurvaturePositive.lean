import CompactPotentialExteriorGraph
import CompactPotentialDivergenceOneForm
import TensorExteriorJointHodgeDomain
import TensorExteriorOperatorChain

/-! Closing the actual compact curvature estimate in every positive
auxiliary degree, using the genuine closed Hilbert complex. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators RealInnerProductSpace LinearPMap
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
variable {n r : ℕ} {φ ψ : Space n → ℝ}

lemma compactPotentialAdjointOneForm_pointwise_symmetric
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : Space n) :
    WithLp.toLp 2 (fun a => compactPotentialAdjointOneForm φ ψ r a x)
      ∈ tensorOneFormSymmetricFiber n (r+1) := by
  apply (mem_tensorOneFormSymmetricFiber_iff _).mpr
  intro a b hp
  exact congrFun (tensorAdjointDivergence_symmetric
    (coordinatePotentialTensor_symmetric hψ (r+3)) _ _ hp) x

theorem compactPotentialPositive_curvature_residual_bound
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (r : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hlower : ∀ (x : Space n) (v : Fin n → ℝ),
      a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
    ‖compactPotentialOneFormAdjointDivergenceLp (hφ.of_le (by simp)) hψ hc (r+2)-
      compactPotentialProjectedDivergence (hφ.of_le (by simp)) hψ hc (r+2)‖^2 ≤
      compactPotentialCurvatureEnergy φ ψ (r+2)-
        a*‖compactPotentialTensorLp hφ.continuous hψ hc (r+3)‖^2 := by
  letI : CompleteSpace (TensorThreeFormL2 φ (r+1)) :=
    (isClosed_univ : IsClosed (Set.univ : Set (CenteredL2.Family
      (potentialMeasure φ) (TensorThreeFormIndex n (r+1))))).completeSpace_coe
  let A := tensorExteriorOneOperator (hφ.of_le (by simp)) (r+1)
  let B := tensorExteriorTwoOperator (hφ.of_le (by simp)) (r+1)
  obtain ⟨hy,hz,hgraph⟩ := compactPotentialAdjointOneForm_graph
    (hφ.of_le (by simp)) hψ hc (fun x => compactPotentialAdjointOneForm_pointwise_symmetric hψ x)
  have hgraph' : (compactPotentialAdjointOneFormL2 (hφ.of_le (by simp)) hψ hc (r+1),
      (⟨compactPotentialCurvatureCurlLp (hφ.of_le (by simp)) hψ hc r,hz⟩ : TensorTwoFormL2 φ (r+1)))
      ∈ A.graph := by
    exact hgraph
  obtain ⟨u,hu,hAu⟩ := A.mem_graph_iff.mp hgraph'
  have hb := hilbert_complex_residual_bound_of_differential_test_bound A B
    (tensorExteriorOneOperator_isClosed _ _) (tensorExteriorOneOperator_domain_dense _ _)
    (tensorExteriorTwoOperator_isClosed _ _) (tensorExteriorOperators_chain _ _) u
    (M := compactPotentialCurvatureEnergy φ ψ (r+2)-
      a*‖compactPotentialTensorLp hφ.continuous hψ hc (r+3)‖^2) ?_
  · rw [hu] at hb
    rw [compactPotentialAdjointOneFormL2_residual_norm] at hb
    exact hb
  · intro w hwB
    have ht := compactPotential_curvature_test_bound (hφ.of_le (by simp)) hψ hc
      (tensorExterior_joint_hasWeakConstrainedHodge hφ (r+1) w hwB)
      (fun z => Lp.memLp ((w : TensorTwoFormL2 φ (r+1)).val z))
      (tensorHodgeJointOutput_memLp hφ (r+1) w hwB) ha hlower
    rw [finiteMatrixLp_coe_eq,tensorHodgeJointOutput_norm_sq] at ht
    rw [hAu]
    change 2*inner ℝ (compactPotentialCurvatureCurlLp (hφ.of_le (by simp)) hψ hc r)
      (w : TensorTwoFormL2 φ (r+1)).val-‖A.adjoint w‖^2-
      ‖B ⟨(w : TensorTwoFormL2 φ (r+1)),hwB⟩‖^2 ≤ _
    linarith

variable [IsProbabilityMeasure (potentialMeasure φ)]

theorem compactPotentialDivergenceHilbert_positive_curvature
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (r : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hlower : ∀ (x : Space n) (v : Fin n → ℝ),
      a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
    ‖compactPotentialTensorLp hφ.continuous hψ hc (r+4)‖^2+
      a*‖compactPotentialTensorLp hφ.continuous hψ hc (r+3)‖^2 ≤
      ‖compactPotentialDivergenceHilbert hφ hψ hc (r+2)‖^2 := by
  rw [compactPotentialDivergenceHilbert_bochner_split]
  have hb := compactPotentialPositive_curvature_residual_bound hφ hψ hc r ha hlower
  change ‖compactPotentialTensorLp hφ.continuous hψ hc (r+4)‖^2+
    a*‖compactPotentialTensorLp hφ.continuous hψ hc (r+3)‖^2 ≤
    ‖compactPotentialTensorLp hφ.continuous hψ hc (r+4)‖^2+
      compactPotentialCurvatureEnergy φ ψ (r+2)-
      ‖compactPotentialOneFormAdjointDivergenceLp (hφ.of_le (by simp)) hψ hc (r+2)-
        compactPotentialProjectedDivergence (hφ.of_le (by simp)) hψ hc (r+2)‖^2
  linarith [hb]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialPositive_curvature_residual_bound
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialDivergenceHilbert_positive_curvature
