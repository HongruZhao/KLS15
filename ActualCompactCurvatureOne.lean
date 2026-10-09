import CompactPotentialDivergenceOneForm
import TensorExteriorJointHodgeDomain
import TensorExteriorOperatorChain

/-! Literal compact curvature inequality at tensor rank one. The residual
bound is derived from the true closed Hilbert complex and the actual full
weak Hodge graph; the Bochner split then cancels the physical curvature.
No residual, domain, projection, or curvature gate is a premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open MeasureTheory InnerProductSpace Set Matrix Filter LinearPMap
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
open KLS.DeterministicBridgeNext
variable {n : ℕ} {φ ψ : Space n → ℝ}

 theorem compactPotentialAdjointOneFormL2_zero_residual_bound
     (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
     {a : ℝ} (ha : 0 ≤ a)
     (hlower : ∀ x (v : Fin n → ℝ),
       a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
     ‖compactPotentialOneFormAdjointDivergenceLp (hφ.of_le (by simp)) hψ hc 1 -
       tensorCompactProjection (hφ.of_le (by simp)) 1
         (compactPotentialOneFormAdjointDivergenceLp (hφ.of_le (by simp)) hψ hc 1)‖^2 ≤
       compactPotentialCurvatureEnergy φ ψ 1 - a*‖compactPotentialTensorLp hφ.continuous hψ hc 2‖^2 := by
   letI : CompleteSpace (TensorThreeFormL2 φ 0) :=
     (isClosed_univ : IsClosed (Set.univ : Set (CenteredL2.Family (potentialMeasure φ)
       (TensorThreeFormIndex n 0)))).completeSpace_coe
   let A := tensorExteriorOneOperator (hφ.of_le (by simp)) 0
   let B := tensorExteriorTwoOperator (hφ.of_le (by simp)) 0
   let Y := compactPotentialAdjointOneFormL2 (hφ.of_le (by simp)) hψ hc 0
   let u : A.domain := ⟨Y, compactPotentialAdjointOneFormL2_mem_domain hφ hψ hc 0⟩
   have hbound : ∀ w : A.adjoint.domain, ∀ hwB : (w : TensorTwoFormL2 φ 0) ∈ B.domain,
       2*inner ℝ (A u) (w : TensorTwoFormL2 φ 0)-‖A.adjoint w‖^2-
         ‖B ⟨(w : TensorTwoFormL2 φ 0),hwB⟩‖^2 ≤
       compactPotentialCurvatureEnergy φ ψ 1 - a*‖compactPotentialTensorLp hφ.continuous hψ hc 2‖^2 := by
     intro w hwB
     have ht := compactPotentialZero_curvature_test_bound (hφ.of_le (by simp)) hψ hc
       (tensorExterior_joint_hasWeakConstrainedHodge hφ 0 w hwB)
       (fun z => Lp.memLp ((w : TensorTwoFormL2 φ 0).val z))
       (tensorHodgeJointOutput_memLp hφ 0 w hwB) ha hlower
     rw [finiteMatrixLp_coe_eq, tensorHodgeJointOutput_norm_sq] at ht
     have hi : inner ℝ (A u) (w : TensorTwoFormL2 φ 0) =
         inner ℝ (compactPotentialCurvatureCurlZeroLp (hφ.of_le (by simp)) hψ hc)
           (w : TensorTwoFormL2 φ 0).val := by
       change inner ℝ (tensorExteriorOneOperator (hφ.of_le (by simp)) 0
         ⟨compactPotentialAdjointOneFormL2 (hφ.of_le (by simp)) hψ hc 0,
           compactPotentialAdjointOneFormL2_mem_domain hφ hψ hc 0⟩) _ = _
       rw [compactPotentialAdjointOneFormL2_zero_apply hφ hψ hc]
       rfl
     rw [hi]
     dsimp only [A,B] at *
     linarith
   have hb := hilbert_complex_residual_bound_of_differential_test_bound A B
     (tensorExteriorOneOperator_isClosed _ 0) (tensorExteriorOneOperator_domain_dense _ 0)
     (tensorExteriorTwoOperator_isClosed _ 0) (tensorExteriorOperators_chain _ 0) u hbound
   change ‖Y-closedPartialKernelProjection A (tensorExteriorOneOperator_isClosed _ 0) Y‖^2 ≤ _ at hb
   rw [compactPotentialAdjointOneFormL2_residual_norm] at hb
   exact hb

 variable [IsProbabilityMeasure (potentialMeasure φ)]

 /-- The genuine compact tensor-rank-one instance of equation 5.2. -/
 theorem compactPotentialDivergenceHilbert_rank_one_curvature
     (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
     {a : ℝ} (ha : 0 ≤ a)
     (hlower : ∀ x (v : Fin n → ℝ),
       a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
     ‖compactPotentialTensorLp hφ.continuous hψ hc 3‖^2+
       a*‖compactPotentialTensorLp hφ.continuous hψ hc 2‖^2 ≤
       ‖compactPotentialDivergenceHilbert hφ hψ hc 1‖^2 := by
   have hb := compactPotentialDivergenceHilbert_bochner_split hφ hψ hc 1
   have hr := compactPotentialAdjointOneFormL2_zero_residual_bound hφ hψ hc ha hlower
   change ‖tensorAdjointDivergenceLp (hφ.of_le (by simp))
       (fun I => (coordinatePotentialTensor_contDiff hψ 2 I).of_le (by simp))
       (coordinatePotentialTensor_hasCompactSupport hc 2) -
       compactPotentialProjectedDivergence (hφ.of_le (by simp)) hψ hc 1‖^2 ≤ _ at hr
   linarith

end KLS.DeterministicBridgeIntegration
end
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialAdjointOneFormL2_zero_residual_bound
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialDivergenceHilbert_rank_one_curvature
