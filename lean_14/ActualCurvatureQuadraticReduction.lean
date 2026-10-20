import TensorGradientCompactCore
import ActualGradedTensorOperators
import BoundedInverseQuadraticDuality

/-! Genuine quadratic-duality passage from compact potential curvature
and projected-divergence density to the actual rational block comparison.
Both analytic gates are explicit; neither is inferred from ordinary tensor
density or assumed as a paper theorem. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace Set
open scoped ContDiff BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25 KLSBelow25.GradedHilbert
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {n r : ℕ} {φ : Space n → ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]

theorem orderedTensorMeanPart_inner_centered (hφ : ContDiff ℝ 1 φ)
    (F : OrderedTensorField φ r) (v : CenteredCompatibleTensorHilbert hφ r) :
    inner ℝ (v : OrderedTensorField φ r) (orderedTensorMeanPart φ r F)=0 := by
  have hm := (mem_centeredCompatibleTensorSubspace_iff hφ
    (v : OrderedTensorField φ r)).mp v.property
  rw [real_inner_comm,PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro I hI
  rw [orderedTensorMeanPart_apply,inner_smul_left,CenteredL2.inner_oneLp,hm.2 I]
  simp

variable {κ : ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

def compactPotentialDivergenceHilbert {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℕ) :
    CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r :=
  compactCenteredProjectedDivergence hφ
    (fun I => (coordinatePotentialTensor_contDiff hψ (r+1) I).of_le (by simp))
    (coordinatePotentialTensor_hasCompactSupport hc (r+1))

theorem compact_potential_quadratic_resolvent_le {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℕ)
    (v : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) (r+1)) :
    2*inner ℝ (v : OrderedTensorField φ (r+1))
        (compactPotentialTensorLp hφ.continuous hψ hc (r+1))-
      ‖compactPotentialTensorLp hφ.continuous hψ hc (r+2)‖^2-
      κ*‖compactPotentialTensorLp hφ.continuous hψ hc (r+1)‖^2 ≤
    ⟪(κ⁻¹ • (1-blockResolvent (centeredTensorIntegration hφ hκ hlower)
      (constantTensorIntegration hφ hκ hlower) κ (r+1))) v,v⟫_ℝ := by
  let F := compactPotentialTensorLp hφ.continuous hψ hc (r+1)
  let G := compactPotentialTensorLp hφ.continuous hψ hc (r+2)
  have hG := compactPotentialTensorLp_mem (hφ.of_le (by simp)) hψ hc (r+2)
  let X : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) (r+2) :=
    ⟨orderedTensorCenter φ (r+2) G,orderedTensorCenter_mem _ G hG,orderedTensorMeanPart_center G⟩
  let Y : ConstantCompatibleTensorHilbert (hφ.of_le (by simp)) (r+2) :=
    ⟨orderedTensorMeanPart φ (r+2) G,orderedTensorMeanPart_mem _ G hG,
      sub_eq_zero.mpr (orderedTensorMeanPart_idempotent G)⟩
  let J := centeredTensorIntegration hφ hκ hlower (r+1)
  let L := constantTensorIntegration hφ hκ hlower (r+1)
  let U := blockResolvent (centeredTensorIntegration hφ hκ hlower)
    (constantTensorIntegration hφ hκ hlower) κ (r+1)
  have hU : (1+κ • (J.comp J.adjoint+L.comp L.adjoint))*U=1 :=
    blockResolvent_inverse _ _ hκ.le (r+1)
  have hb := bounded_split_inverse_quadratic_duality J L U hκ hU v X Y
  have hinv : (J X+L Y : OrderedTensorField φ (r+1))=orderedTensorCenter φ (r+1) F := by
    change compatibleTensorPrimitive hφ hκ hlower (r+1)
      (G-orderedTensorMeanPart φ (r+2) G)+
      compatibleTensorPrimitive hφ hκ hlower (r+1) (orderedTensorMeanPart φ (r+2) G)=_
    rw [map_sub,sub_add_cancel]
    exact compatibleTensorPrimitive_compactPotential hφ hκ hlower hψ hc (r+1)
  have hnG : ‖G‖^2=‖X‖^2+‖Y‖^2 := by
    have hs := orderedTensor_split_norm_sq G
    change ‖G‖^2=‖orderedTensorCenter φ (r+2) G‖^2+
      ‖orderedTensorMeanPart φ (r+2) G‖^2
    linarith
  have hnF : ‖orderedTensorCenter φ (r+1) F‖^2 ≤ ‖F‖^2 := by
    nlinarith [orderedTensor_split_norm_sq F,sq_nonneg ‖orderedTensorMeanPart φ (r+1) F‖]
  have hi : inner ℝ (v : OrderedTensorField φ (r+1)) (orderedTensorCenter φ (r+1) F)=
      inner ℝ (v : OrderedTensorField φ (r+1)) F := by
    change inner ℝ (v : OrderedTensorField φ (r+1)) (F-orderedTensorMeanPart φ (r+1) F)=_
    rw [inner_sub_right,orderedTensorMeanPart_inner_centered,sub_zero]
  have hn : ‖J X+L Y‖^2=‖orderedTensorCenter φ (r+1) F‖^2 := by
    change ‖(J X+L Y : OrderedTensorField φ (r+1))‖^2=_
    rw [hinv]
  have hip : inner ℝ v (J X+L Y)=inner ℝ (v : OrderedTensorField φ (r+1)) F := by
    change inner ℝ (v : OrderedTensorField φ (r+1))
      (J X+L Y : OrderedTensorField φ (r+1))=_
    rw [hinv,hi]
  rw [hip,hn] at hb
  change 2*inner ℝ (v : OrderedTensorField φ (r+1)) F-‖G‖^2-κ*‖F‖^2 ≤ _
  have hmul := mul_le_mul_of_nonneg_left hnF hκ.le
  linarith [hb,hnG]

theorem actual_tensor_curvature_comparison_of_compact_estimate_and_density
    (hdense : ∀ r, Dense {u : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r |
      ∃ (ψ : Space n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ),
        u=compactPotentialDivergenceHilbert hφ hψ hc r})
    (hcurvature : ∀ (ψ : Space n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
      (hc : HasCompactSupport ψ) (r : ℕ),
      ‖compactPotentialTensorLp hφ.continuous hψ hc (r+2)‖^2+
        κ*‖compactPotentialTensorLp hφ.continuous hψ hc (r+1)‖^2 ≤
          ‖compactPotentialDivergenceHilbert hφ hψ hc r‖^2) :
    ActualTensorCurvatureComparison hφ hκ hlower := by
  intro r v
  apply norm_sq_le_of_dense_quadratic_tests _ (hdense r)
  rintro u ⟨ψ,hψ,hc,rfl⟩
  have hp := compatibleTensorInverse_compact_divergence_pairing hφ hκ hlower
    (fun I => (coordinatePotentialTensor_contDiff hψ (r+1) I).of_le (by simp))
    (coordinatePotentialTensor_hasCompactSupport hc (r+1))
    (coordinatePotentialTensor_symmetric hψ (r+1))
    (coordinatePotentialTensor_compatible hψ r)
    (centeredCompatibleTensorInclusion (hφ.of_le (by simp)) (r+1) v)
  change inner ℝ (centeredTensorIntegration hφ hκ hlower r v)
    (compactPotentialDivergenceHilbert hφ hψ hc r)=
      inner ℝ (v : OrderedTensorField φ (r+1))
        (compactPotentialTensorLp hφ.continuous hψ hc (r+1)) at hp
  rw [hp]
  have hb := compact_potential_quadratic_resolvent_le hφ hκ hlower hψ hc r v
  have hc' := hcurvature ψ hψ hc r
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.compact_potential_quadratic_resolvent_le
#print axioms KLS.DeterministicBridgeNext.actual_tensor_curvature_comparison_of_compact_estimate_and_density
