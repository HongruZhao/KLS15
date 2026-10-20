import CompatibleTensorDegreeZero
import AffineSchur

/-!
Exact Schur replacement on the actual closed distributional tensor carriers
used by KLS15. The joint estimate is an explicit hypothesis, not a universal
bound asserted by this module. In particular the theorem at four remains
conditional on the missing actual rank-zero joint quadratic-form bound.

No triangle estimate or graded-operator norm estimate is used in this bridge.
-/

noncomputable section
open MeasureTheory Matrix InnerProductSpace
open scoped ContDiff ENNReal BigOperators

namespace KLSImprovement.ActualAffineSchur
open KLS KLS.DeterministicBridgeIntegration

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

/-- The proposed improved estimate on the actual scalar centered primitive.
The covariance observation is the actual adjoint of constant integration. -/
def ActualRankZeroJointSchurBound (C : ℝ) : Prop :=
  ∀ G : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) 1,
    ‖centeredTensorIntegration hφ hκ hlower 0 G‖ ^ 2 +
      (C - 1)⁻¹ *
        ‖(constantTensorIntegration hφ hκ hlower 0).adjoint
          (centeredTensorIntegration hφ hκ hlower 0 G)‖ ^ 2 ≤ C * ‖G‖ ^ 2

theorem compatibleTensorPrimitive_norm_sq_le_of_joint_schur
    (hiso : IsIsotropic (potentialMeasure φ))
    {C : ℝ} (hC : 1 < C)
    (hjoint : ActualRankZeroJointSchurBound hφ hκ hlower C)
    (F : OrderedTensorField φ 1)
    (hF : F ∈ compatibleSymmetricTensorSubspace (hφ.of_le (by simp)) 1) :
    ‖compatibleTensorPrimitive hφ hκ hlower 0 F‖ ^ 2 ≤ C * ‖F‖ ^ 2 := by
  let E : ConstantCompatibleTensorHilbert (hφ.of_le (by simp)) 1 :=
    ⟨orderedTensorMeanPart φ 1 F,
      orderedTensorMeanPart_mem (hφ.of_le (by simp)) F hF,
      sub_eq_zero.mpr (orderedTensorMeanPart_idempotent F)⟩
  let G : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) 1 :=
    ⟨orderedTensorCenter φ 1 F,
      orderedTensorCenter_mem (hφ.of_le (by simp)) F hF,
      orderedTensorMeanPart_center F⟩
  have hsplit : compatibleTensorPrimitive hφ hκ hlower 0 F =
      (centeredTensorIntegration hφ hκ hlower 0 G : OrderedTensorField φ 0) +
        (constantTensorIntegration hφ hκ hlower 0 E : OrderedTensorField φ 0) := by
    rw [centeredTensorIntegration_coe, constantTensorIntegration_coe]
    change compatibleTensorPrimitive hφ hκ hlower 0 F =
      compatibleTensorPrimitive hφ hκ hlower 0 (F - orderedTensorMeanPart φ 1 F) +
        compatibleTensorPrimitive hφ hκ hlower 0 (orderedTensorMeanPart φ 1 F)
    rw [map_sub]
    abel
  have hbound :=
    (AffineSchur.full_primitive_bound_iff_joint_schur
      (E := ConstantCompatibleTensorHilbert (hφ.of_le (by simp)) 1)
      (G := CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) 1)
      (H := CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) 0)
      (centeredTensorIntegration hφ hκ hlower 0)
      (constantTensorIntegration hφ hκ hlower 0)
      (constantTensorIntegration_norm hφ hκ hlower hiso 0) C hC).mpr hjoint G E
  have hs : ‖F‖ ^ 2 = ‖E‖ ^ 2 + ‖G‖ ^ 2 := orderedTensor_split_norm_sq F
  rw [hsplit]
  change ‖centeredTensorIntegration hφ hκ hlower 0 G +
      constantTensorIntegration hφ hκ hlower 0 E‖ ^ 2 ≤ C * ‖F‖ ^ 2
  rw [hs]
  calc
    _ ≤ C * (‖G‖ ^ 2 + ‖E‖ ^ 2) := hbound
    _ = C * (‖E‖ ^ 2 + ‖G‖ ^ 2) := by ring

theorem poincareConstant_le_of_actual_joint_schur
    (hn : 0 < n) (hiso : IsIsotropic (potentialMeasure φ))
    {C : ℝ} (hC : 1 < C)
    (hjoint : ActualRankZeroJointSchurBound hφ hκ hlower C) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal C := by
  obtain ⟨lam, U, _, hlam, hU, hweak, _, hCP⟩ :=
    exists_positive_weighted_eigenpair_with_optimal_poincare
      hn (hφ.of_le (by simp)) hκ hlower
  have he : weightedEnergyForm φ U U = lam := by
    simpa only [real_inner_self_eq_norm_sq, hU, one_pow, mul_one] using hweak U
  have hb := compatibleTensorPrimitive_norm_sq_le_of_joint_schur hφ hκ hlower
    hiso hC hjoint (rankOneGraphGradient U) (rankOneGraphGradient_mem hφ U)
  rw [rankZeroGraphPrimitive_norm_sq, rankOneGraphGradient_norm_sq,
    weightedH1Gradient_norm_sq, hU, one_pow] at hb
  rw [← weightedEnergyForm_self, he] at hb
  have hr : lam⁻¹ ≤ C := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hlam).mpr (by nlinarith [hb])
  rw [hCP]
  exact ENNReal.ofReal_le_ofReal hr

theorem poincareConstant_le_four_of_actual_joint_schur
    (hn : 0 < n) (hiso : IsIsotropic (potentialMeasure φ))
    (hjoint : ActualRankZeroJointSchurBound hφ hκ hlower 4) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal 4 :=
  poincareConstant_le_of_actual_joint_schur hφ hκ hlower hn hiso (by norm_num) hjoint

end KLSImprovement.ActualAffineSchur

#print axioms KLSImprovement.ActualAffineSchur.compatibleTensorPrimitive_norm_sq_le_of_joint_schur
#print axioms KLSImprovement.ActualAffineSchur.poincareConstant_le_of_actual_joint_schur
#print axioms KLSImprovement.ActualAffineSchur.poincareConstant_le_four_of_actual_joint_schur
