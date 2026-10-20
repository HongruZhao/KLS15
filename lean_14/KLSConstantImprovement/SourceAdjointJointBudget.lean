import KLSConstantImprovement.SourceThirdAdjointResponse

/-! The signed source adjoint/response gate retains its projection loss.
Actual source Riesz, vector-Bochner and range/core identifications are
analytic inputs. This module supplies no universal numerical bound for
the signed joint expression and assumes no separate cross/response caps.
Its sufficient payoff is the already accepted conditional raw336 chain. -/
noncomputable section
namespace KLSConstantImprovement.SourceAdjointJointBudget
open SourceThirdAdjointResponse

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem adjoint_projection_defect_identity (a : E) (b r : F) {curvature : ℝ}
    (hpair : inner ℝ a a = inner ℝ b r)
    (hbochner : ‖a‖^2 = ‖r‖^2 + curvature) :
    ‖b‖^2 - ‖a‖^2 = ‖b-r‖^2 + curvature := by
  rw [real_inner_self_eq_norm_sq] at hpair
  rw [norm_sub_sq_real]
  nlinarith

theorem adjoint_projection_defect_nonneg (a : E) (b r : F) {curvature : ℝ}
    (hpair : inner ℝ a a = inner ℝ b r)
    (hbochner : ‖a‖^2 = ‖r‖^2 + curvature)
    (hcurvature : 0 ≤ curvature) :
    0 ≤ ‖b‖^2 - ‖a‖^2 := by
  rw [adjoint_projection_defect_identity a b r hpair hbochner]
  exact add_nonneg (sq_nonneg _) hcurvature

theorem joint_gate_iff_residual_ninety (a f : E) {V J N : ℝ}
    (hvariance : V = 9 * ‖a+f‖^2) :
    2 * inner ℝ a f + ‖f‖^2 - (J-‖a‖^2) ≤ 10*N ↔
      V-9*J ≤ 90*N := by
  have h := source_adjoint_split_residual a f (J := J) hvariance
  constructor <;> intro hbound <;> linarith

theorem signed_joint_budget_gives_cubic336 (a f : E) {V J N : ℝ}
    (hN : 0 ≤ N) (hvariance : V = 9 * ‖a+f‖^2)
    (hmain : J ≤ (16+8*Real.sqrt 2)*N)
    (hjoint : 2 * inner ℝ a f + ‖f‖^2 - (J-‖a‖^2) ≤ 10*N) :
    V ≤ 336*N := by
  have hr := (joint_gate_iff_residual_ninety a f hvariance).mp hjoint
  exact KLSConstantImprovement.HessianMomentScalar.residual_ninety_gives_cubic336
    hN hmain hr

theorem retained_null_charge_pays_joint_gate (a f : E) {J N charge : ℝ}
    (hcharge : charge ≤ J-‖a‖^2)
    (hjoint : 2 * inner ℝ a f + ‖f‖^2 - charge ≤ 10*N) :
    2 * inner ℝ a f + ‖f‖^2 - (J-‖a‖^2) ≤ 10*N := by
  linarith

end KLSConstantImprovement.SourceAdjointJointBudget
#print axioms KLSConstantImprovement.SourceAdjointJointBudget.adjoint_projection_defect_identity
#print axioms KLSConstantImprovement.SourceAdjointJointBudget.adjoint_projection_defect_nonneg
#print axioms KLSConstantImprovement.SourceAdjointJointBudget.joint_gate_iff_residual_ninety
#print axioms KLSConstantImprovement.SourceAdjointJointBudget.signed_joint_budget_gives_cubic336
#print axioms KLSConstantImprovement.SourceAdjointJointBudget.retained_null_charge_pays_joint_gate
