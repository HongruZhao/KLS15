import KLSConstantImprovement.HessianMomentScalar

/-! A source third-adjoint Riesz coercivity component. Actual source IBP,
vector Bochner, graph-range density, and same original-law geometry are
analytic inputs. The numerical cross4/response2 caps are hypotheses. -/
noncomputable section
namespace KLSConstantImprovement.SourceThirdAdjointResponse

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem third_adjoint_norm_coercivity (a : E) (b : F) (r : E → F)
    (hcontract : ∀ v, ‖r v‖ ≤ ‖v‖)
    (hrep : ∀ v, inner ℝ a v = inner ℝ b (r v)) :
    ‖a‖^2 ≤ ‖b‖^2 := by
  have hc : ‖a‖^2 ≤ ‖b‖ * ‖a‖ := by
    calc
      ‖a‖^2 = inner ℝ b (r a) := by
        rw [← hrep a, real_inner_self_eq_norm_sq]
      _ ≤ |inner ℝ b (r a)| := le_abs_self _
      _ ≤ ‖b‖ * ‖r a‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖b‖ * ‖a‖ := mul_le_mul_of_nonneg_left (hcontract a) (norm_nonneg b)
  have hnorm : ‖a‖ ≤ ‖b‖ := by
    by_contra h
    have hlt : ‖b‖ < ‖a‖ := lt_of_not_ge h
    nlinarith [norm_nonneg a, norm_nonneg b]
  nlinarith [norm_nonneg a, norm_nonneg b]

theorem source_adjoint_split_residual (a f : E) {V J : ℝ}
    (hvariance : V = 9 * ‖a + f‖^2) :
    V - 9 * J =
      18 * inner ℝ a f + 9 * ‖f‖^2 - 9 * (J - ‖a‖^2) := by
  rw [norm_add_sq_real] at hvariance
  nlinarith

/-- The two same-source numeric caps remain unproved analytic premises. -/
theorem joint_cross_response_caps_pay_ninety (a f : E) {V J N : ℝ}
    (hvariance : V = 9 * ‖a + f‖^2)
    (hprojection : ‖a‖^2 ≤ J)
    (hcross : inner ℝ a f ≤ 4 * N)
    (hresponse : ‖f‖^2 ≤ 2 * N) :
    V - 9 * J ≤ 90 * N := by
  have h := source_adjoint_split_residual a f (J := J) hvariance
  linarith

theorem joint_cross_response_caps_give_cubic336 (a f : E) {V J N : ℝ}
    (hN : 0 ≤ N)
    (hvariance : V = 9 * ‖a + f‖^2)
    (hprojection : ‖a‖^2 ≤ J)
    (hcross : inner ℝ a f ≤ 4 * N)
    (hresponse : ‖f‖^2 ≤ 2 * N)
    (hmain : J ≤ (16 + 8 * Real.sqrt 2) * N) :
    V ≤ 336 * N := by
  have hres := joint_cross_response_caps_pay_ninety a f
    hvariance hprojection hcross hresponse
  exact KLSConstantImprovement.HessianMomentScalar.residual_ninety_gives_cubic336
    hN hmain (by linarith)

theorem exponential_adjoint_calibration :
    (216:ℝ) - 9 * 14 = 18 * 4 + 9 * 2 - 9 * 0 ∧
    (18:ℝ) * 4 + 9 * 2 = 90 := by
  norm_num

end KLSConstantImprovement.SourceThirdAdjointResponse
#print axioms KLSConstantImprovement.SourceThirdAdjointResponse.third_adjoint_norm_coercivity
#print axioms KLSConstantImprovement.SourceThirdAdjointResponse.source_adjoint_split_residual
#print axioms KLSConstantImprovement.SourceThirdAdjointResponse.joint_cross_response_caps_pay_ninety
#print axioms KLSConstantImprovement.SourceThirdAdjointResponse.joint_cross_response_caps_give_cubic336
#print axioms KLSConstantImprovement.SourceThirdAdjointResponse.exponential_adjoint_calibration
