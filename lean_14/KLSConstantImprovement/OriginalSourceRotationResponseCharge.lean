import KLSConstantImprovement.SourceThirdAdjointResponse

/-! A finite response-gradient null correction. Actual canonical source
IBP, the weighted rotation Gram and Lambda2 identification are analytic
inputs. This keeps the SAME response and datum range; no universal
numerical weighted-cost or Poincare bound is asserted. -/
noncomputable section
namespace KLSConstantImprovement.OriginalSourceRotationResponseCharge
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem null_rotation_keeps_response_cost (f : E) (b k : F)
    (r : E → F)
    (hcontract : ∀ v, ‖r v‖ ≤ ‖v‖)
    (hrep : ∀ v, inner ℝ f v = inner ℝ b (r v))
    (hnull : ∀ v, inner ℝ k (r v) = 0) :
    ‖f‖^2 ≤ ‖b-k‖^2 := by
  apply SourceThirdAdjointResponse.third_adjoint_norm_coercivity
    f (b-k) r hcontract
  intro v
  rw [inner_sub_left, hnull v, sub_zero]
  exact hrep v

/-- For `b=Hhalf e`, `k=Hhalf Z_rot X`, `z2=|Z_rot|^2`, the actual
rotation Gram pays `hcap`, and its adjoint mean pays `hcross`. -/
theorem rotation_cap_pays_half_charge (f : E) (b k : F)
    (r : E → F) {z2 : ℝ}
    (hcontract : ∀ v, ‖r v‖ ≤ ‖v‖)
    (hrep : ∀ v, inner ℝ f v = inner ℝ b (r v))
    (hnull : ∀ v, inner ℝ k (r v) = 0)
    (hcross : inner ℝ b k = z2)
    (hcap : ‖k‖^2 ≤ 2*z2) :
    ‖f‖^2+z2/2 ≤ ‖b‖^2 := by
  have hnull' : ∀ v, inner ℝ ((1/2:ℝ) • k) (r v) = 0 := by
    intro v
    simp [inner_smul_left, hnull v]
  have h := null_rotation_keeps_response_cost
    f b ((1/2:ℝ) • k) r hcontract hrep hnull'
  have hnorm : ‖(1/2:ℝ) • k‖^2 = (1/4:ℝ)*‖k‖^2 := by
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    ring
  have hinner : inner ℝ b ((1/2:ℝ) • k) = z2/2 := by
    simp [inner_smul_right, hcross]
    ring
  rw [norm_sub_sq_real, hnorm, hinner] at h
  linarith

theorem exponential_mixed_rotation_calibration :
    (1:ℝ)-(-1)^2/2=1/2 ∧ (1/4:ℝ)≤1/2 ∧
    (1/4:ℝ)+(1/2)/2≤1 := by norm_num

end KLSConstantImprovement.OriginalSourceRotationResponseCharge
#print axioms KLSConstantImprovement.OriginalSourceRotationResponseCharge.null_rotation_keeps_response_cost
#print axioms KLSConstantImprovement.OriginalSourceRotationResponseCharge.rotation_cap_pays_half_charge
#print axioms KLSConstantImprovement.OriginalSourceRotationResponseCharge.exponential_mixed_rotation_calibration
