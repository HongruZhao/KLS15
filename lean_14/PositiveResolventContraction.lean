import RealOperatorComplexification

/-! The actual inverse of I+aT is contractive when T is positive.
The resulting rational quadratic form is nonnegative. -/
noncomputable section
namespace KLSBelow25
open ContinuousLinearMap InnerProductSpace
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem positive_resolvent_apply_norm_le
    (T U : H →L[ℝ] H) (hT : T.IsPositive) {a : ℝ} (ha : 0 ≤ a)
    (hU : (1+a • T)*U=1) (v : H) : ‖U v‖ ≤ ‖v‖ := by
  have he : (1+a • T) (U v)=v := congrArg (fun A : H →L[ℝ] H => A v) hU
  have hp := hT.re_inner_nonneg_left (U v)
  simp only [RCLike.re_to_real] at hp
  have hi : ‖U v‖^2 ≤ ⟪v,U v⟫_ℝ := by
    calc
      _ ≤ ⟪(1+a • T) (U v),U v⟫_ℝ := by
        simp only [add_apply,one_apply_eq_self,smul_apply,inner_add_left,
          real_inner_smul_left,real_inner_self_eq_norm_sq]
        nlinarith
      _ = _ := by rw [he]
  have hs := real_inner_le_norm v (U v)
  nlinarith [norm_nonneg v,norm_nonneg (U v)]

theorem positive_resolvent_norm_le_one
    (T U : H →L[ℝ] H) (hT : T.IsPositive) {a : ℝ} (ha : 0 ≤ a)
    (hU : (1+a • T)*U=1) : ‖U‖ ≤ 1 := by
  apply U.opNorm_le_bound zero_le_one
  intro v
  simpa only [one_mul] using positive_resolvent_apply_norm_le T U hT ha hU v

theorem positive_resolvent_rational_nonneg
    (T U : H →L[ℝ] H) (hT : T.IsPositive) {a : ℝ} (ha : 0 ≤ a)
    (hU : (1+a • T)*U=1) (v : H) :
    0 ≤ ⟪(a⁻¹ • (1-U)) v,v⟫_ℝ := by
  have hu := positive_resolvent_apply_norm_le T U hT ha hU v
  have hi : ⟪U v,v⟫_ℝ ≤ ‖v‖^2 :=
    (real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg v])
  simp only [smul_apply,sub_apply,one_apply_eq_self,real_inner_smul_left,
    inner_sub_left,real_inner_self_eq_norm_sq]
  exact mul_nonneg (inv_nonneg.mpr ha) (sub_nonneg.mpr hi)

variable [CompleteSpace H]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
open RealHilbertComplexification

theorem realCanonicalIntegrationResolvent_norm_le_one
    (R : H →L[ℝ] H) (L : F →L[ℝ] H) {a : ℝ} (ha : 0 ≤ a) :
    ‖realCanonicalIntegrationResolvent R L a‖ ≤ 1 :=
  positive_resolvent_norm_le_one _ _ (realIntegrationGram_isPositive R L) ha
    (realCanonicalIntegrationResolvent_inverse R L ha)

theorem realCanonicalIntegrationResolvent_rational_nonneg
    (R : H →L[ℝ] H) (L : F →L[ℝ] H) {a : ℝ} (ha : 0 ≤ a) (v : H) :
    0 ≤ ⟪(a⁻¹ • (1-realCanonicalIntegrationResolvent R L a)) v,v⟫_ℝ :=
  positive_resolvent_rational_nonneg _ _ (realIntegrationGram_isPositive R L) ha
    (realCanonicalIntegrationResolvent_inverse R L ha) v

#print axioms positive_resolvent_apply_norm_le
#print axioms positive_resolvent_rational_nonneg
#print axioms realCanonicalIntegrationResolvent_norm_le_one
end KLSBelow25
