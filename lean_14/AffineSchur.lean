import Mathlib

/-!
Exact affine Schur complement for a centered compatible primitive `J` and the
isometric linear primitive `L`.  These are genuine continuous linear maps on
real Hilbert spaces, and the covariance charge is the genuine Hilbert adjoint
`L.adjoint (J g)`.  No Poincare or log-concavity hypothesis is introduced here.

The equivalence replaces the triangle estimate on the full primitive by a
joint quadratic-form target.  It does not assert that the new target holds at
four, or supply a new analytic estimate on `J`.
-/

noncomputable section

namespace KLSImprovement.AffineSchur

variable {E G H : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem exact_identity
    (J : G →L[ℝ] H) (L : E →L[ℝ] H)
    (hL : ∀ b : E, ‖L b‖ = ‖b‖)
    (C : ℝ) (hC : 1 < C) (g : G) (b : E) :
    C * (‖g‖ ^ 2 + ‖b‖ ^ 2) - ‖J g + L b‖ ^ 2 =
      (C - 1) * ‖b - (C - 1)⁻¹ • (L.adjoint (J g))‖ ^ 2 +
        C * ‖g‖ ^ 2 - ‖J g‖ ^ 2 -
          (C - 1)⁻¹ * ‖L.adjoint (J g)‖ ^ 2 := by
  have hne : C - 1 ≠ 0 := by linarith
  have hcros : inner ℝ (J g) (L b) = inner ℝ b (L.adjoint (J g)) := by
    rw [real_inner_comm, ContinuousLinearMap.adjoint_inner_right]
  rw [norm_add_sq_real, norm_sub_sq_real, hL, hcros]
  simp only [inner_smul_right, Real.norm_eq_abs, norm_smul, mul_pow, sq_abs]
  field_simp [hne]
  ring

theorem full_primitive_bound_iff_joint_schur
    (J : G →L[ℝ] H) (L : E →L[ℝ] H)
    (hL : ∀ b : E, ‖L b‖ = ‖b‖)
    (C : ℝ) (hC : 1 < C) :
    (∀ (g : G) (b : E), ‖J g + L b‖ ^ 2 ≤
      C * (‖g‖ ^ 2 + ‖b‖ ^ 2)) ↔
    (∀ g : G, ‖J g‖ ^ 2 +
      (C - 1)⁻¹ * ‖L.adjoint (J g)‖ ^ 2 ≤ C * ‖g‖ ^ 2) := by
  constructor
  · intro h g
    let b : E := (C - 1)⁻¹ • (L.adjoint (J g))
    have hb := h g b
    have hid := exact_identity J L hL C hC g b
    have hzero : b - (C - 1)⁻¹ • (L.adjoint (J g)) = 0 := sub_self _
    rw [hzero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hid
    linarith
  · intro h g b
    have hj := h g
    have hid := exact_identity J L hL C hC g b
    have hs : 0 ≤ (C - 1) *
        ‖b - (C - 1)⁻¹ • (L.adjoint (J g))‖ ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    linarith

theorem reverse_observation_sufficient
    (J : G →L[ℝ] H) (L : E →L[ℝ] H)
    (hL : ∀ b : E, ‖L b‖ = ‖b‖)
    (S q C : ℝ) (hC : 1 < C)
    (hJ : ∀ g : G, ‖J g‖ ^ 2 ≤ S * ‖g‖ ^ 2)
    (hobs : ∀ g : G,
      ‖L.adjoint (J g)‖ ^ 2 ≤ q * ‖g‖ ^ 2)
    (hbudget : S + (C - 1)⁻¹ * q ≤ C) :
    ∀ (g : G) (b : E), ‖J g + L b‖ ^ 2 ≤
      C * (‖g‖ ^ 2 + ‖b‖ ^ 2) := by
  apply (full_primitive_bound_iff_joint_schur J L hL C hC).mpr
  intro g
  have hi : 0 ≤ (C - 1)⁻¹ := inv_nonneg.mpr (by linarith)
  have ho := mul_le_mul_of_nonneg_left (hobs g) hi
  have hb := mul_le_mul_of_nonneg_right hbudget (sq_nonneg ‖g‖)
  nlinarith [hJ g]

theorem four_bound_iff_joint_schur
    (J : G →L[ℝ] H) (L : E →L[ℝ] H)
    (hL : ∀ b : E, ‖L b‖ = ‖b‖) :
    (∀ (g : G) (b : E), ‖J g + L b‖ ^ 2 ≤
      4 * (‖g‖ ^ 2 + ‖b‖ ^ 2)) ↔
    (∀ g : G, ‖J g‖ ^ 2 +
      (1 / 3 : ℝ) * ‖L.adjoint (J g)‖ ^ 2 ≤ 4 * ‖g‖ ^ 2) := by
  convert full_primitive_bound_iff_joint_schur J L hL (4 : ℝ) (by norm_num) using 1
  norm_num

end KLSImprovement.AffineSchur

#print axioms KLSImprovement.AffineSchur.exact_identity
#print axioms KLSImprovement.AffineSchur.full_primitive_bound_iff_joint_schur
#print axioms KLSImprovement.AffineSchur.reverse_observation_sufficient
#print axioms KLSImprovement.AffineSchur.four_bound_iff_joint_schur
