import PositiveResolventContraction

/-! Quadratic duality for the genuine bounded inverse-gradient Gram.
No spectral-calculus or form-domain equivalence premise is used. -/
noncomputable section
namespace KLSBelow25
open ContinuousLinearMap InnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem bounded_inverse_quadratic_duality
    (T : E →L[ℝ] H) (U : H →L[ℝ] H) {a : ℝ} (ha : 0 < a)
    (hU : (1+a • (T.comp T.adjoint))*U=1) (v : H) (z : E) :
    2*⟪v,T z⟫_ℝ-‖z‖^2-a*‖T z‖^2 ≤
      ⟪(a⁻¹ • (1-U)) v,v⟫_ℝ := by
  let w := U v
  let y := T.adjoint w
  have hv : v=w+a • T y := by
    have he := congrArg (fun A : H →L[ℝ] H => A v) hU
    simpa only [_root_.mul_apply_eq_comp,add_apply,one_apply_eq_self,smul_apply,
      comp_apply] using he.symm
  have hp : ⟪w,T z⟫_ℝ=⟪y,z⟫_ℝ := (adjoint_inner_left T z w).symm
  have hyy : ⟪w,T y⟫_ℝ=‖y‖^2 := by
    rw [←adjoint_inner_left,real_inner_self_eq_norm_sq]
  have he : ⟪T y,v⟫_ℝ=‖y‖^2+a*‖T y‖^2 := by
    rw [hv,inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
      real_inner_comm w (T y),hyy]
  have hr : (a⁻¹ • (1-U)) v=T y := by
    change a⁻¹ • (v-w)=T y
    rw [hv,add_sub_cancel_left,inv_smul_smul₀ ha.ne']
  rw [hr,he]
  have hnorm1 := norm_sub_sq_real z y
  have hnorm2 := norm_sub_sq_real (T z) (T y)
  have hpair : ⟪v,T z⟫_ℝ=⟪y,z⟫_ℝ+a*⟪T y,T z⟫_ℝ := by
    rw [hv,inner_add_left,real_inner_smul_left,hp]
  rw [hpair]
  rw [real_inner_comm y z] at hnorm1
  rw [real_inner_comm (T y) (T z)] at hnorm2
  nlinarith [sq_nonneg ‖z-y‖,mul_nonneg ha.le (sq_nonneg ‖T z-T y‖)]

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

theorem bounded_split_inverse_quadratic_duality
    (J : G →L[ℝ] H) (L : E →L[ℝ] H) (U : H →L[ℝ] H) {a : ℝ} (ha : 0 < a)
    (hU : (1+a • (J.comp J.adjoint+L.comp L.adjoint))*U=1)
    (v : H) (x : G) (y : E) :
    2*⟪v,J x+L y⟫_ℝ-‖x‖^2-‖y‖^2-a*‖J x+L y‖^2 ≤
      ⟪(a⁻¹ • (1-U)) v,v⟫_ℝ := by
  let w := U v
  let x₀ := J.adjoint w
  let y₀ := L.adjoint w
  let z₀ := J x₀+L y₀
  let z := J x+L y
  have hv : v=w+a • z₀ := by
    have he := congrArg (fun A : H →L[ℝ] H => A v) hU
    simpa only [_root_.mul_apply_eq_comp,add_apply,one_apply_eq_self,smul_apply,
      comp_apply] using he.symm
  have hp : ⟪w,z⟫_ℝ=⟪x₀,x⟫_ℝ+⟪y₀,y⟫_ℝ := by
    dsimp [z,x₀,y₀]
    rw [inner_add_right,←adjoint_inner_left J x w,←adjoint_inner_left L y w]
  have hp₀ : ⟪w,z₀⟫_ℝ=‖x₀‖^2+‖y₀‖^2 := by
    dsimp [z₀]
    rw [inner_add_right,←adjoint_inner_left J x₀ w,←adjoint_inner_left L y₀ w,
      real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  have he : ⟪z₀,v⟫_ℝ=‖x₀‖^2+‖y₀‖^2+a*‖z₀‖^2 := by
    rw [hv,inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
      real_inner_comm w z₀,hp₀]
  have hr : (a⁻¹ • (1-U)) v=z₀ := by
    change a⁻¹ • (v-w)=z₀
    rw [hv,add_sub_cancel_left,inv_smul_smul₀ ha.ne']
  rw [hr,he]
  have hx := norm_sub_sq_real x x₀
  have hy := norm_sub_sq_real y y₀
  have hz := norm_sub_sq_real z z₀
  have hpair : ⟪v,z⟫_ℝ=⟪x₀,x⟫_ℝ+⟪y₀,y⟫_ℝ+a*⟪z₀,z⟫_ℝ := by
    rw [hv,inner_add_left,real_inner_smul_left,hp]
  change 2*⟪v,z⟫_ℝ-‖x‖^2-‖y‖^2-a*‖z‖^2 ≤ _
  rw [hpair]
  rw [real_inner_comm x₀ x] at hx
  rw [real_inner_comm y₀ y] at hy
  rw [real_inner_comm z₀ z] at hz
  nlinarith [sq_nonneg ‖x-x₀‖,sq_nonneg ‖y-y₀‖,
    mul_nonneg ha.le (sq_nonneg ‖z-z₀‖)]

theorem norm_sq_le_of_dense_quadratic_tests (S : Set H) (hS : Dense S)
    (u : H) {C : ℝ} (hC : ∀ v ∈ S, 2*⟪u,v⟫_ℝ-‖v‖^2 ≤ C) :
    ‖u‖^2 ≤ C := by
  have hc : IsClosed {v : H | 2*⟪u,v⟫_ℝ-‖v‖^2 ≤ C} := by
    apply isClosed_le _ continuous_const
    exact (continuous_const.mul (continuous_const.inner continuous_id)).sub
      (continuous_norm.pow 2)
  have hs := hc.closure_subset_iff.mpr hC
  have hu := hs (hS u)
  change 2*⟪u,u⟫_ℝ-‖u‖^2 ≤ C at hu
  rw [real_inner_self_eq_norm_sq] at hu
  linarith

end KLSBelow25
#print axioms KLSBelow25.bounded_inverse_quadratic_duality
#print axioms KLSBelow25.bounded_split_inverse_quadratic_duality
#print axioms KLSBelow25.norm_sq_le_of_dense_quadratic_tests
