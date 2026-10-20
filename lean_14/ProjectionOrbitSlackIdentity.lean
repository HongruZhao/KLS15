import Mathlib

/-! Extra orbit constraints when the observation Gram is a projection.
These exact identities retain the Cauchy/comparison slack discarded by the
scalar relaxation. They do not assert a new universal numerical estimate. -/
noncomputable section
open InnerProductSpace ContinuousLinearMap
namespace KLSBelow25.ProjectionOrbitSlack
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def defect (R P : H→L[ℝ]H) : H→L[ℝ]H :=
  R.comp R.adjoint+P-R.adjoint.comp R

theorem projection_orbit_residual_identity (R P : H→L[ℝ]H)
    (u v w : H) (ρ σ : ℝ) (hv : v=R.adjoint u) (hw : w=R.adjoint v) :
    P v=(ρ-σ)•v+R.adjoint (R v-ρ•u)-(R w-σ•v)+defect R P v := by
  simp only [defect,add_apply,sub_apply,comp_apply,map_sub,map_smul,sub_smul]
  rw [←hv,hw]
  abel

omit [CompleteSpace H] in
theorem projection_residual_norm_sq (P : H→L[ℝ]H)
    (hinner : ∀ v : H,⟪v,P v⟫_ℝ=‖P v‖^2) (v : H) (d : ℝ) :
    ‖P v-d•v‖^2=(1-2*d)*‖P v‖^2+d^2*‖v‖^2 := by
  rw [norm_sub_sq_real,inner_smul_right,real_inner_comm,hinner,norm_smul,
    Real.norm_eq_abs,mul_pow,sq_abs]
  ring

theorem cauchy_comparison_slack_identity (R P : H→L[ℝ]H)
    (u v w : H) (_hu : 0<‖u‖^2) (hv : v=R.adjoint u) (hw : w=R.adjoint v) :
    ‖w‖^2+⟪v,P v⟫_ℝ-‖v‖^4/‖u‖^2=
      ‖R v-(‖v‖^2/‖u‖^2)•u‖^2+⟪v,defect R P v⟫_ℝ := by
  have hi : ⟪R v,u⟫_ℝ=‖v‖^2 := by
    rw [←adjoint_inner_right,←hv,real_inner_self_eq_norm_sq]
  have hj : ⟪v,R (R.adjoint v)⟫_ℝ=‖w‖^2 := by
    rw [←adjoint_inner_left,←hw,real_inner_self_eq_norm_sq]
  have hk : ⟪v,R.adjoint (R v)⟫_ℝ=‖R v‖^2 := by
    rw [adjoint_inner_right,real_inner_self_eq_norm_sq]
  simp only [norm_sub_sq_real,inner_smul_right,hi,norm_smul,Real.norm_eq_abs,mul_pow,
    sq_abs,defect,add_apply,sub_apply,comp_apply,inner_sub_right,inner_add_right,hj,hk]
  field_simp [_hu.ne']
  ring

theorem zero_slack_projection_dichotomy (R P : H→L[ℝ]H)
    (hinner : ∀ v : H,⟪v,P v⟫_ℝ=‖P v‖^2)
    (u v w : H) (ρ σ : ℝ) (hv : v=R.adjoint u) (hw : w=R.adjoint v)
    (hx : R v=ρ•u) (hy : R w=σ•v) (hD : defect R P v=0)
    (hv0 : v≠0) : ρ-σ=0 ∨ ρ-σ=1 := by
  have h := projection_orbit_residual_identity R P u v w ρ σ hv hw
  rw [hx,hy,sub_self,map_zero,sub_self,hD] at h
  simp only [add_zero,sub_zero] at h
  have hh := hinner v
  rw [h,inner_smul_right,real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs] at hh
  have hn : 0<‖v‖^2 := pow_pos (norm_pos_iff.mpr hv0) 2
  have he : (ρ-σ)*(ρ-σ-1)=0 := by nlinarith
  rcases mul_eq_zero.mp he with h0|h1
  · exact Or.inl h0
  · right;linarith

end KLSBelow25.ProjectionOrbitSlack
#print axioms KLSBelow25.ProjectionOrbitSlack.projection_orbit_residual_identity
#print axioms KLSBelow25.ProjectionOrbitSlack.projection_residual_norm_sq
#print axioms KLSBelow25.ProjectionOrbitSlack.cauchy_comparison_slack_identity
#print axioms KLSBelow25.ProjectionOrbitSlack.zero_slack_projection_dichotomy
