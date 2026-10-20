import Mathlib
noncomputable section
open InnerProductSpace ContinuousLinearMap
namespace KLSBelow25.ProjectionOrbitSlack
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
set_option maxHeartbeats 1000000

/-- Cauchy in the direct sum of the original Hilbert form and a positive
semidefinite form. It retains their shared resource before any norm bound. -/
theorem psd_block_cauchy_square (A : H→L[ℝ]H) (hA : A.adjoint=A)
    (hpos : ∀ z : H, 0≤⟪z,A z⟫_ℝ) (r x y v : H) :
    (⟪r,x⟫_ℝ+⟪y,A v⟫_ℝ)^2≤
      (‖r‖^2+⟪y,A y⟫_ℝ)*(‖x‖^2+⟪v,A v⟫_ℝ) := by
  have hcross : ⟪v,A y⟫_ℝ=⟪y,A v⟫_ℝ := by
    calc
      _=⟪v,A.adjoint y⟫_ℝ := by rw [hA]
      _=⟪A v,y⟫_ℝ := adjoint_inner_right A v y
      _=_ := real_inner_comm _ _
  have hquad (t : ℝ) :
      0≤(‖r‖^2+⟪y,A y⟫_ℝ)*(t*t)+
        (-2*(⟪r,x⟫_ℝ+⟪y,A v⟫_ℝ))*t+(‖x‖^2+⟪v,A v⟫_ℝ) := by
    have hh := add_nonneg (sq_nonneg ‖x-t•r‖) (hpos (v-t•y))
    rw [norm_sub_sq_real] at hh
    simp only [map_sub,map_smul,inner_sub_left,inner_sub_right,
      real_inner_smul_left,real_inner_smul_right,hcross,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs] at hh
    rw [←real_inner_comm x r] at hh
    nlinarith only [hh]
  have hd := discrim_le_zero hquad
  dsimp [discrim] at hd
  nlinarith only [hd]

end KLSBelow25.ProjectionOrbitSlack
#print axioms KLSBelow25.ProjectionOrbitSlack.psd_block_cauchy_square
