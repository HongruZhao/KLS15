import ProjectionOrbitSlackIdentity

/-! Quantitative restrictions from an actual projection observation.
No effective curvature or extra spectral gap is assumed. -/
noncomputable section
open InnerProductSpace ContinuousLinearMap
open scoped BigOperators
namespace KLSBelow25.ProjectionOrbitSlack
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem positive_form_apply_sq_le (A : H→L[ℝ]H) (hA : A.adjoint=A)
    {M : ℝ} (hM : 0<M)
    (hpos : ∀ x : H,0≤⟪x,A x⟫_ℝ)
    (hupper : ∀ x : H,⟪x,A x⟫_ℝ≤M*‖x‖^2) (x : H) :
    ‖A x‖^2≤M*⟪x,A x⟫_ℝ := by
  have hc : ⟪x,A (A x)⟫_ℝ=‖A x‖^2 := by
    rw [←hA,adjoint_inner_right,hA,real_inner_self_eq_norm_sq]
  have hh := hpos (M•x-A x)
  simp only [map_sub,map_smul,inner_sub_left,inner_sub_right,real_inner_smul_left,
    real_inner_smul_right,hc,real_inner_self_eq_norm_sq] at hh
  have hu := hupper (A x)
  nlinarith

theorem defect_quadratic (R P : H→L[ℝ]H)
    (hinner : ∀ v : H,⟪v,P v⟫_ℝ=‖P v‖^2) (v : H) :
    ⟪v,defect R P v⟫_ℝ=‖R.adjoint v‖^2+‖P v‖^2-‖R v‖^2 := by
  have hR : ⟪v,R (R.adjoint v)⟫_ℝ=‖R.adjoint v‖^2 := by
    rw [←adjoint_inner_left R (R.adjoint v) v,real_inner_self_eq_norm_sq]
  have hS : ⟪v,R.adjoint (R v)⟫_ℝ=‖R v‖^2 := by
    rw [adjoint_inner_right,real_inner_self_eq_norm_sq]
  simp only [defect,add_apply,sub_apply,comp_apply,inner_sub_right,inner_add_right,
    hR,hS,hinner]

theorem defect_apply_sq_le (R P : H→L[ℝ]H) (hP : P.adjoint=P)
    (hinner : ∀ v : H,⟪v,P v⟫_ℝ=‖P v‖^2)
    (hPnorm : ∀ v : H,‖P v‖≤‖v‖)
    (hcomp : ∀ v : H,‖R v‖^2≤‖R.adjoint v‖^2+‖P v‖^2) (v : H) :
    ‖defect R P v‖^2≤(‖R‖^2+1)*⟪v,defect R P v⟫_ℝ := by
  have hD : (defect R P).adjoint=defect R P := by
    simp only [defect,map_sub,map_add,adjoint_comp,adjoint_adjoint,hP]
  apply positive_form_apply_sq_le _ hD (by positivity)
  · intro x
    rw [defect_quadratic R P hinner]
    linarith [hcomp x]
  · intro x
    rw [defect_quadratic R P hinner]
    have hr := pow_le_pow_left₀ (norm_nonneg _) (R.adjoint.le_opNorm x) 2
    rw [adjoint.norm_map,mul_pow] at hr
    have hp := pow_le_pow_left₀ (norm_nonneg _) (hPnorm x) 2
    nlinarith [sq_nonneg ‖R x‖]

omit [CompleteSpace H] [InnerProductSpace ℝ H] in
theorem three_vector_sq_le (a b c : H) {A B C x y z : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C)
    (hx : 0≤x) (hy : 0≤y) (hz : 0≤z)
    (ha : ‖a‖^2≤A*x) (hb : ‖b‖^2≤B*y) (hc : ‖c‖^2≤C*z) :
    ‖a+b+c‖^2≤(A+B+C)*(x+y+z) := by
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (Fin 3))
    (r := ![‖a‖,‖b‖,‖c‖]) (f := ![A,B,C]) (g := ![x,y,z])
    (by intro i hi;fin_cases i;simpa using hA;simpa using hB;simpa using hC)
    (by intro i hi;fin_cases i;simpa using hx;simpa using hy;simpa using hz)
    (by intro i hi;fin_cases i;simpa using ha;simpa using hb;simpa using hc)
  simp only [Fin.sum_univ_succ,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_fin_one,Fin.sum_univ_zero,add_zero] at hh
  have hnorm : ‖a+b+c‖≤‖a‖+‖b‖+‖c‖ := by
    have h1 := norm_add_le (a+b) c
    have h2 := norm_add_le a b
    linarith
  have hn := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  exact hn.trans (by simpa only [add_assoc] using hh)

omit [CompleteSpace H] in
theorem projection_variance_le_residual (P : H→L[ℝ]H)
    (hinner : ∀ v : H,⟪v,P v⟫_ℝ=‖P v‖^2) (v : H) (hu : 0<‖v‖^2) (d : ℝ) :
    ‖P v‖^2-(‖P v‖^2)^2/‖v‖^2≤‖P v-d•v‖^2 := by
  rw [projection_residual_norm_sq P hinner]
  apply le_of_mul_le_mul_right (a := ‖v‖^2) ?_ hu
  have hs := sq_nonneg (d*‖v‖^2-‖P v‖^2)
  have he : (‖P v‖^2-(‖P v‖^2)^2/‖v‖^2)*‖v‖^2=
      ‖P v‖^2*‖v‖^2-(‖P v‖^2)^2 := by
    rw [sub_mul,div_mul_cancel₀ _ hu.ne']
  rw [he]
  nlinarith

theorem projection_variance_le_orbit_resource (R P : H→L[ℝ]H)
    (hP : P.adjoint=P) (hinner : ∀ v : H,⟪v,P v⟫_ℝ=‖P v‖^2)
    (hPnorm : ∀ v : H,‖P v‖≤‖v‖)
    (hcomp : ∀ v : H,‖R v‖^2≤‖R.adjoint v‖^2+‖P v‖^2)
    (u v w : H) (ρ σ : ℝ) (hv : v=R.adjoint u) (hw : w=R.adjoint v)
    (hvpos : 0<‖v‖^2) :
    ‖P v‖^2-(‖P v‖^2)^2/‖v‖^2≤(2*‖R‖^2+2)*
      (‖R v-ρ•u‖^2+⟪v,defect R P v⟫_ℝ+‖R w-σ•v‖^2) := by
  let x := R v-ρ•u
  let y := R w-σ•v
  have hd : 0≤⟪v,defect R P v⟫_ℝ := by
    rw [defect_quadratic R P hinner]
    linarith [hcomp v]
  have hx := pow_le_pow_left₀ (norm_nonneg _) (R.adjoint.le_opNorm x) 2
  rw [adjoint.norm_map,mul_pow] at hx
  have hD := defect_apply_sq_le R P hP hinner hPnorm hcomp v
  have hc := three_vector_sq_le (R.adjoint x) (-y) (defect R P v)
    (sq_nonneg ‖R‖) (by norm_num : (0:ℝ)≤1) (by positivity : 0≤‖R‖^2+1)
    (sq_nonneg ‖x‖) (sq_nonneg ‖y‖) hd hx (by simp only [norm_neg,one_mul];rfl) hD
  have he : P v-(ρ-σ)•v=R.adjoint x+(-y)+defect R P v := by
    have hh := projection_orbit_residual_identity R P u v w ρ σ hv hw
    dsimp [x,y]
    rw [hh]
    abel
  calc
    _≤‖P v-(ρ-σ)•v‖^2 := projection_variance_le_residual P hinner v hvpos _
    _=‖R.adjoint x+(-y)+defect R P v‖^2 := by rw [he]
    _≤_ := by
      dsimp [x,y] at hc
      convert hc using 1
      ring

theorem projection_variance_le_consecutive_slacks (R P : H→L[ℝ]H)
    (hP : P.adjoint=P) (hinner : ∀ v : H,⟪v,P v⟫_ℝ=‖P v‖^2)
    (hPnorm : ∀ v : H,‖P v‖≤‖v‖)
    (hcomp : ∀ v : H,‖R v‖^2≤‖R.adjoint v‖^2+‖P v‖^2)
    (u v w : H) (hv : v=R.adjoint u) (hw : w=R.adjoint v)
    (hupos : 0<‖u‖^2) (hvpos : 0<‖v‖^2) :
    ‖P v‖^2-(‖P v‖^2)^2/‖v‖^2≤(2*‖R‖^2+2)*
      ((‖w‖^2+‖P v‖^2-‖v‖^4/‖u‖^2)+
       (‖R.adjoint w‖^2+‖P w‖^2-‖w‖^4/‖v‖^2)) := by
  have hh := projection_variance_le_orbit_resource R P hP hinner hPnorm hcomp
    u v w (‖v‖^2/‖u‖^2) (‖w‖^2/‖v‖^2) hv hw hvpos
  have h1 := cauchy_comparison_slack_identity R P u v w hupos hv hw
  have h2 := cauchy_comparison_slack_identity R P v w (R.adjoint w) hvpos hw rfl
  rw [hinner] at h1 h2
  have hd : 0≤⟪w,defect R P w⟫_ℝ := by
    rw [defect_quadratic R P hinner]
    linarith [hcomp w]
  have hr : ‖R v-(‖v‖^2/‖u‖^2)•u‖^2+⟪v,defect R P v⟫_ℝ+
      ‖R w-(‖w‖^2/‖v‖^2)•v‖^2≤
      (‖w‖^2+‖P v‖^2-‖v‖^4/‖u‖^2)+
       (‖R.adjoint w‖^2+‖P w‖^2-‖w‖^4/‖v‖^2) := by linarith
  exact hh.trans (mul_le_mul_of_nonneg_left hr (by positivity))

end KLSBelow25.ProjectionOrbitSlack
#print axioms KLSBelow25.ProjectionOrbitSlack.positive_form_apply_sq_le
#print axioms KLSBelow25.ProjectionOrbitSlack.defect_apply_sq_le
#print axioms KLSBelow25.ProjectionOrbitSlack.three_vector_sq_le
#print axioms KLSBelow25.ProjectionOrbitSlack.projection_variance_le_residual

#print axioms KLSBelow25.ProjectionOrbitSlack.projection_variance_le_orbit_resource
#print axioms KLSBelow25.ProjectionOrbitSlack.projection_variance_le_consecutive_slacks
