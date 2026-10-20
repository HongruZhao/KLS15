import PositiveBlockCauchy
import ProjectionOrbitWeightedSlack
noncomputable section
open InnerProductSpace ContinuousLinearMap
open scoped BigOperators
namespace KLSBelow25.ProjectionOrbitSlack
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

 theorem two_real_sq_le {a b A B x y : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hx : 0≤x) (hy : 0≤y) (ha : a^2≤A*x) (hb : b^2≤B*y) :
    (a+b)^2≤(A+B)*(x+y) := by
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (Fin 2))
    (r:=![a,b]) (f:=![A,B]) (g:=![x,y])
    (by intro i hi;fin_cases i;simpa using hA;simpa using hB)
    (by intro i hi;fin_cases i;simpa using hx;simpa using hy)
    (by intro i hi;fin_cases i;simpa using ha;simpa using hb)
  simpa only [Fin.sum_univ_succ,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_fin_one,Fin.sum_univ_zero,add_zero] using hh

 theorem projection_variance_le_shared_weighted_orbit_resource (R P : H→L[ℝ]H)
    (hP : P.adjoint=P) (hinner : ∀ v : H,⟪v,P v⟫_ℝ=‖P v‖^2)
    (hPnorm : ∀ v : H,‖P v‖≤‖v‖)
    (hcomp : ∀ v : H,‖R v‖^2≤‖R.adjoint v‖^2+‖P v‖^2)
    (u v w : H) (rho sigma : ℝ) (hv : v=R.adjoint u) (hw : w=R.adjoint v)
    (hvpos : 0<‖v‖^2) {omega zeta : ℝ} (ho : 0<omega) (hz : 0<zeta) :
    ‖P v‖^2-(‖P v‖^2)^2/‖v‖^2≤
      ((‖R‖^2+1)/omega+1/zeta)*
        (omega*(‖R v-rho•u‖^2+⟪v,defect R P v⟫_ℝ)+zeta*‖R w-sigma•v‖^2) := by
  let D := defect R P
  let x := R v-rho•u
  let next := R w-sigma•v
  let c := ‖P v‖^2/‖v‖^2
  let y := P v-c•v
  let V := ‖P v‖^2-(‖P v‖^2)^2/‖v‖^2
  have hD : D.adjoint=D := by
    dsimp [D,defect]
    simp only [map_sub,map_add,adjoint_comp,adjoint_adjoint,hP]
  have hDpos (z : H) : 0≤⟪z,D z⟫_ℝ := by
    dsimp [D]
    rw [defect_quadratic R P hinner]
    linarith [hcomp z]
  have hyv : ⟪y,v⟫_ℝ=0 := by
    dsimp [y,c]
    rw [inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
      ←real_inner_comm (P v) v,hinner,div_mul_cancel₀ _ hvpos.ne']
    ring
  have hynorm : ‖y‖^2=V := by
    rw [show y=P v-c•v by rfl,projection_residual_norm_sq P hinner]
    dsimp [c,V]
    field_simp
    ring
  have hyP : ⟪y,P v⟫_ℝ=V := by
    dsimp [y,V,c]
    rw [inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,hinner]
    ring
  have hpair : V=⟪R y,x⟫_ℝ+⟪y,D v⟫_ℝ-⟪y,next⟫_ℝ := by
    have hh := congrArg (fun z : H=>⟪y,z⟫_ℝ)
      (projection_orbit_residual_identity R P u v w rho sigma hv hw)
    rw [hyP] at hh
    simp only [inner_add_right,inner_sub_right,real_inner_smul_right,hyv,mul_zero,
      zero_add] at hh
    rw [adjoint_inner_right] at hh
    dsimp [D,x,next] at hh ⊢
    simp only [inner_sub_right,real_inner_smul_right,hyv,mul_zero] at hh ⊢
    linarith
  have hV : 0≤V := hynorm ▸ sq_nonneg ‖y‖
  have ht : 0≤‖x‖^2+⟪v,D v⟫_ℝ := add_nonneg (sq_nonneg _) (hDpos v)
  have hC : ‖R y‖^2+⟪y,D y⟫_ℝ≤(‖R‖^2+1)*V := by
    have he := defect_quadratic R P hinner y
    have hr := pow_le_pow_left₀ (norm_nonneg _) (R.adjoint.le_opNorm y) 2
    rw [adjoint.norm_map,mul_pow,hynorm] at hr
    have hp := pow_le_pow_left₀ (norm_nonneg _) (hPnorm y) 2
    rw [hynorm] at hp
    change ⟪y,D y⟫_ℝ=_ at he
    nlinarith
  have hfirst := (psd_block_cauchy_square D hD hDpos (R y) x y v).trans
    (mul_le_mul_of_nonneg_right hC ht)
  have hlast := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm y next) 2
  rw [sq_abs,mul_pow,hynorm] at hlast
  have hfirst' : (⟪R y,x⟫_ℝ+⟪y,D v⟫_ℝ)^2≤
      ((‖R‖^2+1)*V/omega)*(omega*(‖x‖^2+⟪v,D v⟫_ℝ)) := by
    convert hfirst using 1
    field_simp
  have hlast' : (-⟪y,next⟫_ℝ)^2≤(V/zeta)*(zeta*‖next‖^2) := by
    rw [neg_sq]
    convert hlast using 1
    field_simp
  have hh := two_real_sq_le (a:=⟪R y,x⟫_ℝ+⟪y,D v⟫_ℝ) (b:=-⟪y,next⟫_ℝ)
    (by positivity : 0≤(‖R‖^2+1)*V/omega) (div_nonneg hV hz.le)
    (mul_nonneg ho.le ht) (by positivity : 0≤zeta*‖next‖^2) hfirst' hlast'
  rw [←sub_eq_add_neg,←hpair] at hh
  have he : ((‖R‖^2+1)*V/omega+V/zeta)*
      (omega*(‖x‖^2+⟪v,D v⟫_ℝ)+zeta*‖next‖^2)=
      V*(((‖R‖^2+1)/omega+1/zeta)*
        (omega*(‖x‖^2+⟪v,D v⟫_ℝ)+zeta*‖next‖^2)) := by ring
  rw [he] at hh
  by_cases h0 : V=0
  · change V≤_
    rw [h0]
    exact mul_nonneg (by positivity) (add_nonneg (mul_nonneg ho.le ht) (by positivity))
  · have hv' : 0<V := lt_of_le_of_ne hV (Ne.symm h0)
    have hc : V*V≤V*(((‖R‖^2+1)/omega+1/zeta)*
        (omega*(‖x‖^2+⟪v,D v⟫_ℝ)+zeta*‖next‖^2)) := by
      simpa only [pow_two] using hh
    exact le_of_mul_le_mul_left hc hv'


theorem projection_variance_le_shared_weighted_consecutive_slacks (R P : H→L[ℝ]H)
    (hP : P.adjoint=P) (hinner : ∀ v : H,⟪v,P v⟫_ℝ=‖P v‖^2)
    (hPnorm : ∀ v : H,‖P v‖≤‖v‖)
    (hcomp : ∀ v : H,‖R v‖^2≤‖R.adjoint v‖^2+‖P v‖^2)
    (u v w : H) (hv : v=R.adjoint u) (hw : w=R.adjoint v)
    (hupos : 0<‖u‖^2) (hvpos : 0<‖v‖^2)
    {ω ζ : ℝ} (hω : 0<ω) (hζ : 0<ζ) :
    ‖P v‖^2-(‖P v‖^2)^2/‖v‖^2≤
      ((‖R‖^2+1)/ω+1/ζ)*
        (ω*(‖w‖^2+‖P v‖^2-‖v‖^4/‖u‖^2)+
         ζ*(‖R.adjoint w‖^2+‖P w‖^2-‖w‖^4/‖v‖^2)) := by
  have hh := projection_variance_le_shared_weighted_orbit_resource R P hP hinner hPnorm hcomp
    u v w (‖v‖^2/‖u‖^2) (‖w‖^2/‖v‖^2) hv hw hvpos hω hζ
  have h1 := cauchy_comparison_slack_identity R P u v w hupos hv hw
  have h2 := cauchy_comparison_slack_identity R P v w (R.adjoint w) hvpos hw rfl
  rw [hinner] at h1 h2
  have hd : 0≤⟪w,defect R P w⟫_ℝ := by
    rw [defect_quadratic R P hinner]
    linarith [hcomp w]
  have hr : ω*(‖R v-(‖v‖^2/‖u‖^2)•u‖^2+⟪v,defect R P v⟫_ℝ)+
      ζ*‖R w-(‖w‖^2/‖v‖^2)•v‖^2≤
      ω*(‖w‖^2+‖P v‖^2-‖v‖^4/‖u‖^2)+
      ζ*(‖R.adjoint w‖^2+‖P w‖^2-‖w‖^4/‖v‖^2) := by
    nlinarith [mul_nonneg hζ.le hd]
  exact hh.trans (mul_le_mul_of_nonneg_left hr (by positivity))


theorem projection_variance_normalized_le_shared_weighted_slacks (R P : H→L[ℝ]H)
    (hP : P.adjoint=P) (hinner : ∀ v : H,⟪v,P v⟫_ℝ=‖P v‖^2)
    (hPnorm : ∀ v : H,‖P v‖≤‖v‖)
    (hcomp : ∀ v : H,‖R v‖^2≤‖R.adjoint v‖^2+‖P v‖^2)
    (u v w : H) (hv : v=R.adjoint u) (hw : w=R.adjoint v)
    (hupos : 0<‖u‖^2) (hvpos : 0<‖v‖^2) (hwpos : 0<‖w‖^2)
    {ω : ℝ} (hω : 0<ω) (hω1 : ω<1) :
    (‖P v‖^2-(‖P v‖^2)^2/‖v‖^2)/‖v‖^2≤
      ((‖R‖^2+1)/ω+‖R‖^2/(1-ω))*
        (ω*((‖w‖^2+‖P v‖^2-‖v‖^4/‖u‖^2)/‖v‖^2)+
         (1-ω)*((‖R.adjoint w‖^2+‖P w‖^2-‖w‖^4/‖v‖^2)/‖w‖^2)) := by
  let S := ‖R‖^2
  let t₁ := ‖w‖^2+‖P v‖^2-‖v‖^4/‖u‖^2
  let t₂ := ‖R.adjoint w‖^2+‖P w‖^2-‖w‖^4/‖v‖^2
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (R.adjoint.le_opNorm v) 2
  rw [adjoint.norm_map,mul_pow,←hw] at hnorm
  have hS : 0<S := by dsimp [S];nlinarith [sq_nonneg ‖v‖]
  have ht₂ : 0≤t₂ := by
    have hh := cauchy_comparison_slack_identity R P v w (R.adjoint w) hvpos hw rfl
    rw [hinner] at hh
    have hd : 0≤⟪w,defect R P w⟫_ℝ := by
      rw [defect_quadratic R P hinner]
      linarith [hcomp w]
    dsimp [t₂]
    nlinarith [sq_nonneg ‖R w-(‖w‖^2/‖v‖^2)•v‖]
  have hz : 0<(1-ω)/S := div_pos (by linarith) hS
  have hraw := projection_variance_le_shared_weighted_consecutive_slacks R P hP hinner
    hPnorm hcomp u v w hv hw hupos hvpos hω hz
  have hh := weighted_slack_normalize hS hvpos hwpos hω hω1 ht₂
    (by positivity : 0≤(S+1)/ω+1/((1-ω)/S)) hnorm hraw
  have he : 1/((1-ω)/S)=S/(1-ω) := by field_simp
  dsimp [S,t₁,t₂] at hh he
  rw [he] at hh
  exact hh


theorem projection_observation_le_shared_weighted_slack_payment (R P : H→L[ℝ]H)
    (hP : P.adjoint=P) (hinner : ∀ v : H,⟪v,P v⟫_ℝ=‖P v‖^2)
    (hPnorm : ∀ v : H,‖P v‖≤‖v‖)
    (hcomp : ∀ v : H,‖R v‖^2≤‖R.adjoint v‖^2+‖P v‖^2)
    (u v w : H) (hv : v=R.adjoint u) (hw : w=R.adjoint v)
    (hupos : 0<‖u‖^2) (hvpos : 0<‖v‖^2) (hwpos : 0<‖w‖^2)
    {ω η q : ℝ} (hω : 0<ω) (hω1 : ω<1)
    (hcap : ‖P v‖^2≤q*‖v‖^2)
    (hcoefficient : η*((‖R‖^2+1)/ω+‖R‖^2/(1-ω))≤1-q) :
    η*(‖P v‖^2/‖v‖^2)≤
      ω*((‖w‖^2+‖P v‖^2-‖v‖^4/‖u‖^2)/‖v‖^2)+
      (1-ω)*((‖R.adjoint w‖^2+‖P w‖^2-‖w‖^4/‖v‖^2)/‖w‖^2) := by
  let b := ‖P v‖^2/‖v‖^2
  let M := (‖R‖^2+1)/ω+‖R‖^2/(1-ω)
  have hM : 0<M := by dsimp [M];positivity
  have hb : 0≤b := div_nonneg (sq_nonneg _) hvpos.le
  have hbq : b≤q := (div_le_iff₀ hvpos).2 hcap
  have hvar := projection_variance_normalized_le_shared_weighted_slacks R P hP hinner hPnorm
    hcomp u v w hv hw hupos hvpos hwpos hω hω1
  have he : (‖P v‖^2-(‖P v‖^2)^2/‖v‖^2)/‖v‖^2=b-b^2 := by dsimp [b];ring
  rw [he] at hvar
  have hbb := mul_le_mul_of_nonneg_right hbq hb
  have hcoef := mul_le_mul_of_nonneg_right hcoefficient hb
  apply le_of_mul_le_mul_right (a := M) ?_ hM
  dsimp [M] at *
  nlinarith only [hvar,hbb,hcoef]

end KLSBelow25.ProjectionOrbitSlack
#print axioms KLSBelow25.ProjectionOrbitSlack.projection_variance_le_shared_weighted_orbit_resource

#print axioms KLSBelow25.ProjectionOrbitSlack.projection_variance_le_shared_weighted_consecutive_slacks

#print axioms KLSBelow25.ProjectionOrbitSlack.projection_variance_normalized_le_shared_weighted_slacks

#print axioms KLSBelow25.ProjectionOrbitSlack.projection_observation_le_shared_weighted_slack_payment
