import ProjectionOrbitSlackEstimate

/-! Sharp weighted Cauchy completion for the two consecutive comparison slacks.
The observation is a genuine orthogonal projection; no positive uniform defect
is assumed. -/
noncomputable section
open InnerProductSpace ContinuousLinearMap
namespace KLSBelow25.ProjectionOrbitSlack
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem projection_variance_le_weighted_orbit_resource (R P : H→L[ℝ]H)
    (hP : P.adjoint=P) (hinner : ∀ v : H,⟪v,P v⟫_ℝ=‖P v‖^2)
    (hPnorm : ∀ v : H,‖P v‖≤‖v‖)
    (hcomp : ∀ v : H,‖R v‖^2≤‖R.adjoint v‖^2+‖P v‖^2)
    (u v w : H) (ρ σ : ℝ) (hv : v=R.adjoint u) (hw : w=R.adjoint v)
    (hvpos : 0<‖v‖^2) {ω ζ : ℝ} (hω : 0<ω) (hζ : 0<ζ) :
    ‖P v‖^2-(‖P v‖^2)^2/‖v‖^2≤
      ((2*‖R‖^2+1)/ω+1/ζ)*
        (ω*(‖R v-ρ•u‖^2+⟪v,defect R P v⟫_ℝ)+ζ*‖R w-σ•v‖^2) := by
  let x := R v-ρ•u
  let y := R w-σ•v
  have hd : 0≤⟪v,defect R P v⟫_ℝ := by
    rw [defect_quadratic R P hinner]
    linarith [hcomp v]
  have hx := pow_le_pow_left₀ (norm_nonneg _) (R.adjoint.le_opNorm x) 2
  rw [adjoint.norm_map,mul_pow] at hx
  have hD := defect_apply_sq_le R P hP hinner hPnorm hcomp v
  have ha : ‖R.adjoint x‖^2≤(‖R‖^2/ω)*(ω*‖x‖^2) := by
    convert hx using 1; field_simp
  have hb : ‖defect R P v‖^2≤((‖R‖^2+1)/ω)*(ω*⟪v,defect R P v⟫_ℝ) := by
    convert hD using 1; field_simp
  have hc : ‖-y‖^2≤(1/ζ)*(ζ*‖y‖^2) := by
    simp only [norm_neg]
    rw [one_div,←mul_assoc,inv_mul_cancel₀ hζ.ne',one_mul]
  have hh := three_vector_sq_le (R.adjoint x) (defect R P v) (-y)
    (by positivity : 0≤‖R‖^2/ω) (by positivity : 0≤(‖R‖^2+1)/ω)
    (by positivity : 0≤1/ζ) (by positivity : 0≤ω*‖x‖^2)
    (mul_nonneg hω.le hd) (by positivity : 0≤ζ*‖y‖^2) ha hb hc
  have he : P v-(ρ-σ)•v=R.adjoint x+defect R P v+(-y) := by
    have hi := projection_orbit_residual_identity R P u v w ρ σ hv hw
    dsimp [x,y]
    rw [hi]
    abel
  calc
    _≤‖P v-(ρ-σ)•v‖^2 := projection_variance_le_residual P hinner v hvpos _
    _=‖R.adjoint x+defect R P v+(-y)‖^2 := by rw [he]
    _≤_ := by
      convert hh using 1; dsimp [x,y]; ring

theorem projection_variance_le_weighted_consecutive_slacks (R P : H→L[ℝ]H)
    (hP : P.adjoint=P) (hinner : ∀ v : H,⟪v,P v⟫_ℝ=‖P v‖^2)
    (hPnorm : ∀ v : H,‖P v‖≤‖v‖)
    (hcomp : ∀ v : H,‖R v‖^2≤‖R.adjoint v‖^2+‖P v‖^2)
    (u v w : H) (hv : v=R.adjoint u) (hw : w=R.adjoint v)
    (hupos : 0<‖u‖^2) (hvpos : 0<‖v‖^2)
    {ω ζ : ℝ} (hω : 0<ω) (hζ : 0<ζ) :
    ‖P v‖^2-(‖P v‖^2)^2/‖v‖^2≤
      ((2*‖R‖^2+1)/ω+1/ζ)*
        (ω*(‖w‖^2+‖P v‖^2-‖v‖^4/‖u‖^2)+
         ζ*(‖R.adjoint w‖^2+‖P w‖^2-‖w‖^4/‖v‖^2)) := by
  have hh := projection_variance_le_weighted_orbit_resource R P hP hinner hPnorm hcomp
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


theorem weighted_slack_normalize {S u v t₁ t₂ V M ω : ℝ}
    (_hS : 0<S) (hu : 0<u) (hv : 0<v) (_hω : 0<ω) (hω1 : ω<1)
    (ht₂ : 0≤t₂) (hM : 0≤M) (hvu : v≤S*u)
    (hraw : V≤M*(ω*t₁+((1-ω)/S)*t₂)) :
    V/u≤M*(ω*(t₁/u)+(1-ω)*(t₂/v)) := by
  have hd := div_le_div_of_nonneg_left ht₂ hv hvu
  have hr : (ω*t₁+((1-ω)/S)*t₂)/u≤ω*(t₁/u)+(1-ω)*(t₂/v) := by
    calc
      _=ω*(t₁/u)+(1-ω)*(t₂/(S*u)) := by ring
      _≤_ := by
        have hh := mul_le_mul_of_nonneg_left hd (by linarith : 0≤1-ω)
        linarith
  have hh := div_le_div_of_nonneg_right hraw hu.le
  calc
    V/u≤(M*(ω*t₁+((1-ω)/S)*t₂))/u := hh
    _=M*((ω*t₁+((1-ω)/S)*t₂)/u) := by ring
    _≤_ := mul_le_mul_of_nonneg_left hr hM

theorem projection_variance_normalized_le_weighted_slacks (R P : H→L[ℝ]H)
    (hP : P.adjoint=P) (hinner : ∀ v : H,⟪v,P v⟫_ℝ=‖P v‖^2)
    (hPnorm : ∀ v : H,‖P v‖≤‖v‖)
    (hcomp : ∀ v : H,‖R v‖^2≤‖R.adjoint v‖^2+‖P v‖^2)
    (u v w : H) (hv : v=R.adjoint u) (hw : w=R.adjoint v)
    (hupos : 0<‖u‖^2) (hvpos : 0<‖v‖^2) (hwpos : 0<‖w‖^2)
    {ω : ℝ} (hω : 0<ω) (hω1 : ω<1) :
    (‖P v‖^2-(‖P v‖^2)^2/‖v‖^2)/‖v‖^2≤
      ((2*‖R‖^2+1)/ω+‖R‖^2/(1-ω))*
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
  have hraw := projection_variance_le_weighted_consecutive_slacks R P hP hinner
    hPnorm hcomp u v w hv hw hupos hvpos hω hz
  have hh := weighted_slack_normalize hS hvpos hwpos hω hω1 ht₂
    (by positivity : 0≤(2*S+1)/ω+1/((1-ω)/S)) hnorm hraw
  have he : 1/((1-ω)/S)=S/(1-ω) := by field_simp
  dsimp [S,t₁,t₂] at hh he
  rw [he] at hh
  exact hh


theorem projection_observation_le_weighted_slack_payment (R P : H→L[ℝ]H)
    (hP : P.adjoint=P) (hinner : ∀ v : H,⟪v,P v⟫_ℝ=‖P v‖^2)
    (hPnorm : ∀ v : H,‖P v‖≤‖v‖)
    (hcomp : ∀ v : H,‖R v‖^2≤‖R.adjoint v‖^2+‖P v‖^2)
    (u v w : H) (hv : v=R.adjoint u) (hw : w=R.adjoint v)
    (hupos : 0<‖u‖^2) (hvpos : 0<‖v‖^2) (hwpos : 0<‖w‖^2)
    {ω η q : ℝ} (hω : 0<ω) (hω1 : ω<1)
    (hcap : ‖P v‖^2≤q*‖v‖^2)
    (hcoefficient : η*((2*‖R‖^2+1)/ω+‖R‖^2/(1-ω))≤1-q) :
    η*(‖P v‖^2/‖v‖^2)≤
      ω*((‖w‖^2+‖P v‖^2-‖v‖^4/‖u‖^2)/‖v‖^2)+
      (1-ω)*((‖R.adjoint w‖^2+‖P w‖^2-‖w‖^4/‖v‖^2)/‖w‖^2) := by
  let b := ‖P v‖^2/‖v‖^2
  let M := (2*‖R‖^2+1)/ω+‖R‖^2/(1-ω)
  have hM : 0<M := by dsimp [M];positivity
  have hb : 0≤b := div_nonneg (sq_nonneg _) hvpos.le
  have hbq : b≤q := (div_le_iff₀ hvpos).2 hcap
  have hvar := projection_variance_normalized_le_weighted_slacks R P hP hinner hPnorm
    hcomp u v w hv hw hupos hvpos hwpos hω hω1
  have he : (‖P v‖^2-(‖P v‖^2)^2/‖v‖^2)/‖v‖^2=b-b^2 := by dsimp [b];ring
  rw [he] at hvar
  have hbb := mul_le_mul_of_nonneg_right hbq hb
  have hcoef := mul_le_mul_of_nonneg_right hcoefficient hb
  apply le_of_mul_le_mul_right (a := M) ?_ hM
  dsimp [M] at *
  nlinarith only [hvar,hbb,hcoef]

end KLSBelow25.ProjectionOrbitSlack
#print axioms KLSBelow25.ProjectionOrbitSlack.projection_variance_le_weighted_orbit_resource
#print axioms KLSBelow25.ProjectionOrbitSlack.projection_variance_le_weighted_consecutive_slacks

#print axioms KLSBelow25.ProjectionOrbitSlack.weighted_slack_normalize
#print axioms KLSBelow25.ProjectionOrbitSlack.projection_variance_normalized_le_weighted_slacks

#print axioms KLSBelow25.ProjectionOrbitSlack.projection_observation_le_weighted_slack_payment
