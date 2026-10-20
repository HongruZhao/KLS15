import PairProjectionDefinitions

/-! The Hilbert square completion and scalar absorption used by the
all-rank pair projection. These are algebraic consequences of literal
projection data, without a measure or an endpoint hypothesis. -/
noncomputable section
open scoped RealInnerProductSpace
namespace KLSBelow25.PairProjection
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def leadingNoiseCoefficient (d : ℝ) : ℝ := 4*d^2+8*d*(d-2)/(3*(d-1))
def positiveNoiseCoefficient (d : ℝ) : ℝ := 2*d^2+2*d+8*d*(d-2)/(3*(d-1))
def covarianceNoiseForm (W V : H) (d Q : ℝ) : ℝ :=
  ‖W‖^2-2*inner ℝ W V+(1/2 : ℝ)*‖V‖^2+(1/2 : ℝ)*d*Q

theorem hilbert_square_completion (W V P : H) {δ : ℝ} (hδ : 0<δ)
    (hinner : inner ℝ W V=inner ℝ W P) :
    (1-δ)*‖W‖^2-‖P‖^2/δ≤‖W‖^2-2*inner ℝ W V := by
  have hs : 0≤‖δ • W-P‖^2 := sq_nonneg _
  rw [norm_sub_sq_real] at hs
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,real_inner_smul_left] at hs
  rw [←hinner] at hs
  have hdiv := div_nonneg hs hδ.le
  have he : (δ^2*‖W‖^2-2*(δ*inner ℝ W V)+‖P‖^2)/δ=
      δ*‖W‖^2-2*inner ℝ W V+‖P‖^2/δ := by field_simp
  rw [he] at hdiv
  linarith

theorem pair_noise_completion_of_projection_data (W V P : H) {d Q R S δ : ℝ}
    (hd : 3≤d) (hδ : 0<δ)
    (hinner : inner ℝ W V=inner ℝ W P)
    (hV : ‖V‖^2=d*Q+d*(d-1)*R)
    (hP : ‖P‖^2=(2*d/(d+1))*(Q+2*(d-1)*R+((d-1)*(d-2)/2)*S)) :
    (1-δ)*‖W‖^2+(d-2*d/((d+1)*δ))*Q+
      (d*(d-1)/2-4*d*(d-1)/((d+1)*δ))*R-
      d*(d-1)*(d-2)/((d+1)*δ)*S≤covarianceNoiseForm W V d Q := by
  have hc := hilbert_square_completion W V P hδ hinner
  have he : (1-δ)*‖W‖^2+(d-2*d/((d+1)*δ))*Q+
      (d*(d-1)/2-4*d*(d-1)/((d+1)*δ))*R-
      d*(d-1)*(d-2)/((d+1)*δ)*S=
      (1-δ)*‖W‖^2-‖P‖^2/δ+(1/2 : ℝ)*‖V‖^2+(1/2 : ℝ)*d*Q := by
    rw [hV,hP]
    field_simp
    ring
  rw [he]
  unfold covarianceNoiseForm
  linarith

theorem low_noise_bound_of_projection_data (W V P : H) {d Q R S δ E : ℝ}
    (hd : 3≤d) (hδ : 0<δ) (hδ1 : δ≤1) (hδlo : 2≤(d+1)*δ)
    (hinner : inner ℝ W V=inner ℝ W P)
    (hV : ‖V‖^2=d*Q+d*(d-1)*R)
    (hP : ‖P‖^2=(2*d/(d+1))*(Q+2*(d-1)*R+((d-1)*(d-2)/2)*S))
    (hresidual : (d-2)*S≤Q+(d-3)*R)
    (hR : R≤4*E) (hS : S≤(4+8/(3*(d-1)))*E) :
    (1-δ)*‖W‖^2-(leadingNoiseCoefficient d/δ-positiveNoiseCoefficient d)*E≤
      covarianceNoiseForm W V d Q := by
  have hc := pair_noise_completion_of_projection_data W V P hd hδ hinner hV hP
  have hd0 : 0<d := by linarith
  have hdm : 0<d-1 := by linarith
  have hden : 0<(d+1)*δ := mul_pos (by linarith) hδ
  have ha : 0≤d-2*d/((d+1)*δ) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hδlo hd0.le]
  have htwo : 2≤2/δ := (le_div_iff₀ hδ).mpr (by nlinarith)
  have hrc : d*(5-d)/2-2*d/δ≤0 := by
    have hh : (5-d)/2-2/δ≤0 := by linarith
    have hh' := mul_nonpos_of_nonneg_of_nonpos hd0.le hh
    convert hh' using 1; ring
  have hone : 1≤1/δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hsc : d*(d-2)*(1-1/δ)≤0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hd0.le (by linarith)) (by linarith)
  have hq0 : (d-2)*S-(d-3)*R≤Q := by linarith
  have hq := mul_le_mul_of_nonneg_left hq0 ha
  have hr := mul_le_mul_of_nonpos_left hR hrc
  have hs := mul_le_mul_of_nonpos_left hS hsc
  have hid : (d*(5-d)/2-2*d/δ)*(4*E)+
      (d*(d-2)*(1-1/δ))*((4+8/(3*(d-1)))*E)=
      -(leadingNoiseCoefficient d/δ-positiveNoiseCoefficient d)*E := by
    unfold leadingNoiseCoefficient positiveNoiseCoefficient
    field_simp
    ring
  have hcombine : (d*(5-d)/2-2*d/δ)*R+(d*(d-2)*(1-1/δ))*S=
      (d-2*d/((d+1)*δ))*((d-2)*S-(d-3)*R)+
      (d*(d-1)/2-4*d*(d-1)/((d+1)*δ))*R-
      d*(d-1)*(d-2)/((d+1)*δ)*S := by
    field_simp
    ring
  calc
    (1-δ)*‖W‖^2-(leadingNoiseCoefficient d/δ-positiveNoiseCoefficient d)*E=
        (1-δ)*‖W‖^2+(d*(5-d)/2-2*d/δ)*(4*E)+
          (d*(d-2)*(1-1/δ))*((4+8/(3*(d-1)))*E) := by linarith [hid]
    _≤(1-δ)*‖W‖^2+(d*(5-d)/2-2*d/δ)*R+(d*(d-2)*(1-1/δ))*S := by linarith
    _=(1-δ)*‖W‖^2+((d*(5-d)/2-2*d/δ)*R+(d*(d-2)*(1-1/δ))*S) := by ring
    _=(1-δ)*‖W‖^2+((d-2*d/((d+1)*δ))*((d-2)*S-(d-3)*R)+
      (d*(d-1)/2-4*d*(d-1)/((d+1)*δ))*R-
      d*(d-1)*(d-2)/((d+1)*δ)*S) := by rw [hcombine]
    _≤(1-δ)*‖W‖^2+(d-2*d/((d+1)*δ))*Q+
      (d*(d-1)/2-4*d*(d-1)/((d+1)*δ))*R-
      d*(d-1)*(d-2)/((d+1)*δ)*S := by linarith
    _≤covarianceNoiseForm W V d Q := hc

end KLSBelow25.PairProjection
#print axioms KLSBelow25.PairProjection.hilbert_square_completion
#print axioms KLSBelow25.PairProjection.pair_noise_completion_of_projection_data
#print axioms KLSBelow25.PairProjection.low_noise_bound_of_projection_data
