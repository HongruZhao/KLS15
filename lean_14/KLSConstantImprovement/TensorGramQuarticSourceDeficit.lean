import Mathlib

/-! The new quartic source Gram square and matched cubic disk.
The pointwise operator/source contractions, conservative integration,
BL matrix, matched means and original joint approximation are explicit
analytic identifications in the companion proof. No raw336 or CP<14
claim is asserted without the SAME-field response hypothesis. -/
noncomputable section
namespace KLSConstantImprovement.TensorGramQuarticSourceDeficit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Apply with u=BK and v=KB in matrix Hilbert space. -/
theorem half_commutator_square (u v : E)
    (htranspose : ‖u‖^2=‖v‖^2) :
    ‖u‖^2-inner ℝ u v=‖u-v‖^2/2 := by
  rw [norm_sub_sq_real]
  nlinarith

theorem quartic_source_deficit_identity {F mean energy curvature comm D : ℝ}
    (henergy : 2*F=curvature+2*energy+comm/2)
    (hdeficit : D=energy-F+mean) :
    D+curvature/2+comm/4=mean := by linarith

theorem quartic_source_deficit_cap {F mean energy curvature comm D : ℝ}
    (hp : 0≤curvature) (hc : 0≤comm)
    (henergy : 2*F=curvature+2*energy+comm/2)
    (hdeficit : D=energy-F+mean) :
    D ≤ mean := by linarith

theorem matched_cross_bound {r delta top bottom cross : ℝ}
    (hr : 0≤r) (htop : 0≤top)
    (htopcap : top≤delta/2) (hbottomcap : bottom≤2*r)
    (hBL : cross^2≤top*bottom) :
    cross^2≤r*delta := by
  have h1 := mul_nonneg htop (sub_nonneg.mpr hbottomcap)
  have h2 := mul_nonneg hr (sub_nonneg.mpr htopcap)
  nlinarith

theorem matched_cubic_disk {N r delta cross : ℝ}
    (hr : 0≤r) (hdelta : delta≤2*N-r)
    (hcross : cross^2≤r*delta) :
    (r-N)^2+cross^2≤N^2 := by
  have hp := mul_nonneg hr (sub_nonneg.mpr hdelta)
  nlinarith

theorem cubic_disk_linear_cap {N r cross : ℝ}
    (hN : 0≤N) (hdisk : (r-N)^2+cross^2≤N^2) :
    r-cross≤(1+Real.sqrt 2)*N := by
  have hr := Real.sqrt_nonneg (2:ℝ)
  have hrs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have heq : (Real.sqrt 2*N)^2=2*N^2 := by rw [mul_pow, hrs]
  have hsq : ((r-N)-cross)^2≤2*N^2 := by
    nlinarith [sq_nonneg ((r-N)+cross)]
  have hlin : (r-N)-cross≤Real.sqrt 2*N := by
    by_contra h
    have hlt : Real.sqrt 2*N<(r-N)-cross := lt_of_not_ge h
    have hu : 0<(r-N)-cross := lt_of_le_of_lt (by positivity) hlt
    have hsum : 0<(r-N)-cross+Real.sqrt 2*N := by
      nlinarith
    have hp := mul_pos (sub_pos.mpr hlt) hsum
    nlinarith
  nlinarith

theorem direct_tensor_third_moment_cap {N r cross W p rem : ℝ}
    (hN : 0≤N) (hp : 0≤p) (hrem : 0≤rem)
    (hdisk : (r-N)^2+cross^2≤N^2)
    (hsource : W+2*p+2*rem=3*r-3*cross) :
    W+2*p+2*rem≤(3+3*Real.sqrt 2)*N ∧
    W≤(3+3*Real.sqrt 2)*N := by
  have h := cubic_disk_linear_cap hN hdisk
  constructor <;> nlinarith

theorem tensor_third_disk_coefficient_lt_seven_point_five :
    (3+3*Real.sqrt (2:ℝ))<15/2 := by
  have hr := Real.sqrt_nonneg (2:ℝ)
  have hrs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem affine_trace_disk_discount {N W J q : ℝ}
    (hW : W≤(3+3*Real.sqrt 2)*N)
    (hdiscount : Real.sqrt 2*J+q≤(Real.sqrt 2+2)*W) :
    Real.sqrt 2*J+q≤(12+9*Real.sqrt 2)*N := by
  have hr := Real.sqrt_nonneg (2:ℝ)
  have hrs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hp := mul_nonneg (show 0≤Real.sqrt (2:ℝ)+2 by positivity)
    (sub_nonneg.mpr hW)
  have heq : (Real.sqrt (2:ℝ)+2)*(3+3*Real.sqrt 2)*N=
      (12+9*Real.sqrt 2)*N := by
    calc
      (Real.sqrt (2:ℝ)+2)*(3+3*Real.sqrt 2)*N=
          (6+9*Real.sqrt 2+3*(Real.sqrt 2)^2)*N := by ring
      _=(12+9*Real.sqrt 2)*N := by rw [hrs]; ring
  nlinarith

theorem affine_trace_disk_cap {N J q : ℝ} (hq : 0≤q)
    (hpaid : Real.sqrt 2*J+q≤(12+9*Real.sqrt 2)*N) :
    J≤(9+6*Real.sqrt 2)*N := by
  have hr : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hrs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have heq : Real.sqrt 2*((9+6*Real.sqrt 2)*N)=
      (12+9*Real.sqrt 2)*N := by
    calc
      Real.sqrt 2*((9+6*Real.sqrt 2)*N)=
          (9*Real.sqrt 2+6*(Real.sqrt 2)^2)*N := by ring
      _=(12+9*Real.sqrt 2)*N := by rw [hrs]; ring
  have h : Real.sqrt 2*J≤Real.sqrt 2*((9+6*Real.sqrt 2)*N) := by
    rw [heq]
    linarith
  exact (mul_le_mul_iff_right₀ hr).mp h

theorem conditional_compensated_source_response {N V J res q : ℝ}
    (hmain : Real.sqrt 2*J+q≤(12+9*Real.sqrt 2)*N)
    (hvariance : V=9*J+res)
    (hresponse : Real.sqrt 2*res≤90*Real.sqrt 2*N+9*q) :
    Real.sqrt 2*V≤(108+171*Real.sqrt 2)*N := by
  have hv : Real.sqrt 2 * V =
      9 * (Real.sqrt 2 * J) + Real.sqrt 2 * res := by
    rw [hvariance]
    ring
  nlinarith

theorem conditional_raw_cap {N V : ℝ}
    (hpaid : Real.sqrt 2*V≤(108+171*Real.sqrt 2)*N) :
    V≤(171+54*Real.sqrt 2)*N := by
  have hr : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hrs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have heq : Real.sqrt 2*((171+54*Real.sqrt 2)*N)=
      (108+171*Real.sqrt 2)*N := by
    calc
      Real.sqrt 2*((171+54*Real.sqrt 2)*N)=
          (171*Real.sqrt 2+54*(Real.sqrt 2)^2)*N := by ring
      _=(108+171*Real.sqrt 2)*N := by rw [hrs]; ring
  rw [← heq] at hpaid
  exact (mul_le_mul_iff_right₀ hr).mp hpaid

end KLSConstantImprovement.TensorGramQuarticSourceDeficit
#print axioms KLSConstantImprovement.TensorGramQuarticSourceDeficit.half_commutator_square
#print axioms KLSConstantImprovement.TensorGramQuarticSourceDeficit.quartic_source_deficit_identity
#print axioms KLSConstantImprovement.TensorGramQuarticSourceDeficit.quartic_source_deficit_cap
#print axioms KLSConstantImprovement.TensorGramQuarticSourceDeficit.matched_cross_bound
#print axioms KLSConstantImprovement.TensorGramQuarticSourceDeficit.matched_cubic_disk
#print axioms KLSConstantImprovement.TensorGramQuarticSourceDeficit.cubic_disk_linear_cap
#print axioms KLSConstantImprovement.TensorGramQuarticSourceDeficit.direct_tensor_third_moment_cap
#print axioms KLSConstantImprovement.TensorGramQuarticSourceDeficit.tensor_third_disk_coefficient_lt_seven_point_five
#print axioms KLSConstantImprovement.TensorGramQuarticSourceDeficit.affine_trace_disk_discount
#print axioms KLSConstantImprovement.TensorGramQuarticSourceDeficit.affine_trace_disk_cap
#print axioms KLSConstantImprovement.TensorGramQuarticSourceDeficit.conditional_compensated_source_response
#print axioms KLSConstantImprovement.TensorGramQuarticSourceDeficit.conditional_raw_cap
