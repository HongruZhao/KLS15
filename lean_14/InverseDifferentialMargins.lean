import C1InverseBarrier

/-! Conversion of a literal inverse differential residual to the paper's
pointwise criteria. Rational square-root majorants are used in the safe
direction. This contains no KLS or numerical barrier premise. -/
noncomputable section
namespace KLSBelow25
set_option maxHeartbeats 1000000

theorem inverse_q_identity {z Up d : ℝ} (hd : d=Up⁻¹) :
    -d/z = -1/(z*Up) := by
  rw [hd]
  ring

theorem inverse_margin_of_differential_residual {z Up q X d r : ℝ}
    (hz : 0<z) (hUp : Up<0) (hq : q = -1/(z*Up))
    (hres : 0 < X+(d*z+r*Real.sqrt z)*Up) :
    0 < q*X-d-r/Real.sqrt z := by
  have hden : 0 < -z*Up := by nlinarith
  have hs : Real.sqrt z*Real.sqrt z=z := Real.mul_self_sqrt hz.le
  have hsne : Real.sqrt z≠0 := (Real.sqrt_pos.mpr hz).ne'
  have hcancel : q*(-z*Up)=1 := by
    rw [hq]
    field_simp [ne_of_gt hz,ne_of_lt hUp]
  have hratio : (r/Real.sqrt z)*(-z*Up) = -r*Real.sqrt z*Up := by
    field_simp [hsne]
    rw [Real.sq_sqrt hz.le]
  have hid : (q*X-d-r/Real.sqrt z)*(-z*Up) = X+(d*z+r*Real.sqrt z)*Up := by
    calc
      _ = X*(q*(-z*Up))-d*(-z*Up)-(r/Real.sqrt z)*(-z*Up) := by ring
      _ = X+(d*z+r*Real.sqrt z)*Up := by rw [hcancel,hratio]; ring
  have hp : 0 < (q*X-d-r/Real.sqrt z)*(-z*Up) := by rw [hid]; exact hres
  exact (mul_pos_iff_of_pos_right hden).mp hp

theorem inverse_common_margin_of_majorant_residual {z u Up q alpha K A r R : ℝ}
    (hz : 0<z) (hUp : Up<0) (hq : q = -1/(z*Up)) (hrR : r≤R)
    (hres : 0 < alpha*K*z-A*u-R*Real.sqrt u+(2*z+R*Real.sqrt z)*Up) :
    0 < q*(alpha*K*z-A*u-r*Real.sqrt u)-2-r/Real.sqrt z := by
  have hcoef : Real.sqrt z*Up-Real.sqrt u ≤ 0 := by
    have := Real.sqrt_nonneg z
    have := Real.sqrt_nonneg u
    nlinarith
  have hloss : (R-r)*(Real.sqrt z*Up-Real.sqrt u) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hrR) hcoef
  apply inverse_margin_of_differential_residual hz hUp hq
  nlinarith

theorem inverse_seed_margin_of_majorant_residual {z u Up q alpha B A r R : ℝ}
    (hz : 0<z) (hUp : Up<0) (hq : q = -1/(z*Up)) (hrR : r≤R)
    (hres : 0 < alpha*(9*B/2)*z-(6*A-4)*u+(17*z+R*Real.sqrt z)*Up) :
    q*(alpha*(9*B/2)*z-(6*A-4)*u)>17+r/Real.sqrt z := by
  have hcoef : Real.sqrt z*Up ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg z) hUp.le
  have hloss : (R-r)*(Real.sqrt z*Up) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hrR) hcoef
  have hp : 0 < q*(alpha*(9*B/2)*z-(6*A-4)*u)-17-r/Real.sqrt z := by
    apply inverse_margin_of_differential_residual hz hUp hq
    nlinarith
  linarith

theorem zero_margin_of_slope_majorant {a p d r R : ℝ}
    (ha : 0<a) (hrR : r≤R) (hm : (d+R)*a<p) :
    0 < a⁻¹*p-d-r := by
  have hmul : (d+r)*a<p := lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith) ha.le) hm
  have hdiv : d+r<p/a := (lt_div_iff₀ ha).mpr hmul
  rw [inv_mul_eq_div]
  linarith

theorem sqrt_div_le_of_square_majorant {B K R : ℝ}
    (hB : 0≤B) (hK : 0<K) (hR : 0≤R) (hmajorant : B≤R^2*K^2) :
    Real.sqrt B/K≤R := by
  apply (div_le_iff₀ hK).mpr
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · nlinarith

theorem eight_div_sqrt_le_of_square_majorant {B R : ℝ}
    (hB : 0<B) (hR : 0≤R) (hmajorant : 64≤R^2*B) :
    8/Real.sqrt B≤R := by
  have hs := Real.sq_sqrt hB.le
  have hsp : 0<Real.sqrt B := Real.sqrt_pos.mpr hB
  apply (div_le_iff₀ hsp).mpr
  have hnonneg : 0≤R*Real.sqrt B := by positivity
  have hsq : 64≤(R*Real.sqrt B)^2 := by rw [mul_pow,hs]; exact hmajorant
  nlinarith

theorem seed_sqrt_denominator_identity {B z : ℝ} (hB : 0<B) (hz : 0<z) :
    (8/Real.sqrt B)/Real.sqrt z = 8/Real.sqrt (B*z) := by
  rw [Real.sqrt_mul hB.le]
  ring

end KLSBelow25
end

#print axioms KLSBelow25.inverse_margin_of_differential_residual
#print axioms KLSBelow25.inverse_common_margin_of_majorant_residual
#print axioms KLSBelow25.inverse_seed_margin_of_majorant_residual
#print axioms KLSBelow25.zero_margin_of_slope_majorant
#print axioms KLSBelow25.sqrt_div_le_of_square_majorant
#print axioms KLSBelow25.eight_div_sqrt_le_of_square_majorant
