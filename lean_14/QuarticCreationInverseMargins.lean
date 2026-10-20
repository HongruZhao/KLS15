import ActualQuarticCreation239Barrier

/-! Exact conversion of an inverse-branch residual margin into the genuine
quartic adjacent-energy scalar criterion. No actual-law estimate is assumed
or weakened by this algebraic conversion. -/
noncomputable section
namespace KLSBelow25
set_option maxHeartbeats 1000000

 theorem quartic_creation_criterion_of_inverse_margin
    {z H J u Z alpha a b c Up : ℝ}
    (hz : 0<z) (hH : 0<H) (hJ : 0<J) (hUp : Up<0)
    (_hu : 0≤u) (hZ : 0≤Z)
    (ha : 2*Real.sqrt (48*Z/H)≤a)
    (hb : 2*Real.sqrt (176*H/J)≤b)
    (hc : 2*Real.sqrt (13824*Z/J)≤c)
    (hmargin : 0<alpha*(J/H)*z-(44/(1-alpha)-32)*u-a*Real.sqrt u+
      (29*z+(b*Real.sqrt u+c)*Real.sqrt z)*Up) :
    (-1/(z*Up))*(alpha*J/H*z-(44/(1-alpha)-32)*u-
      2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J*z) := by
  have hsz : 0<Real.sqrt z := Real.sqrt_pos.2 hz
  have hsJ : 0<Real.sqrt J := Real.sqrt_pos.2 hJ
  have hsu : 0≤Real.sqrt u := Real.sqrt_nonneg u
  have haz : 2*Real.sqrt (48*Z)/Real.sqrt H≤a := by
    rw [Real.sqrt_div (by positivity : 0≤48*Z)] at ha
    simpa only [mul_div_assoc] using ha
  have hbz : 2*Real.sqrt (176*H)/Real.sqrt J≤b := by
    rw [Real.sqrt_div (by positivity : 0≤176*H)] at hb
    simpa only [mul_div_assoc] using hb
  have hcz : 2*Real.sqrt (13824*Z)/Real.sqrt J≤c := by
    rw [Real.sqrt_div (by positivity : 0≤13824*Z)] at hc
    simpa only [mul_div_assoc] using hc
  let A := alpha*J/H*z-(44/(1-alpha)-32)*u-
    2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u
  have hcore : 0<A+(29*z+(b*Real.sqrt u+c)*Real.sqrt z)*Up := by
    have hprod := mul_le_mul_of_nonneg_right haz hsu
    calc
      0 < alpha*(J/H)*z-(44/(1-alpha)-32)*u-a*Real.sqrt u+
          (29*z+(b*Real.sqrt u+c)*Real.sqrt z)*Up := hmargin
      _ ≤ A+(29*z+(b*Real.sqrt u+c)*Real.sqrt z)*Up := by
        dsimp [A]
        linear_combination hprod
  have hden : 0< -(z*Up) := neg_pos.mpr (mul_neg_of_pos_of_neg hz hUp)
  have hid : (29+(b*Real.sqrt u+c)/Real.sqrt z)*(-(z*Up))=
      -(29*z+(b*Real.sqrt u+c)*Real.sqrt z)*Up := by
    have hg : (b*Real.sqrt u+c)/Real.sqrt z*z=(b*Real.sqrt u+c)*Real.sqrt z := by
      calc
        _ = (b*Real.sqrt u+c)/Real.sqrt z*(Real.sqrt z)^2 := by rw [Real.sq_sqrt hz.le]
        _ = _ := by field_simp
    calc
      _ = -29*z*Up-((b*Real.sqrt u+c)/Real.sqrt z*z)*Up := by ring
      _ = _ := by rw [hg];ring
  have hm : 29+(b*Real.sqrt u+c)/Real.sqrt z<A/(-(z*Up)) := by
    apply (lt_div_iff₀ hden).2
    rw [hid]
    linarith
  have hcoeff : 2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J*z)≤
      (b*Real.sqrt u+c)/Real.sqrt z := by
    rw [Real.sqrt_mul (by positivity : 0≤176*H),Real.sqrt_mul hJ.le]
    apply (div_le_div_iff₀ (mul_pos hsJ hsz) hsz).2
    have hh := mul_le_mul_of_nonneg_right hbz hsu
    have hh' : 2*Real.sqrt (176*H)*Real.sqrt u≤(b*Real.sqrt u)*Real.sqrt J := by
      apply (div_le_iff₀ hsJ).1
      simpa only [div_mul_eq_mul_div] using hh
    have hc' := (div_le_iff₀ hsJ).1 hcz
    have hsum : 2*(Real.sqrt (176*H)*Real.sqrt u+Real.sqrt (13824*Z))≤
        (b*Real.sqrt u+c)*Real.sqrt J := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsum hsz.le]
  have hq : (-1/(z*Up))*A=A/(-(z*Up)) := by ring
  dsimp [A] at hq hm
  rw [hq]
  linarith

end KLSBelow25
#print axioms KLSBelow25.quartic_creation_criterion_of_inverse_margin
