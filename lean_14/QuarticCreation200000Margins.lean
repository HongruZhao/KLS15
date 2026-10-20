import QuarticCreation200000Calculus
import QuarticCreationInverseMargins
import QuarticSeed239EnvelopeCap
noncomputable section
open Set
namespace KLSBelow25.QuarticCreation200000
open KLSBelow25
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem radical_majorants_of_rho {rho a c Z:ℝ}
    (_hrho:0 ≤ rho) (ha:0 ≤ a) (hc:0 ≤ c) (hZ:0 ≤ Z) (hcap:Z ≤ 8*rho)
    (hasq:4*384*rho/H ≤ a^2) (hcsq:4*110592*rho/J ≤ c^2) :
    2*Real.sqrt (48*Z/H) ≤ a ∧ 2*Real.sqrt (176*H/J) ≤ radicalB ∧
      2*Real.sqrt (13824*Z/J) ≤ c := by
  have hH:=H_positive
  have hJ:=J_positive
  have hA0:0 ≤ 48*Z/H := by positivity
  have hC0:0 ≤ 13824*Z/J := by positivity
  have hB0:0 ≤ 176*H/J := by positivity
  have hAd:48*Z/H ≤ 384*rho/H :=
    div_le_div_of_nonneg_right (by linarith) hH.le
  have hCd:13824*Z/J ≤ 110592*rho/J :=
    div_le_div_of_nonneg_right (by linarith) hJ.le
  have hAs:=Real.sq_sqrt hA0
  have hBs:=Real.sq_sqrt hB0
  have hCs:=Real.sq_sqrt hC0
  have hbn:=radicalB_positive
  have hbs:=radicalB_square
  have hAsq : (2*Real.sqrt (48*Z/H))^2 ≤ a^2 := by
    calc
      _ = 4*(48*Z/H) := by nlinarith [hAs]
      _ ≤ 4*(384*rho/H) := by linarith
      _ = 4*384*rho/H := by ring
      _ ≤ a^2 := hasq
  have hBsq : (2*Real.sqrt (176*H/J))^2 ≤ radicalB^2 := by
    calc
      _ = 4*(176*H/J) := by nlinarith [hBs]
      _ = 4*176*H/J := by ring
      _ ≤ radicalB^2 := hbs
  have hCsq : (2*Real.sqrt (13824*Z/J))^2 ≤ c^2 := by
    calc
      _ = 4*(13824*Z/J) := by nlinarith [hCs]
      _ ≤ 4*(110592*rho/J) := by linarith
      _ = 4*110592*rho/J := by ring
      _ ≤ c^2 := hcsq
  exact ⟨(sq_le_sq₀ (by positivity) ha).mp hAsq,
    (sq_le_sq₀ (by positivity) hbn.le).mp hBsq,
    (sq_le_sq₀ (by positivity) hc).mp hCsq⟩

theorem variable_margin_of_signs {a c t:ℝ} (ht:0<t) (htT:t ≤ seedT)
    (hP:0<variableP a t) (hQ:0<variableQ c t)
    (hdet:0<(variableP a t)^2-(1-t^2)*(variableQ c t)^2) :
    0<seedAlphaAt t*(J/H)*(1-t^2)-(44/(1-seedAlphaAt t)-32)*(t^2*(seedV t)^2)-
      a*t*seedV t+(29*(1-t^2)+(radicalB*t*seedV t+c)*Real.sqrt (1-t^2))*(-(seedV t*seedSlope t)) := by
  rw [variable_residual_identity a c ht htT]
  exact VariableAlpha24.sqrt_residual_positive
    (VariableAlpha24.parameterized_z_positive ht.le htT seedT_range.2) hP hQ hdet

theorem half_margin_of_signs {a c t:ℝ} (ht:0 ≤ t) (htT:t ≤ seedT)
    (hP:0<halfP a t) (hQ:0<halfQ c t)
    (hdet:0<(halfP a t)^2-(1-t^2)*(halfQ c t)^2) :
    0<(1/2:ℝ)*(J/H)*(1-t^2)-(44/(1-(1/2:ℝ))-32)*(t^2*(seedV t)^2)-
      a*t*seedV t+(29*(1-t^2)+(radicalB*t*seedV t+c)*Real.sqrt (1-t^2))*(-(seedV t*seedSlope t)) := by
  rw [half_residual_identity]
  exact VariableAlpha24.sqrt_residual_positive
    (VariableAlpha24.parameterized_z_positive ht htT seedT_range.2) hP hQ hdet

theorem criterion_of_parameter_margin {alpha a c t u Z:ℝ}
    (hti:t∈Icc (0:ℝ) seedT) (heq:u=t^2*(seedV t)^2)
    (hu:u∈Icc (0:ℝ) 1) (hZ:Z∈Icc (0:ℝ) 8)
    (ha:2*Real.sqrt (48*Z/H) ≤ a) (hb:2*Real.sqrt (176*H/J) ≤ radicalB)
    (hc:2*Real.sqrt (13824*Z/J) ≤ c)
    (hm:0<alpha*(J/H)*(1-t^2)-(44/(1-alpha)-32)*(t^2*(seedV t)^2)-
      a*t*seedV t+(29*(1-t^2)+(radicalB*t*seedV t+c)*Real.sqrt (1-t^2))*(-(seedV t*seedSlope t))) :
    (-1/((1-t^2)*(-(seedV t*seedSlope t))))*
      (alpha*J/H*(1-t^2)-(44/(1-alpha)-32)*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J*(1-t^2)) := by
  have hz:=VariableAlpha24.parameterized_z_positive hti.1 hti.2 seedT_range.2
  have hv:=seedV_positive hti
  have hs:=seedSlope_positive hti
  have hup:-(seedV t*seedSlope t)<0 := neg_lt_zero.mpr (mul_pos hv hs)
  have hsu:Real.sqrt u=t*seedV t := by
    rw [heq,Real.sqrt_mul (sq_nonneg t),Real.sqrt_sq hti.1,Real.sqrt_sq hv.le]
  apply quartic_creation_criterion_of_inverse_margin hz H_positive J_positive hup hu.1 hZ.1 ha hb hc
  rw [hsu,heq]
  simpa only [mul_assoc] using hm

theorem seedUp_negative {u:ℝ} (hu:u∈Icc (0:ℝ) 1) :
    -(seedV (seedParameter u)*seedSlope (seedParameter u))<0 :=
  neg_lt_zero.mpr (mul_pos (seedV_positive (seedParameter_range hu))
    (seedSlope_positive (seedParameter_range hu)))

theorem seedQ_identity {u:ℝ} (hu:u∈Icc (0:ℝ) 1) :
    -deriv seedPhi u/seedPhi u=
    -1/(seedPhi u*(-(seedV (seedParameter u)*seedSlope (seedParameter u)))) := by
  rw [(hasDerivAt_seedPhi hu).deriv]
  ring

end KLSBelow25.QuarticCreation200000
#print axioms KLSBelow25.QuarticCreation200000.criterion_of_parameter_margin
