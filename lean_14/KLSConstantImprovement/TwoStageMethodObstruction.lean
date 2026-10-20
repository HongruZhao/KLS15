import KLSConstantImprovement.QuadraticCapBellmanCertificates
import KLSConstantImprovement.ConstantTailFamilyLowerBound

/-! Necessary scalar conditions for the present generator/Bellman method.
These are not lower bounds for the optimal universal KLS constant. -/
noncomputable section
namespace KLSConstantImprovement.TwoStageMethodObstruction
open PositiveFiniteHeadBellman QuadraticCapBellmanCertificates
set_option maxHeartbeats 3000000

theorem second_ratio_surplus
    (A R C w h p : ℝ) (L0 L1 L2 : Affine)
    (hA : 0 < A) (hR : 0 < R) (hh : 0 < h) (hhA : h ≤ A)
    (hp : 1 ≤ p) (hpR : p ≤ R)
    (h0 : StageCertificate 1 R (capChord A R) L0 L1)
    (h1 : StageCertificate w R (capChord A R) L1 L2)
    (hbase : A+w*h ≤ C) (hbudget : C < L0.eval p) :
    h < (max 1 (capChord A R p))*(max 1 (capChord A R p)-1) := by
  let s := max 1 (capChord A R p)
  have hs1 : 1 ≤ s := le_max_left _ _
  have hs0 : 0 < s := by linarith
  have hsp : s ≤ p := max_le hp (capChord_le_self hA.le hR hpR)
  have hsR : s ≤ R := hsp.trans hpR
  have hslower : capChord A R p ≤ s := le_max_right _ _
  have hdrop : p-s ≤ A := by
    have hn : 0 ≤ (A/R)*(p-1) := mul_nonneg (div_nonneg hA.le hR.le) (by linarith)
    have he : p-capChord A R p=A-(A/R)*(p-1) := by unfold capChord;ring
    linarith
  by_contra hfail
  have hsprod : s*(s-1) ≤ h := le_of_not_gt hfail
  have hfrac : s-1 ≤ A/s :=
    (le_div_iff₀ hs0).mpr (by nlinarith [hsprod.trans hhA])
  have hslow : capChord A R s ≤ 1 :=
    (capChord_le_quadratic_transition hA.le hR hs1 hsR).trans (by linarith)
  have hz2 : L2.positive 1=0 :=
    L2.positive_zero h1.next_slope_nonneg h1.next_at_one (le_refl _)
  have hL1 : L1.eval s ≤ w*(s-1) := by
    have he := h1.stage s hs1 hsR 1 (le_refl _) hslow hs1
    simpa only [hz2,mul_zero,add_zero] using he
  have hL1pos : L1.positive s ≤ w*(s-1) :=
    max_le (mul_nonneg h1.weight_nonneg (by linarith)) hL1
  have he0 := h0.stage p hp hpR s hs1 hslower hsp
  have hfinal : L0.eval p ≤ C := by
    calc
      L0.eval p ≤ p-s+s*L1.positive s := by simpa only [one_mul] using he0
      _ ≤ p-s+s*(w*(s-1)) := add_le_add (le_refl (p-s)) (mul_le_mul_of_nonneg_left hL1pos hs0.le)
      _ = p-s+w*(s*(s-1)) := by ring
      _ ≤ A+w*h := add_le_add hdrop (mul_le_mul_of_nonneg_left hsprod h1.weight_nonneg)
      _ ≤ C := hbase
  linarith

theorem p_quadratic_surplus
    (A R C w h p : ℝ) (L0 L1 L2 : Affine)
    (hA : 0 < A) (hR : 0 < R) (hh : 0 < h) (hhA : h ≤ A)
    (hp : 1 ≤ p) (hpR : p ≤ R)
    (h0 : StageCertificate 1 R (capChord A R) L0 L1)
    (h1 : StageCertificate w R (capChord A R) L1 L2)
    (hbase : A+w*h ≤ C) (hbudget : C < L0.eval p) :
    h+A-A^2 < p*(p-1) := by
  have hs := second_ratio_surplus A R C w h p L0 L1 L2 hA hR hh hhA hp hpR h0 h1 hbase hbudget
  have hf : 1 < capChord A R p := by
    by_contra hfail
    rw [max_eq_left (le_of_not_gt hfail)] at hs
    nlinarith
  rw [max_eq_right hf.le] at hs
  have hp0 : 0 < p := by linarith
  let t := p-A/p
  have hft : capChord A R p ≤ t := capChord_le_quadratic_transition hA.le hR hp hpR
  have ht1 : 1 < t := hf.trans_le hft
  have hmon : capChord A R p*(capChord A R p-1) ≤ t*(t-1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hft) (by linarith : 0 ≤ t+capChord A R p-1)]
  have hi : 0 ≤ 1/p := by positivity
  have hi1 : 1/p ≤ 1 := (div_le_one hp0).mpr hp
  have hi2 : (1/p)^2 ≤ 1 := by nlinarith
  have he : t*(t-1)=p*(p-1)-2*A+A*(1/p)+A^2*(1/p)^2 := by
    dsimp only [t]
    field_simp [ne_of_gt hp0]
    ring
  have hupper : t*(t-1) ≤ p*(p-1)-A+A^2 := by
    rw [he]
    have ha1 := mul_le_mul_of_nonneg_left hi1 hA.le
    have ha2 := mul_le_mul_of_nonneg_left hi2 (sq_nonneg A)
    nlinarith
  linarith

theorem rational_endpoint_floor
    (K p : ℝ) (hK : (14571/1250 : ℝ) < K) (hp : 1 ≤ p)
    (hnecessary :
      (802604693/2000000 : ℝ)/(36*K^3)+2/K^2-(2/K^2)^2 < p*(p-1)) :
    (129/10 : ℝ) < 1+K*p := by
  have hK0 : 0 < K := by linarith
  let x := K*p
  have hxK : K ≤ x := by dsimp only [x];nlinarith
  have hx0 : 0 ≤ x := hK0.le.trans hxK
  by_contra hfail
  have hxhi : x ≤ (119/10 : ℝ) := by dsimp only [x];linarith
  have hKhi : K ≤ (119/10 : ℝ) := hxK.trans hxhi
  have hKsq : (14571/1250 : ℝ)^2 < K^2 := by
    nlinarith [sq_nonneg (K-(14571/1250 : ℝ))]
  have hsmall : 4/K^2 < (3/100 : ℝ) :=
    (div_lt_iff₀ (sq_pos_of_pos hK0)).mpr (by nlinarith)
  have hlarge : (93/100 : ℝ) < (802604693/2000000 : ℝ)/(36*K) :=
    (lt_div_iff₀ (by positivity : 0 < 36*K)).mpr (by nlinarith)
  have hscaled := mul_lt_mul_of_pos_right hnecessary (sq_pos_of_pos hK0)
  have hid :
      ((802604693/2000000 : ℝ)/(36*K^3)+2/K^2-(2/K^2)^2)*K^2 =
        (802604693/2000000 : ℝ)/(36*K)+2-4/K^2 := by
    field_simp [ne_of_gt hK0]
    ring
  have hright : p*(p-1)*K^2=x^2-K*x := by dsimp only [x];ring
  rw [hid,hright] at hscaled
  have hcross := mul_le_mul_of_nonneg_right hK.le hx0
  have hpoly : x^2-(14571/1250 : ℝ)*x ≤
      (119/10 : ℝ)^2-(14571/1250 : ℝ)*(119/10 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxhi)
      (by linarith : 0 ≤ (119/10 : ℝ)+x-(14571/1250 : ℝ))]
  nlinarith

theorem current_constant_tail_family_endpoint_gt_129
    (K C y alpha R w p : ℝ) (L0 L1 L2 : Affine)
    (hK : 0 < K) (hC : 0 < C) (hy : 0 < y)
    (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (hq : 0 ≤ K*alpha-4/(1-alpha)+2-K*C/y)
    (hR : 0 < R) (hp : 1 ≤ p) (hpR : p ≤ R)
    (h0 : StageCertificate 1 R (capChord (2/K^2) R) L0 L1)
    (h1 : StageCertificate w R (capChord (2/K^2) R) L1 L2)
    (hbase : 2/K^2+w*((802604693/2000000 : ℝ)/(36*K^3)) ≤ C)
    (hbudget : C < L0.eval p) :
    (129/10 : ℝ) < 1+K*p := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hslo : (7071/5000 : ℝ) < Real.sqrt 2 := by nlinarith
  have hkfloor := ConstantTailFamilyLowerBound.K_lower_of_tail_coefficient K C y alpha hK hC hy ha ha1 hq
  have hklo : (14571/1250 : ℝ) < K := by nlinarith
  have hraw : (802604693/2000000 : ℝ) ≤ 72*K := by nlinarith
  have hhA : (802604693/2000000 : ℝ)/(36*K^3) ≤ 2/K^2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 36*K^3) (sq_pos_of_pos hK)).mpr
    nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hraw)]
  have hnecessary := p_quadratic_surplus (2/K^2) R C w
    ((802604693/2000000 : ℝ)/(36*K^3)) p L0 L1 L2
    (by positivity) hR (by positivity) hhA hp hpR h0 h1 hbase hbudget
  exact rational_endpoint_floor K p hklo hp hnecessary

end KLSConstantImprovement.TwoStageMethodObstruction
#print axioms KLSConstantImprovement.TwoStageMethodObstruction.second_ratio_surplus
#print axioms KLSConstantImprovement.TwoStageMethodObstruction.p_quadratic_surplus
#print axioms KLSConstantImprovement.TwoStageMethodObstruction.rational_endpoint_floor
#print axioms KLSConstantImprovement.TwoStageMethodObstruction.current_constant_tail_family_endpoint_gt_129
