import Mathlib

/-! Correct orbit-normalized two-step obstruction. The budget comparison is
C<p*V0(p), including the actual initial orbit mass p. The V functions may be
infinite true-cap Bellman values. This is a scalar method restriction, not a
lower bound for the optimal universal KLS constant. -/
noncomputable section
namespace KLSConstantImprovement.TrueCapTwoStageOrbitObstruction
set_option maxHeartbeats 3000000

theorem second_ratio_surplus
    (A C w h p : ℝ) (V0 V1 V2 : ℝ → ℝ)
    (hA : 0 < A) (hw : 0 ≤ w) (hh : 0 < h) (hhA : h ≤ A)
    (hp : 1 ≤ p)
    (hstep0 : ∀ s,1 ≤ s → p-A/p ≤ s → s ≤ p →
      V0 p ≤ p-s+s*V1 s)
    (hstep1 : ∀ r,1 ≤ r → r ≤ p → ∀ s,1 ≤ s →
      r-A/r ≤ s → s ≤ r → V1 r ≤ w*(r-s)+s*V2 s)
    (hboundary : V2 1=0)
    (hbase : A+w*h ≤ C) (hbudget : C < p*V0 p) :
    h < p*(max 1 (p-A/p))*(max 1 (p-A/p)-1) := by
  let s := max 1 (p-A/p)
  have hp0 : 0 < p := by linarith
  have hs1 : 1 ≤ s := le_max_left _ _
  have hs0 : 0 < s := by linarith
  have hdiv0 : 0 ≤ A/p := by positivity
  have hsp : s ≤ p := max_le hp (by linarith)
  have hslower : p-A/p ≤ s := le_max_right _ _
  have hdrop : p*(p-s) ≤ A := by
    have hd : p-s ≤ A/p := by linarith
    have he := (le_div_iff₀ hp0).mp hd
    nlinarith
  by_contra hfail
  have hpsprod : p*(s*(s-1)) ≤ h := by
    have he := le_of_not_gt hfail
    nlinarith
  have hsprod0 : 0 ≤ s*(s-1) := mul_nonneg hs0.le (by linarith)
  have hweighted : s*(s-1) ≤ p*(s*(s-1)) := by
    have he := mul_le_mul_of_nonneg_right hp hsprod0
    simpa only [one_mul] using he
  have hsprod : s*(s-1) ≤ A := (hweighted.trans hpsprod).trans hhA
  have hfrac : s-1 ≤ A/s := (le_div_iff₀ hs0).mpr (by nlinarith)
  have hslow : s-A/s ≤ 1 := by linarith
  have hV1 : V1 s ≤ w*(s-1) := by
    have he := hstep1 s hs1 hsp 1 (le_refl _) hslow hs1
    simpa only [hboundary,mul_zero,add_zero] using he
  have hfinal : p*V0 p ≤ C := by
    calc
      p*V0 p ≤ p*(p-s+s*V1 s) :=
        mul_le_mul_of_nonneg_left (hstep0 s hs1 hslower hsp) hp0.le
      _ ≤ p*(p-s+s*(w*(s-1))) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (le_refl (p-s)) (mul_le_mul_of_nonneg_left hV1 hs0.le)) hp0.le
      _ = p*(p-s)+w*(p*(s*(s-1))) := by ring
      _ ≤ A+w*h := add_le_add hdrop (mul_le_mul_of_nonneg_left hpsprod hw)
      _ ≤ C := hbase
  linarith

theorem rational_endpoint_floor
    (K p : ℝ) (hK : (14571/1250 : ℝ) < K) (hp : 1 ≤ p)
    (hnecessary : (802604693/2000000 : ℝ)/(36*K^3) <
      p*(max 1 (p-(2/K^2)/p))*(max 1 (p-(2/K^2)/p)-1)) :
    (129/10 : ℝ) < 1+K*p := by
  have hK0 : 0 < K := by linarith
  have hp0 : 0 < p := by linarith
  have hh : 0 < (802604693/2000000 : ℝ)/(36*K^3) := by positivity
  have hf : 1 < p-(2/K^2)/p := by
    by_contra hfail
    rw [max_eq_left (le_of_not_gt hfail)] at hnecessary
    nlinarith
  rw [max_eq_right hf.le] at hnecessary
  let x := K*p
  have hxK : K ≤ x := by dsimp only [x];nlinarith
  have hx0 : 0 < x := hK0.trans_le hxK
  have hscaled := mul_lt_mul_of_pos_right hnecessary
    (by positivity : 0 < K^3*x)
  have hleft : ((802604693/2000000 : ℝ)/(36*K^3))*(K^3*x)=
      (802604693/2000000 : ℝ)*x/36 := by
    field_simp [ne_of_gt hK0] <;> ring
  have hright : (p*(p-(2/K^2)/p)*(p-(2/K^2)/p-1))*(K^3*x)=
      (x^2-2)*(x^2-K*x-2) := by
    dsimp only [x]
    field_simp [ne_of_gt hK0,ne_of_gt hp0]
    ring
  rw [hleft,hright] at hscaled
  by_contra hfail
  have hxhi : x ≤ (119/10 : ℝ) := by dsimp only [x];linarith
  have hxlo : (14571/1250 : ℝ) ≤ x := hK.le.trans hxK
  have hP0 : 0 ≤ x^2-2 := by nlinarith
  have hQ0 : 0 ≤ x^2-K*x-2 := by
    by_contra hbad
    have he := mul_nonpos_of_nonneg_of_nonpos hP0 (le_of_not_ge hbad)
    nlinarith
  have hPmax : x^2-2 ≤ (119/10 : ℝ)^2-2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxhi) (by linarith : 0 ≤ (119/10 : ℝ)+x)]
  have hKx := mul_le_mul_of_nonneg_right hK.le hx0.le
  have hQmax : x^2-K*x-2 ≤ (119/10 : ℝ)^2-(14571/1250 : ℝ)*(119/10 : ℝ)-2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxhi)
      (by linarith : 0 ≤ (119/10 : ℝ)+x-(14571/1250 : ℝ))]
  have hprod := mul_le_mul hPmax hQmax hQ0
    (by norm_num : 0 ≤ (119/10 : ℝ)^2-2)
  nlinarith

theorem true_cap_family_endpoint_gt_129
    (K C w p : ℝ) (V0 V1 V2 : ℝ → ℝ)
    (hKfloor : 6+4*Real.sqrt 2 ≤ K) (hw : 0 ≤ w) (hp : 1 ≤ p)
    (hstep0 : ∀ s,1 ≤ s → p-(2/K^2)/p ≤ s → s ≤ p →
      V0 p ≤ p-s+s*V1 s)
    (hstep1 : ∀ r,1 ≤ r → r ≤ p → ∀ s,1 ≤ s →
      r-(2/K^2)/r ≤ s → s ≤ r → V1 r ≤ w*(r-s)+s*V2 s)
    (hboundary : V2 1=0)
    (hbase : 2/K^2+w*((802604693/2000000 : ℝ)/(36*K^3)) ≤ C)
    (hbudget : C < p*V0 p) :
    (129/10 : ℝ) < 1+K*p := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hslo : (7071/5000 : ℝ) < Real.sqrt 2 := by nlinarith
  have hklo : (14571/1250 : ℝ) < K := by nlinarith
  have hK : 0 < K := by linarith
  have hraw : (802604693/2000000 : ℝ) ≤ 72*K := by nlinarith
  have hhA : (802604693/2000000 : ℝ)/(36*K^3) ≤ 2/K^2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 36*K^3) (sq_pos_of_pos hK)).mpr
    nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hraw)]
  have hnecessary := second_ratio_surplus (2/K^2) C w
    ((802604693/2000000 : ℝ)/(36*K^3)) p V0 V1 V2
    (by positivity) hw (by positivity) hhA hp hstep0 hstep1 hboundary hbase hbudget
  exact rational_endpoint_floor K p hklo hp hnecessary

end KLSConstantImprovement.TrueCapTwoStageOrbitObstruction
#print axioms KLSConstantImprovement.TrueCapTwoStageOrbitObstruction.second_ratio_surplus
#print axioms KLSConstantImprovement.TrueCapTwoStageOrbitObstruction.rational_endpoint_floor
#print axioms KLSConstantImprovement.TrueCapTwoStageOrbitObstruction.true_cap_family_endpoint_gt_129
