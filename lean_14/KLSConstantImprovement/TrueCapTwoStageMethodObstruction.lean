import KLSConstantImprovement.TwoStageMethodObstruction

/-! Two-step obstruction for the true quadratic-cap action interval.
The V functions may be the infinite Bellman values; affine/chord potentials
are not required. These are scalar method restrictions, not universal KLS
lower bounds. The leading K floor is an explicit interface hypothesis. -/
noncomputable section
namespace KLSConstantImprovement.TrueCapTwoStageMethodObstruction
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
    (hbase : A+w*h ≤ C) (hbudget : C < V0 p) :
    h < (max 1 (p-A/p))*(max 1 (p-A/p)-1) := by
  let s := max 1 (p-A/p)
  have hp0 : 0 < p := by linarith
  have hs1 : 1 ≤ s := le_max_left _ _
  have hs0 : 0 < s := by linarith
  have hdiv0 : 0 ≤ A/p := by positivity
  have hsp : s ≤ p := max_le hp (by linarith)
  have hslower : p-A/p ≤ s := le_max_right _ _
  have hdiv : A/p ≤ A := (div_le_iff₀ hp0).mpr (by nlinarith)
  have hdrop : p-s ≤ A := by linarith
  by_contra hfail
  have hsprod : s*(s-1) ≤ h := le_of_not_gt hfail
  have hfrac : s-1 ≤ A/s :=
    (le_div_iff₀ hs0).mpr (by nlinarith [hsprod.trans hhA])
  have hslow : s-A/s ≤ 1 := by linarith
  have hV1 : V1 s ≤ w*(s-1) := by
    have he := hstep1 s hs1 hsp 1 (le_refl _) hslow hs1
    simpa only [hboundary,mul_zero,add_zero] using he
  have hfinal : V0 p ≤ C := by
    calc
      V0 p ≤ p-s+s*V1 s := hstep0 s hs1 hslower hsp
      _ ≤ p-s+s*(w*(s-1)) := add_le_add (le_refl (p-s)) (mul_le_mul_of_nonneg_left hV1 hs0.le)
      _ = p-s+w*(s*(s-1)) := by ring
      _ ≤ A+w*h := add_le_add hdrop (mul_le_mul_of_nonneg_left hsprod hw)
      _ ≤ C := hbase
  linarith

theorem p_quadratic_surplus
    (A C w h p : ℝ) (V0 V1 V2 : ℝ → ℝ)
    (hA : 0 < A) (hw : 0 ≤ w) (hh : 0 < h) (hhA : h ≤ A)
    (hp : 1 ≤ p)
    (hstep0 : ∀ s,1 ≤ s → p-A/p ≤ s → s ≤ p →
      V0 p ≤ p-s+s*V1 s)
    (hstep1 : ∀ r,1 ≤ r → r ≤ p → ∀ s,1 ≤ s →
      r-A/r ≤ s → s ≤ r → V1 r ≤ w*(r-s)+s*V2 s)
    (hboundary : V2 1=0)
    (hbase : A+w*h ≤ C) (hbudget : C < V0 p) :
    h+A-A^2 < p*(p-1) := by
  have hs := second_ratio_surplus A C w h p V0 V1 V2 hA hw hh hhA hp hstep0 hstep1 hboundary hbase hbudget
  have hf : 1 < p-A/p := by
    by_contra hfail
    rw [max_eq_left (le_of_not_gt hfail)] at hs
    nlinarith
  rw [max_eq_right hf.le] at hs
  have hp0 : 0 < p := by linarith
  have hi : 0 ≤ 1/p := by positivity
  have hi1 : 1/p ≤ 1 := (div_le_one hp0).mpr hp
  have hi2 : (1/p)^2 ≤ 1 := by nlinarith
  have he : (p-A/p)*(p-A/p-1)=p*(p-1)-2*A+A*(1/p)+A^2*(1/p)^2 := by
    field_simp [ne_of_gt hp0]
    ring
  rw [he] at hs
  have ha1 := mul_le_mul_of_nonneg_left hi1 hA.le
  have ha2 := mul_le_mul_of_nonneg_left hi2 (sq_nonneg A)
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
    (hbudget : C < V0 p) :
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
  have hnecessary := p_quadratic_surplus (2/K^2) C w
    ((802604693/2000000 : ℝ)/(36*K^3)) p V0 V1 V2
    (by positivity) hw (by positivity) hhA hp hstep0 hstep1 hboundary hbase hbudget
  exact TwoStageMethodObstruction.rational_endpoint_floor K p hklo hp hnecessary

end KLSConstantImprovement.TrueCapTwoStageMethodObstruction
#print axioms KLSConstantImprovement.TrueCapTwoStageMethodObstruction.second_ratio_surplus
#print axioms KLSConstantImprovement.TrueCapTwoStageMethodObstruction.p_quadratic_surplus
#print axioms KLSConstantImprovement.TrueCapTwoStageMethodObstruction.true_cap_family_endpoint_gt_129
