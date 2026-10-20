import KLSConstantImprovement.AffineSameTestCreationSeed238452Inverse
import VariableAlpha24ScalarInstances
import SquareRootResidualAlgebra
import KLSConstantImprovement.ActualSameTestAffineTerminal
noncomputable section
open Set
namespace KLSBelow25.AffineSameTestCreationSeed238452
open KLSBelow25 KLS.DeterministicBridgeNext VariableAlpha24
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def seedAlphaAt (t : ℝ) : ℝ := 1-seedC*t*seedV t/Real.sqrt (1-t^2)

theorem seed_alpha_ge_third {t:ℝ} (ht:0<t) (htT:t ≤ seedT) : (1/3:ℝ) ≤ seedAlphaAt t := by
  have hi:t∈Icc 0 seedT := ⟨ht.le,htT⟩
  have hz:0<1-t^2 := parameterized_z_positive ht.le htT seedT_range.2
  have hs:0<Real.sqrt (1-t^2) := Real.sqrt_pos.mpr hz
  have hs2 := Real.sq_sqrt hz.le
  have hp := seedAlphaPoly_positive hi
  have hv := seedV_positive hi
  have hc := seedC_positive
  have hx:0 ≤ seedC*t*seedV t := by positivity
  have hsmall:3*(seedC*t*seedV t) ≤ 2*Real.sqrt (1-t^2) := by
    dsimp [seedAlphaPoly] at hp
    dsimp [seedC] at *
    nlinarith [sq_nonneg (3*(seedC*t*seedV t)+2*Real.sqrt (1-t^2))]
  have hd:seedC*t*seedV t/Real.sqrt (1-t^2) ≤ (2/3:ℝ) := (div_le_iff₀ hs).mpr (by linarith)
  dsimp [seedAlphaAt]
  linarith

theorem seed_alpha_mem_unit {t:ℝ} (ht:0<t) (htT:t ≤ seedT) : seedAlphaAt t∈Ioo (0:ℝ) 1 := by
  constructor
  · linarith [seed_alpha_ge_third ht htT]
  · dsimp [seedAlphaAt]
    have hp:0<seedC*t*seedV t/Real.sqrt (1-t^2) := div_pos
      (mul_pos (mul_pos seedC_positive ht) (seedV_positive ⟨ht.le,htT⟩))
      (Real.sqrt_pos.mpr (parameterized_z_positive ht.le htT seedT_range.2))
    linarith

def seedAlpha (u : ℝ) : ℝ := if u=0 then alphaZero else seedAlphaAt (seedParameter u)
theorem seedAlpha_unit {u : ℝ} (hu : u∈Icc (0:ℝ) 1) : seedAlpha u∈Ioo (0:ℝ) 1 := by
  by_cases hz : u=0
  · simpa [seedAlpha,hz] using alphaZero_range
  · simpa [seedAlpha,hz] using seed_alpha_mem_unit
      (seedParameter_positive hu (lt_of_le_of_ne hu.1 (Ne.symm hz))) (seedParameter_range hu).2

def seedShape : ScalarVariableBarrierShape where
  phi := seedPhi
  alpha := seedAlpha
  continuous := seedInverseBarrier.continuousOn_phi
  positive := fun _ hu => seedInverseBarrier.phi_positive hu
  antitone := seedInverseBarrier.strictAntiOn_phi.antitoneOn
  concave := seedInverseBarrier.concaveOn_phi
  hasDeriv := fun _ hu => by
    rw [(hasDerivAt_seedPhi hu).deriv]
    exact hasDerivAt_seedPhi hu
  derivative_negative := fun _ hu => seedInverseBarrier.deriv_phi_negative hu
  zero := seedPhi_zero
  alpha_unit := fun _ hu => seedAlpha_unit hu

theorem seedUp_negative {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    -(seedV (seedParameter u)*seedSlope (seedParameter u))<0 := by
  exact neg_lt_zero.mpr (mul_pos (seedV_positive (seedParameter_range hu))
    (seedSlope_positive (seedParameter_range hu)))
theorem seedQ_identity {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    -deriv seedPhi u/seedPhi u =
      -1/(seedPhi u*(-(seedV (seedParameter u)*seedSlope (seedParameter u)))) :=
  inverse_q_identity (hasDerivAt_seedPhi hu).deriv

theorem seedQ_zero : -deriv seedPhi 0/seedPhi 0=((seedV 0)^2)⁻¹ := by
  rw [(hasDerivAt_seedPhi (by norm_num : (0:ℝ)∈Icc 0 1)).deriv]
  norm_num [seedParameter,seedPhi_zero,RadicalBarrier.parameter,seedV,seedSlope,seedVp]


theorem seedAlpha_ge_third {u:ℝ} (hu:u∈Icc (0:ℝ) 1) : (1/3:ℝ) ≤ seedAlpha u := by
  by_cases hz:u=0
  · simpa [seedAlpha,hz] using alphaZero_ge_third
  · simpa [seedAlpha,hz] using seed_alpha_ge_third
      (seedParameter_positive hu (lt_of_le_of_ne hu.1 (Ne.symm hz))) (seedParameter_range hu).2

theorem sqrt_residual_positive {t : ℝ} (ht0 : 0<t) (ht : t∈Icc (0 : ℝ) seedT) :
    0<seedP t-Real.sqrt (1-t^2)*seedNegQ t := by
  exact VariableAlpha24.sqrt_residual_positive (parameterized_z_positive ht.1 ht.2 seedT_range.2)
    (seedP_positive ht) (seedNegQ_positive ht0 ht.2) (seedDet_positive ht)

theorem differential_residual_identity {t : ℝ} (ht : 0<t) (htT : t ≤ seedT) :
    seedAlphaAt t*(9*B/2)*(1-t^2)-
      (64/(3*(1-seedAlphaAt t))-17)*(t^2*(seedV t)^2)+
      ((16+seedExtraAt t*t^2*(seedV t)^2)*(1-t^2)+seedRAt t*t*seedV t*Real.sqrt (1-t^2))*(-(seedV t*seedSlope t))=
      seedP t-Real.sqrt (1-t^2)*seedNegQ t := by
  have hi : t∈Icc 0 seedT := ⟨ht.le,htT⟩
  have he := variable_alpha_residual_identity
    (z:=1-t^2) (c:=seedC) (t:=t) (v:=seedV t) (s:=seedSlope t)
    (p:=9*B/2) (C:=64/3) (D:=17) (R:=seedRAt t*t*seedV t) (r0:=0) (a:=16+seedExtraAt t*t^2*(seedV t)^2)
    (parameterized_z_positive ht.le htT seedT_range.2)
    (ne_of_gt seedC_positive) (ne_of_gt ht) (ne_of_gt (seedV_positive hi))
  rw [seedNegQ_formula,seedP_formula]
  convert he using 1 <;> dsimp [seedAlphaAt,B,seedC] <;> ring

theorem differential_residual_positive {t : ℝ} (ht : 0<t) (htT : t ≤ seedT) :
    0<seedAlphaAt t*(9*B/2)*(1-t^2)-
      (64/(3*(1-seedAlphaAt t))-17)*(t^2*(seedV t)^2)+
      ((16+seedExtraAt t*t^2*(seedV t)^2)*(1-t^2)+seedRAt t*t*seedV t*Real.sqrt (1-t^2))*(-(seedV t*seedSlope t)) := by
  rw [differential_residual_identity ht htT]
  exact sqrt_residual_positive ht ⟨ht.le,htT⟩

theorem centered_seed_margin (u : ℝ) (hu : u∈Icc (0 : ℝ) 1) :
    (-deriv seedPhi u/seedPhi u)*(seedAlpha u*(9*B/2)*seedPhi u-
      (64/(3*(1-seedAlpha u))-17)*u)>16+seedExtraAt (seedParameter u)*u+seedRAt (seedParameter u)*Real.sqrt u/Real.sqrt (seedPhi u) := by
  by_cases hz : u=0
  · subst u
    rw [seedQ_zero,seedPhi_zero]
    simp only [seedAlpha,ite_true,Real.sqrt_zero,mul_zero,mul_one,sub_zero,zero_div,add_zero]
    have hv := seedV_positive (by norm_num [seedT] : (0:ℝ)∈Icc 0 seedT)
    have hs : 0<(seedV 0)^2 := sq_pos_of_pos hv
    have hm := seed_zero_strict_margin
    norm_num only [B] at ⊢
    change ((seedV 0)^2)⁻¹*(alphaZero*(536517/5000))>16
    apply (lt_inv_mul_iff₀ hs).mpr
    nlinarith [hm]
  · have hp : 0<u := lt_of_le_of_ne hu.1 (Ne.symm hz)
    have ht := seedParameter_positive hu hp
    have htr := seedParameter_range hu
    have hr := differential_residual_positive ht htr.2
    have hzpos : 0<seedPhi u := seedInverseBarrier.phi_positive hu
    have hUp := seedUp_negative hu
    have hsu : Real.sqrt u=seedParameter u*seedV (seedParameter u) := by
      have hh := seedPhi_u_identity hu
      have hv:=seedV_positive htr
      have hs : (seedParameter u*seedV (seedParameter u))^2=u := by nlinarith [hh]
      apply (Real.sqrt_eq_iff_mul_self_eq hu.1 (mul_nonneg htr.1 hv.le)).mpr
      nlinarith [hs]
    rw [←seedPhi_z_identity hu,←seedPhi_u_identity hu] at hr
    have hm : 0<(-deriv seedPhi u/seedPhi u)*
        (seedAlphaAt (seedParameter u)*(9*B/2)*seedPhi u-
          (64/(3*(1-seedAlphaAt (seedParameter u)))-17)*u)-(16+seedExtraAt (seedParameter u)*u)-
        (seedRAt (seedParameter u)*seedParameter u*seedV (seedParameter u))/Real.sqrt (seedPhi u) := by
      apply inverse_margin_of_differential_residual hzpos hUp (seedQ_identity hu)
      simpa only [mul_assoc, ←seedPhi_u_identity hu] using hr
    rw [hsu]
    simpa only [seedAlpha,hz,ite_false,mul_assoc] using (by linarith :
      (-deriv seedPhi u/seedPhi u)*(seedAlphaAt (seedParameter u)*(9*B/2)*seedPhi u-
        (64/(3*(1-seedAlphaAt (seedParameter u)))-17)*u)>
          16+seedExtraAt (seedParameter u)*u+(seedRAt (seedParameter u)*seedParameter u*seedV (seedParameter u))/Real.sqrt (seedPhi u))


open KLSConstantImprovement.ActualSameTestAffineTerminal
open KLSConstantImprovement.ActualSameTestAffineCreation

theorem seedSupportC_actual : seedSupportC=affineEffectiveC := rfl

theorem same_test_new_radical_majorant {C H R z u : ℝ}
    (hC : 4 < C) (hH : 0 < H) (hz : 0 < z) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (h72 : H*z ≤ 72*C) (hR : 0 ≤ R)
    (hdom : 32*(C-2*u)*(72*C-H*z) ≤ H*C^2*R^2) :
    (8*u+Real.sqrt ((4*C-8*u)*8*u*(72*C/(H*z)-1)))/C ≤
      8*u/C+R*Real.sqrt u/Real.sqrt z := by
  have hCp : 0 < C := by linarith
  have hM : 0 < H*z := mul_pos hH hz
  have htail : 0 ≤ 72*C/(H*z)-1 := by
    apply sub_nonneg.mpr
    exact (le_div_iff₀ hM).mpr (by simpa only [one_mul] using h72)
  let E := (4*C-8*u)*8*u*(72*C/(H*z)-1)
  have hE : 0 ≤ E := mul_nonneg
    (mul_nonneg (mul_nonneg (by linarith : 0 ≤ 4*C-8*u)
      (by norm_num : (0 : ℝ) ≤ 8)) hu) htail
  have hpaid : 0 ≤ u*(H*C^2*R^2-32*(C-2*u)*(72*C-H*z)) :=
    mul_nonneg hu (sub_nonneg.mpr hdom)
  have he : (R^2*u*C^2-E*z)*H = u*(H*C^2*R^2-32*(C-2*u)*(72*C-H*z)) := by
    dsimp [E]
    field_simp [hH.ne',hz.ne']
    ring
  have hpaid' : 0 ≤ (R^2*u*C^2-E*z)*H := by
    rw [he]
    exact hpaid
  have hbound : E*z ≤ R^2*u*C^2 := by
    have hh : 0 ≤ R^2*u*C^2-E*z := (mul_le_mul_iff_of_pos_right hH).mp (by simpa only [zero_mul] using hpaid')
    exact sub_nonneg.mp hh
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz
  have hs : (R*Real.sqrt u/Real.sqrt z*C)^2*z=R^2*u*C^2 := by
    rw [mul_pow,div_pow,mul_pow,Real.sq_sqrt hu,Real.sq_sqrt hz.le]
    field_simp [hz.ne'] <;> ring
  have htarget : 0 ≤ R*Real.sqrt u/Real.sqrt z*C := by positivity
  have hr : Real.sqrt E ≤ R*Real.sqrt u/Real.sqrt z*C := by
    have hb : E ≤ (R*Real.sqrt u/Real.sqrt z*C)^2 := (mul_le_mul_iff_of_pos_right hz).mp (hbound.trans_eq hs.symm)
    nlinarith [Real.sq_sqrt hE,Real.sqrt_nonneg E,sq_nonneg (Real.sqrt E+R*Real.sqrt u/Real.sqrt z*C)]
  have hb : Real.sqrt E/C ≤ R*Real.sqrt u/Real.sqrt z := (div_le_iff₀ hCp).mpr hr
  dsimp [E] at hb
  convert add_le_add_left hb (8*u/C) using 1 <;> ring

theorem seed_ramp_new_identity (t : ℝ) :
    seedRampNew t*((36*B)*seedSupportC^2)=
      32*(seedSupportC-2*t^2*(seedV t)^2)*(72*seedSupportC-(36*B)*(1-t^2)) := by
  unfold seedRampNew seedCMinusTwoU seedU seedAffineTail
  norm_num [B,seedSupportC]
  ring

theorem same_test_closed_le_new_majorant {t u : ℝ}
    (ht : t ∈ Icc (0:ℝ) seedT) (hu : u ∈ Icc (0:ℝ) 1)
    (heu : u=t^2*(seedV t)^2) :
    2*affineClosedRatio ((36*B)*(1-t^2)) (8*u) ≤
      (8/seedSupportC)*u+seedRNew t*Real.sqrt u/Real.sqrt (1-t^2) := by
  have hH : 0 < 36*B := by positivity [B_positive]
  have hC := seedSupportC_positive
  have hz := parameterized_z_positive ht.1 ht.2 seedT_range.2
  have hm : (36*B)*(1-t^2) ≤ 72*seedSupportC := by
    have ht2 := sq_nonneg t
    norm_num [B,seedSupportC] at *
    nlinarith [ht2]
  have hd : 32*(seedSupportC-2*u)*(72*seedSupportC-(36*B)*(1-t^2)) ≤
      (36*B)*seedSupportC^2*(seedRNew t)^2 := by
    calc
      _ = seedRampNew t*((36*B)*seedSupportC^2) := by
        rw [heu]
        convert (seed_ramp_new_identity t).symm using 1 <;> ring
      _ ≤ (seedRNew t)^2*((36*B)*seedSupportC^2) := mul_le_mul_of_nonneg_right
        (seedRNew_domination t) (mul_nonneg hH.le (sq_nonneg seedSupportC))
      _ = _ := by ring
  have hh := same_test_new_radical_majorant (by norm_num [seedSupportC]) hH hz hu.1 hu.2 hm
    (seedRNew_positive ht).le hd
  unfold affineClosedRatio
  rw [←seedSupportC_actual]
  convert hh using 1 <;> field_simp [hC.ne'] <;> ring

theorem cap_root_coefficient_le_seedR :
    2*Real.sqrt 384/Real.sqrt (36*B) ≤ seedR := by
  have hH : 0 < 36*B := by positivity [B_positive]
  have hsH : 0 < Real.sqrt (36*B) := Real.sqrt_pos.mpr hH
  have hh := seedR_domination
  have hr := seedR_positive
  have hsR : (seedR*Real.sqrt (36*B))^2=seedR^2*(36*B) := by rw [mul_pow,Real.sq_sqrt hH.le]
  have hsL : (2*Real.sqrt 384)^2=(1536:ℝ) := by rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 384)]; norm_num
  have hs : (2*Real.sqrt 384)^2 ≤ (seedR*Real.sqrt (36*B))^2 := by rw [hsL,hsR]; exact hh
  apply (div_le_iff₀ hsH).mpr
  have hp : 0 ≤ seedR*Real.sqrt (36*B) := mul_nonneg hr.le hsH.le
  nlinarith [Real.sqrt_nonneg 384,sq_nonneg (2*Real.sqrt 384+seedR*Real.sqrt (36*B))]

theorem same_test_cap_le_majorant {t u : ℝ} (ht : t ∈ Icc (0:ℝ) seedT) (hu : 0 ≤ u) :
    2*(Real.sqrt (48*(8*u))/Real.sqrt ((36*B)*(1-t^2))) ≤
      seedR*Real.sqrt u/Real.sqrt (1-t^2) := by
  have hH : 0 < 36*B := by positivity [B_positive]
  have hz := parameterized_z_positive ht.1 ht.2 seedT_range.2
  have hsH : 0 < Real.sqrt (36*B) := Real.sqrt_pos.mpr hH
  have hsz : 0 < Real.sqrt (1-t^2) := Real.sqrt_pos.mpr hz
  rw [show 48*(8*u)=384*u by ring,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 384),Real.sqrt_mul hH.le]
  have hb := mul_le_mul_of_nonneg_right cap_root_coefficient_le_seedR
    (div_nonneg (Real.sqrt_nonneg u) hsz.le)
  convert hb using 1 <;> field_simp [hsH.ne',hsz.ne']

theorem same_test_ratio_le_profile_majorant {t u : ℝ}
    (ht : t ∈ Icc (0:ℝ) seedT) (hu : u ∈ Icc (0:ℝ) 1)
    (heu : u=t^2*(seedV t)^2) :
    2*affineCreationRatio ((36*B)*(1-t^2)) (8*u) ≤
      seedExtraAt t*u+seedRAt t*Real.sqrt u/Real.sqrt (1-t^2) := by
  by_cases hc : t ≤ seedCut
  · have hb := mul_le_mul_of_nonneg_left
      (affineCreationRatio_le_closed ((36*B)*(1-t^2)) (8*u)) (by norm_num : (0:ℝ) ≤ 2)
    have hn := same_test_closed_le_new_majorant ht hu heu
    simpa only [seedExtraAt,seedRAt,hc,ite_true] using hb.trans hn
  · have hb := mul_le_mul_of_nonneg_left
      (affineCreationRatio_le_cap ((36*B)*(1-t^2)) (8*u)) (by norm_num : (0:ℝ) ≤ 2)
    have hn := same_test_cap_le_majorant ht hu.1
    simpa only [seedExtraAt,seedRAt,hc,ite_false,zero_mul,zero_add] using hb.trans hn

theorem seed_threshold_lower (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    (360:ℝ) ≤ (36*B)*seedPhi u := by
  have hH : 0 < 36*B := by positivity [B_positive]
  have hm := mul_lt_mul_of_pos_left (seedPhi_range hu).1 hH
  have hnum : (360:ℝ) < (36*B)*(1-seedT^2) := by norm_num [B,seedT]
  exact (hnum.trans hm).le

theorem centered_affine_same_test_seed_margin (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    (-deriv seedPhi u/seedPhi u)*(seedAlpha u*(9*B/2)*seedPhi u-
      (64/(3*(1-seedAlpha u))-17)*u) >
      16+2*affineCreationRatio ((36*B)*seedPhi u) (8*u) := by
  have hm := centered_seed_margin u hu
  have hb := same_test_ratio_le_profile_majorant (seedParameter_range hu) hu (seedPhi_u_identity hu)
  rw [←seedPhi_z_identity hu] at hb
  linarith

end KLSBelow25.AffineSameTestCreationSeed238452
#print axioms KLSBelow25.AffineSameTestCreationSeed238452.seedShape
#print axioms KLSBelow25.AffineSameTestCreationSeed238452.seedAlpha_ge_third
#print axioms KLSBelow25.AffineSameTestCreationSeed238452.same_test_new_radical_majorant
#print axioms KLSBelow25.AffineSameTestCreationSeed238452.same_test_ratio_le_profile_majorant
#print axioms KLSBelow25.AffineSameTestCreationSeed238452.centered_affine_same_test_seed_margin
