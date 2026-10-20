import KLSConstantImprovement.OptimizedJointCreationSeed23849Inverse
import VariableAlpha24ScalarInstances
import SquareRootResidualAlgebra
import KLSConstantImprovement.OptimizedJointCreationTerminal
noncomputable section
open Set
namespace KLSBelow25.OptimizedJointCreationSeed23849
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
      (16*(1-t^2)+seedRAt t*t*seedV t*Real.sqrt (1-t^2))*(-(seedV t*seedSlope t))=
      seedP t-Real.sqrt (1-t^2)*seedNegQ t := by
  have hi : t∈Icc 0 seedT := ⟨ht.le,htT⟩
  have he := variable_alpha_residual_identity
    (z:=1-t^2) (c:=seedC) (t:=t) (v:=seedV t) (s:=seedSlope t)
    (p:=9*B/2) (C:=64/3) (D:=17) (R:=seedRAt t*t*seedV t) (r0:=0) (a:=16)
    (parameterized_z_positive ht.le htT seedT_range.2)
    (ne_of_gt seedC_positive) (ne_of_gt ht) (ne_of_gt (seedV_positive hi))
  rw [seedNegQ_formula]
  convert he using 1 <;> dsimp [seedAlphaAt,seedP,B,seedC] <;> ring

theorem differential_residual_positive {t : ℝ} (ht : 0<t) (htT : t ≤ seedT) :
    0<seedAlphaAt t*(9*B/2)*(1-t^2)-
      (64/(3*(1-seedAlphaAt t))-17)*(t^2*(seedV t)^2)+
      (16*(1-t^2)+seedRAt t*t*seedV t*Real.sqrt (1-t^2))*(-(seedV t*seedSlope t)) := by
  rw [differential_residual_identity ht htT]
  exact sqrt_residual_positive ht ⟨ht.le,htT⟩

theorem centered_seed_margin (u : ℝ) (hu : u∈Icc (0 : ℝ) 1) :
    (-deriv seedPhi u/seedPhi u)*(seedAlpha u*(9*B/2)*seedPhi u-
      (64/(3*(1-seedAlpha u))-17)*u)>16+seedRAt (seedParameter u)*Real.sqrt u/Real.sqrt (seedPhi u) := by
  by_cases hz : u=0
  · subst u
    rw [seedQ_zero,seedPhi_zero]
    simp only [seedAlpha,ite_true,Real.sqrt_zero,mul_zero,mul_one,sub_zero,zero_div,add_zero]
    have hv := seedV_positive (by norm_num [seedT] : (0:ℝ)∈Icc 0 seedT)
    have hs : 0<(seedV 0)^2 := sq_pos_of_pos hv
    have hm := seed_zero_strict_margin
    norm_num only [B] at ⊢
    change ((seedV 0)^2)⁻¹*(alphaZero*(214641/2000))>16
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
          (64/(3*(1-seedAlphaAt (seedParameter u)))-17)*u)-16-
        (seedRAt (seedParameter u)*seedParameter u*seedV (seedParameter u))/Real.sqrt (seedPhi u) := by
      apply inverse_margin_of_differential_residual hzpos hUp (seedQ_identity hu)
      exact hr
    rw [hsu]
    simpa only [seedAlpha,hz,ite_false,mul_assoc] using (by linarith :
      (-deriv seedPhi u/seedPhi u)*(seedAlphaAt (seedParameter u)*(9*B/2)*seedPhi u-
        (64/(3*(1-seedAlphaAt (seedParameter u)))-17)*u)>
          16+(seedRAt (seedParameter u)*seedParameter u*seedV (seedParameter u))/Real.sqrt (seedPhi u))

open KLSConstantImprovement.OptimizedJointCreationTerminal

theorem joint_coefficient_nonneg_parameter (t : ℝ) :
    0 ≤ jointCreationCoefficient ((36*B)*(1-t^2)) := by
  unfold jointCreationCoefficient KLSConstantImprovement.ActualCubicCreationOptimizedSupport.jointConstant
  apply le_min (by norm_num)
  apply div_nonneg _ (by norm_num)
  have hH : 0 < 36*B := by positivity [B_positive]
  have hD : 36*B < (86453779175388/70090297225 : ℝ) := by norm_num [B]
  nlinarith [mul_nonneg hH.le (sq_nonneg t)]

theorem joint_coefficient_sq_envelope (t : ℝ) :
    32*jointCreationCoefficient ((36*B)*(1-t^2)) ≤ (seedRAt t)^2*(36*B) := by
  by_cases h : t ≤ seedSwitch
  · have hc : jointCreationCoefficient ((36*B)*(1-t^2)) ≤ ((86453779175388/70090297225 : ℝ)-(36*B)*(1-t^2))/10 := min_le_right _ _
    have hH : 0 < 36*B := by positivity [B_positive]
    have hb := mul_le_mul_of_nonneg_left (seedRLow_domination t) hH.le
    have hid : (36*B)*seedRamp t =
        (16/5)*((86453779175388/70090297225 : ℝ)-(36*B)*(1-t^2)) := by
      norm_num [seedRamp,jointConstant,B]
      ring
    rw [hid] at hb
    simp only [seedRAt,h,ite_true]
    nlinarith [hc,hb]
  · have hc : jointCreationCoefficient ((36*B)*(1-t^2)) ≤ 48 := min_le_left _ _
    have hb := seedR_domination
    simp only [seedRAt,h,ite_false]
    nlinarith [hc,hb]

theorem joint_root_coefficient_le_envelope (t : ℝ) :
    2*Real.sqrt (8*jointCreationCoefficient ((36*B)*(1-t^2)))/Real.sqrt (36*B) ≤ seedRAt t := by
  have hH : 0 < 36*B := by positivity [B_positive]
  have hsH : 0 < Real.sqrt (36*B) := Real.sqrt_pos.mpr hH
  apply (div_le_iff₀ hsH).mpr
  have hR := seedRAt_positive t
  have hg := joint_coefficient_nonneg_parameter t
  have hp : 0 ≤ seedRAt t*Real.sqrt (36*B) := by positivity
  have hl : (2*Real.sqrt (8*jointCreationCoefficient ((36*B)*(1-t^2))))^2 =
      32*jointCreationCoefficient ((36*B)*(1-t^2)) := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hg)]
    ring
  have hr : (seedRAt t*Real.sqrt (36*B))^2 = (seedRAt t)^2*(36*B) := by
    rw [mul_pow,Real.sq_sqrt hH.le]
  have hc : (2*Real.sqrt (8*jointCreationCoefficient ((36*B)*(1-t^2))))^2 ≤ (seedRAt t*Real.sqrt (36*B))^2 := by
    rw [hl,hr]
    exact joint_coefficient_sq_envelope t
  have hleft : 0 ≤ 2*Real.sqrt (8*jointCreationCoefficient ((36*B)*(1-t^2))) := by positivity
  nlinarith [hc,sq_nonneg (2*Real.sqrt (8*jointCreationCoefficient ((36*B)*(1-t^2)))+
    seedRAt t*Real.sqrt (36*B))]

theorem joint_root_le_envelope {t u : ℝ} (ht : t ∈ Icc (0:ℝ) seedT) (hu : 0 ≤ u) :
    2*Real.sqrt (8*u*jointCreationCoefficient ((36*B)*(1-t^2)))/
      Real.sqrt ((36*B)*(1-t^2)) ≤ seedRAt t*Real.sqrt u/Real.sqrt (1-t^2) := by
  have hH : 0 < 36*B := by positivity [B_positive]
  have hz := parameterized_z_positive ht.1 ht.2 seedT_range.2
  have hsH : 0 < Real.sqrt (36*B) := Real.sqrt_pos.mpr hH
  have hsz : 0 < Real.sqrt (1-t^2) := Real.sqrt_pos.mpr hz
  have hg := joint_coefficient_nonneg_parameter t
  rw [show 8*u*jointCreationCoefficient ((36*B)*(1-t^2)) =
      (8*jointCreationCoefficient ((36*B)*(1-t^2)))*u by ring,
    Real.sqrt_mul (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hg),Real.sqrt_mul hH.le]
  have hh := mul_le_mul_of_nonneg_right (joint_root_coefficient_le_envelope t)
    (div_nonneg (Real.sqrt_nonneg u) hsz.le)
  convert hh using 1 <;> field_simp [hsH.ne',hsz.ne']

theorem centered_joint_seed_margin (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    (-deriv seedPhi u/seedPhi u)*(seedAlpha u*(9*B/2)*seedPhi u-
      (64/(3*(1-seedAlpha u))-17)*u) >
      16+2*Real.sqrt (8*u*jointCreationCoefficient ((36*B)*seedPhi u))/
        Real.sqrt ((36*B)*seedPhi u) := by
  have hm := centered_seed_margin u hu
  have hr := joint_root_le_envelope (seedParameter_range hu) hu.1
  rw [←seedPhi_z_identity hu] at hr
  linarith

end KLSBelow25.OptimizedJointCreationSeed23849
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedShape
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedAlpha_ge_third
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.centered_seed_margin
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.joint_coefficient_nonneg_parameter
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.joint_coefficient_sq_envelope
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.joint_root_coefficient_le_envelope
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.joint_root_le_envelope
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.centered_joint_seed_margin
