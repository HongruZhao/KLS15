import SharperCubicBarrierData
noncomputable section
open Set
namespace KLSImprovement.SharperCubicBarrier
open KLSBelow25 KLS.DeterministicBridgeNext
open KLSBelow25.SymmetricCenteredSeed245
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem remainder_majorant : (20/3:ℝ)/Real.sqrt B≤R := by
  have hs := Real.sq_sqrt B_positive.le
  have hsp : 0<Real.sqrt B := Real.sqrt_pos.mpr B_positive
  apply (div_le_iff₀ hsp).mpr
  have hnonneg : 0≤R*Real.sqrt B := mul_nonneg R_positive.le (Real.sqrt_nonneg B)
  have hsq : (20/3:ℝ)^2≤(R*Real.sqrt B)^2 := by
    rw [mul_pow,hs]
    exact R_majorant
  nlinarith

theorem sqrt_residual_positive {t : ℝ} (ht : t∈Icc (0 : ℝ) seedT) :
    0<P t-Real.sqrt (1-t^2)*Q t := by
  exact VariableAlpha24.sqrt_residual_positive
    (VariableAlpha24.parameterized_z_positive ht.1 ht.2 seedT_range.2)
    (P_positive ht) (Q_positive ht) (D_positive ht)

theorem differential_residual_identity {t : ℝ} (ht : 0<t) (htT : t ≤ seedT) :
    seedAlphaAt t*(9*B/2)*(1-t^2)-
      (64/(3*(1-seedAlphaAt t))-17)*(t^2*(seedV t)^2)+
      (16*(1-t^2)+R*Real.sqrt (1-t^2))*(-(seedV t*seedSlope t))=
      P t-Real.sqrt (1-t^2)*Q t := by
  have hi : t∈Icc 0 seedT := ⟨ht.le,htT⟩
  have he := VariableAlpha24.variable_alpha_residual_identity
    (z:=1-t^2) (c:=seedC) (t:=t) (v:=seedV t) (s:=seedSlope t)
    (p:=9*B/2) (C:=64/3) (D:=17) (R:=R) (r0:=0) (a:=16)
    (VariableAlpha24.parameterized_z_positive ht.le htT seedT_range.2)
    (ne_of_gt seedC_positive) (ne_of_gt ht) (ne_of_gt (seedV_positive hi))
  convert he using 1 <;> dsimp [seedAlphaAt,P,Q] <;> ring

theorem differential_residual_positive {t : ℝ} (ht : 0<t) (htT : t ≤ seedT) :
    0<seedAlphaAt t*(9*B/2)*(1-t^2)-
      (64/(3*(1-seedAlphaAt t))-17)*(t^2*(seedV t)^2)+
      (16*(1-t^2)+R*Real.sqrt (1-t^2))*(-(seedV t*seedSlope t)) := by
  rw [differential_residual_identity ht htT]
  exact sqrt_residual_positive ⟨ht.le,htT⟩

theorem centered_seed_margin (u : ℝ) (hu : u∈Icc (0 : ℝ) 1) :
    (-deriv seedPhi u/seedPhi u)*(seedAlpha u*(9*B/2)*seedPhi u-
      (64/(3*(1-seedAlpha u))-17)*u)>16+(20/3)/Real.sqrt (B*seedPhi u) := by
  have hR := remainder_majorant
  by_cases hz : u=0
  · subst u
    have hm := zero_margin_of_slope_majorant
      (sq_pos_of_pos (seedV_positive (by norm_num [seedT] : (0 : ℝ)∈Icc 0 seedT))) hR
      zero_strict_margin
    rw [seedQ_zero,seedPhi_zero]
    simp only [seedAlpha,ite_true]
    norm_num only [mul_one,mul_zero,sub_zero] at ⊢
    nlinarith [hm]
  · have hp : 0<u := lt_of_le_of_ne hu.1 (Ne.symm hz)
    have hr := differential_residual_positive (seedParameter_positive hu hp)
      (seedParameter_range hu).2
    rw [←seedPhi_z_identity hu,←seedPhi_u_identity hu] at hr
    have hzpos : 0<seedPhi u := seedInverseBarrier.phi_positive hu
    have hUp := seedUp_negative hu
    have hcoef : Real.sqrt (seedPhi u)*(-(seedV (seedParameter u)*seedSlope (seedParameter u)))≤0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) hUp.le
    have hloss : (R-(20/3)/Real.sqrt B)*
        (Real.sqrt (seedPhi u)*(-(seedV (seedParameter u)*seedSlope (seedParameter u))))≤0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hR) hcoef
    have hm : 0<(-deriv seedPhi u/seedPhi u)*
        (seedAlphaAt (seedParameter u)*(9*B/2)*seedPhi u-
          (64/(3*(1-seedAlphaAt (seedParameter u)))-17)*u)-16-
        ((20/3)/Real.sqrt B)/Real.sqrt (seedPhi u) := by
      apply inverse_margin_of_differential_residual hzpos hUp (seedQ_identity hu)
      nlinarith
    have he : ((20/3:ℝ)/Real.sqrt B)/Real.sqrt (seedPhi u)=
        (20/3)/Real.sqrt (B*seedPhi u) := by rw [Real.sqrt_mul B_positive.le]; ring
    rw [he] at hm
    simpa only [seedAlpha,hz,ite_false] using (by linarith :
      (-deriv seedPhi u/seedPhi u)*(seedAlphaAt (seedParameter u)*(9*B/2)*seedPhi u-
        (64/(3*(1-seedAlphaAt (seedParameter u)))-17)*u)>
        16+(20/3)/Real.sqrt (B*seedPhi u))

end KLSImprovement.SharperCubicBarrier
#print axioms KLSImprovement.SharperCubicBarrier.centered_seed_margin
