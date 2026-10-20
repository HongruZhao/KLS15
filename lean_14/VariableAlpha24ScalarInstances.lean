import VariableAlpha24InverseBranches
import VariableAlpha24PointwiseResiduals
import InverseDifferentialMargins
import GenericCoefficientObservationTransfer

/-! Genuine seed and every-rank variable-alpha barriers at B=57/2,K=2133/100.
The square-root endpoint uses a separate admissible alpha value. All inverse,
whole-interval and finite-rank inputs are proved in the imported modules. -/
noncomputable section
open Set
namespace VariableAlpha24
open KLSBelow25 KLS.DeterministicBridgeNext
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def seedAlpha (u : ℝ) : ℝ := if u=0 then alphaZero else seedAlphaAt (seedParameter u)
def commonAlpha (u : ℝ) : ℝ := if u=0 then alphaZero else commonAlphaAt (commonParameter u)

theorem seedAlpha_unit {u : ℝ} (hu : u∈Icc (0:ℝ) 1) : seedAlpha u∈Ioo (0:ℝ) 1 := by
  by_cases hz : u=0
  · simpa [seedAlpha,hz] using alphaZero_range
  · simpa [seedAlpha,hz] using seed_alpha_mem_unit
      (seedParameter_positive hu (lt_of_le_of_ne hu.1 (Ne.symm hz))) (seedParameter_range hu).2

theorem commonAlpha_unit {u : ℝ} (hu : u∈Icc (0:ℝ) 1) : commonAlpha u∈Ioo (0:ℝ) 1 := by
  by_cases hz : u=0
  · simpa [commonAlpha,hz] using alphaZero_range
  · simpa [commonAlpha,hz] using common_alpha_mem_unit
      (commonParameter_positive hu (lt_of_le_of_ne hu.1 (Ne.symm hz))) (commonParameter_range hu).2

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

def commonShape : ScalarVariableBarrierShape where
  phi := commonPhi
  alpha := commonAlpha
  continuous := commonInverseBarrier.continuousOn_phi
  positive := fun _ hu => commonInverseBarrier.phi_positive hu
  antitone := commonInverseBarrier.strictAntiOn_phi.antitoneOn
  concave := commonInverseBarrier.concaveOn_phi
  hasDeriv := fun _ hu => by
    rw [(hasDerivAt_commonPhi hu).deriv]
    exact hasDerivAt_commonPhi hu
  derivative_negative := fun _ hu => commonInverseBarrier.deriv_phi_negative hu
  zero := commonPhi_zero
  alpha_unit := fun _ hu => commonAlpha_unit hu

theorem seedUp_negative {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    -(seedV (seedParameter u)*seedSlope (seedParameter u))<0 := by
  exact neg_lt_zero.mpr (mul_pos (seedV_positive (seedParameter_range hu))
    (seedSlope_positive (seedParameter_range hu)))
theorem commonUp_negative {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    -(commonV (commonParameter u)*commonSlope (commonParameter u))<0 := by
  exact neg_lt_zero.mpr (mul_pos (commonV_positive (commonParameter_range hu))
    (commonSlope_positive (commonParameter_range hu)))

theorem seedQ_identity {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    -deriv seedPhi u/seedPhi u =
      -1/(seedPhi u*(-(seedV (seedParameter u)*seedSlope (seedParameter u)))) :=
  inverse_q_identity (hasDerivAt_seedPhi hu).deriv

theorem commonQ_identity {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    -deriv commonPhi u/commonPhi u =
      -1/(commonPhi u*(-(commonV (commonParameter u)*commonSlope (commonParameter u)))) :=
  inverse_q_identity (hasDerivAt_commonPhi hu).deriv

theorem seedQ_zero : -deriv seedPhi 0/seedPhi 0=((seedV 0)^2)⁻¹ := by
  rw [(hasDerivAt_seedPhi (by norm_num : (0:ℝ)∈Icc 0 1)).deriv]
  norm_num [seedParameter,seedPhi_zero,RadicalBarrier.parameter,seedV,seedSlope,seedVp]

theorem commonQ_zero : -deriv commonPhi 0/commonPhi 0=((commonV 0)^2)⁻¹ := by
  rw [(hasDerivAt_commonPhi (by norm_num : (0:ℝ)∈Icc 0 1)).deriv]
  norm_num [commonParameter,commonPhi_zero,RadicalBarrier.parameter,commonV,commonSlope,commonVp]

theorem seed_margin (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    (-deriv seedPhi u/seedPhi u)*(seedAlpha u*(9*B/2)*seedPhi u-
      (6*(4/(1-seedAlpha u)-2)-4)*u)>17+8/Real.sqrt (B*seedPhi u) := by
  have hR : 8/Real.sqrt B ≤ seedR := eight_div_sqrt_le_of_square_majorant
    B_positive seedR_positive.le seedR_majorant
  by_cases hz : u=0
  · subst u
    have hm := zero_margin_of_slope_majorant
      (sq_pos_of_pos (seedV_positive (by norm_num [seedT] : (0:ℝ)∈Icc 0 seedT))) hR
      seed_zero_strict_margin
    rw [seedQ_zero,seedPhi_zero]
    simp [seedAlpha]
    nlinarith [hm]
  · have hp : 0<u := lt_of_le_of_ne hu.1 (Ne.symm hz)
    have hr := seed_differential_residual_positive (seedParameter_positive hu hp)
      (seedParameter_range hu).2
    rw [←seedPhi_z_identity hu,←seedPhi_u_identity hu] at hr
    have hr' : 0 < seedAlphaAt (seedParameter u)*(9*B/2)*seedPhi u-
        (6*(4/(1-seedAlphaAt (seedParameter u))-2)-4)*u+
        (17*seedPhi u+seedR*Real.sqrt (seedPhi u))*
          (-(seedV (seedParameter u)*seedSlope (seedParameter u))) := by
      convert hr using 1 <;> ring
    have hm := inverse_seed_margin_of_majorant_residual
      (seedInverseBarrier.phi_positive hu) (seedUp_negative hu) (seedQ_identity hu) hR hr'
    rw [seed_sqrt_denominator_identity B_positive (seedInverseBarrier.phi_positive hu)] at hm
    simpa [seedAlpha,hz,seedPhi] using hm

theorem common_margin (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    0<(-deriv commonPhi u/commonPhi u)*(commonAlpha u*K*commonPhi u-
      (4/(1-commonAlpha u)-2)*u-(Real.sqrt B/K)*Real.sqrt u)-2-
      (Real.sqrt B/K)/Real.sqrt (commonPhi u) := by
  have hR : Real.sqrt B/K ≤ commonR := sqrt_div_le_of_square_majorant
    B_positive.le K_positive commonR_positive.le commonR_majorant
  by_cases hz : u=0
  · subst u
    have hm := zero_margin_of_slope_majorant
      (sq_pos_of_pos (commonV_positive (by norm_num [commonT] : (0:ℝ)∈Icc 0 commonT))) hR
      common_zero_strict_margin
    rw [commonQ_zero,commonPhi_zero]
    simpa [commonAlpha] using hm
  · have hp : 0<u := lt_of_le_of_ne hu.1 (Ne.symm hz)
    have hr := common_differential_residual_positive (commonParameter_positive hu hp)
      (commonParameter_range hu).2
    rw [←commonPhi_z_identity hu,←commonPhi_u_identity hu] at hr
    have hr' : 0 < commonAlphaAt (commonParameter u)*K*commonPhi u-
        (4/(1-commonAlphaAt (commonParameter u))-2)*u-commonR*Real.sqrt u+
        (2*commonPhi u+commonR*Real.sqrt (commonPhi u))*
          (-(commonV (commonParameter u)*commonSlope (commonParameter u))) := by
      convert hr using 1 <;> ring
    have hm := inverse_common_margin_of_majorant_residual
      (commonInverseBarrier.phi_positive hu) (commonUp_negative hu) (commonQ_identity hu) hR hr'
    simpa [commonAlpha,hz,commonPhi] using hm

def variableAlpha24_seed_barrier : VariableCoefficientInductionBarrier 2 scheme.coefficientH :=
  seedShape.seed scheme (by
    intro u hu
    simpa only [seedShape,scheme_B] using seed_margin u hu)

def variableAlpha24_common_barrier (k : ℕ) (hk : 3 ≤ k) :
    VariableCoefficientInductionBarrier k scheme.coefficientH :=
  commonShape.common scheme k hk scheme_delta_lt (by
    intro u hu
    simpa only [commonShape,scheme_K,scheme_r] using common_margin u hu)

theorem variableAlpha24_seed_barrier_nonempty :
    Nonempty (VariableCoefficientInductionBarrier 2 scheme.coefficientH) :=
  ⟨variableAlpha24_seed_barrier⟩

theorem variableAlpha24_common_barriers (k : ℕ) (hk : 3 ≤ k) :
    Nonempty (VariableCoefficientInductionBarrier k scheme.coefficientH) :=
  ⟨variableAlpha24_common_barrier k hk⟩

end VariableAlpha24
#print axioms VariableAlpha24.variableAlpha24_seed_barrier
#print axioms VariableAlpha24.variableAlpha24_common_barrier
