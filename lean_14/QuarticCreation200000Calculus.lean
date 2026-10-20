import QuarticCreation200000Inverse
import SquareRootResidualAlgebra
import GenericVariableBarrierAssembly
noncomputable section
open Set
namespace KLSBelow25.QuarticCreation200000
open KLSBelow25 KLS.DeterministicBridgeNext
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def parameterValue (t:ℝ) : ℝ := t^2*(seedV t)^2

theorem hasDerivAt_parameterValue (t:ℝ) :
    HasDerivAt parameterValue (2*t*seedV t*seedSlope t) t := by
  have he := ((hasDerivAt_id' t).pow 2).mul ((hasDerivAt_seedV t).pow 2)
  convert he using 1
  · rfl
  · dsimp [seedSlope]
    norm_num
    ring

theorem parameterValue_monotone : MonotoneOn parameterValue (Icc (0:ℝ) seedT) := by
  apply (strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_).monotoneOn
  · exact ((continuous_id.pow 2).mul (continuous_seedV.pow 2)).continuousOn
  · intro t ht
    have hti : t∈Ioo (0:ℝ) seedT := by simpa only [interior_Icc] using ht
    rw [(hasDerivAt_parameterValue t).deriv]
    exact mul_pos (mul_pos (mul_pos (by norm_num) hti.1)
      (seedV_positive ⟨hti.1.le,hti.2.le⟩)) (seedSlope_positive ⟨hti.1.le,hti.2.le⟩)

def seedAlphaAt (t:ℝ) : ℝ := 1-seedC*t*seedV t/Real.sqrt (1-t^2)

theorem seed_alpha_ge_half {t:ℝ} (ht:0<t) (htc:t ≤ seedCut) : (1/2:ℝ) ≤ seedAlphaAt t := by
  have hT:t ≤ seedT := htc.trans seedCut_range.2.le
  have hz:0<1-t^2 := VariableAlpha24.parameterized_z_positive ht.le hT seedT_range.2
  have hs:0<Real.sqrt (1-t^2) := Real.sqrt_pos.mpr hz
  have hs2 := Real.sq_sqrt hz.le
  have ha := seedAlphaHalf_positive ⟨ht.le,htc⟩
  have hv := seedV_positive ⟨ht.le,hT⟩
  have hc := seedC_positive
  have hx:0 ≤ seedC*t*seedV t := by positivity
  have hsmall:2*(seedC*t*seedV t) ≤ Real.sqrt (1-t^2) := by
    dsimp [seedAlphaHalf] at ha
    nlinarith [sq_nonneg (2*(seedC*t*seedV t)+Real.sqrt (1-t^2))]
  have hd:seedC*t*seedV t/Real.sqrt (1-t^2) ≤ (1/2:ℝ) :=
    (div_le_iff₀ hs).mpr (by linarith)
  dsimp [seedAlphaAt]
  linarith

theorem seed_alpha_mem_unit {t:ℝ} (ht:0<t) (htc:t ≤ seedCut) : seedAlphaAt t∈Ioo (0:ℝ) 1 := by
  refine ⟨by linarith [seed_alpha_ge_half ht htc],?_⟩
  dsimp [seedAlphaAt]
  have hv := seedV_positive ⟨ht.le,htc.trans seedCut_range.2.le⟩
  have hp:0<seedC*t*seedV t/Real.sqrt (1-t^2) := div_pos (mul_pos (mul_pos seedC_positive ht) hv)
    (Real.sqrt_pos.mpr (VariableAlpha24.parameterized_z_positive ht.le
      (htc.trans seedCut_range.2.le) seedT_range.2))
  linarith

def seedAlpha (u:ℝ) : ℝ := if u=0 then alphaZero else
  if seedParameter u ≤ seedCut then seedAlphaAt (seedParameter u) else 1/2

theorem seedAlpha_unit {u:ℝ} (hu:u∈Icc (0:ℝ) 1) : seedAlpha u∈Ioo (0:ℝ) 1 := by
  by_cases hz:u=0
  · simp only [seedAlpha,hz,ite_true]
    exact ⟨by linarith [alphaZero_range.1],alphaZero_range.2⟩
  · have hp := seedParameter_positive hu (lt_of_le_of_ne hu.1 (Ne.symm hz))
    by_cases hc:seedParameter u ≤ seedCut
    · simpa only [seedAlpha,hz,ite_false,hc,ite_true] using seed_alpha_mem_unit hp hc
    · simp only [seedAlpha,hz,ite_false,hc]
      norm_num

theorem seedAlpha_ge_half {u:ℝ} (hu:u∈Icc (0:ℝ) 1) : (1/2:ℝ) ≤ seedAlpha u := by
  by_cases hz:u=0
  · simpa only [seedAlpha,hz,ite_true] using alphaZero_range.1
  · have hp := seedParameter_positive hu (lt_of_le_of_ne hu.1 (Ne.symm hz))
    by_cases hc:seedParameter u ≤ seedCut
    · simpa only [seedAlpha,hz,ite_false,hc,ite_true] using seed_alpha_ge_half hp hc
    · simp only [seedAlpha,hz,ite_false,hc]
      norm_num

def seedShape : ScalarVariableBarrierShape where
  phi := seedPhi
  alpha := seedAlpha
  continuous := seedInverseBarrier.continuousOn_phi
  positive := fun _ hu => seedInverseBarrier.phi_positive hu
  antitone := seedInverseBarrier.strictAntiOn_phi.antitoneOn
  concave := seedInverseBarrier.concaveOn_phi
  hasDeriv := fun _ hu => by rw [(hasDerivAt_seedPhi hu).deriv]; exact hasDerivAt_seedPhi hu
  derivative_negative := fun _ hu => seedInverseBarrier.deriv_phi_negative hu
  zero := seedPhi_zero
  alpha_unit := fun _ hu => seedAlpha_unit hu

def variableP (a t:ℝ) : ℝ := (J/H)*(1-t^2)+32*t^2*(seedV t)^2-a*t*seedV t-
  29*(1-t^2)*seedV t*seedSlope t

def variableQ (c t:ℝ) : ℝ := ((J/H)*seedC+44/seedC)*t*seedV t+
  (radicalB*t*seedV t+c)*seedV t*seedSlope t

def halfP (a t:ℝ) : ℝ := (J/(2*H))*(1-t^2)-56*t^2*(seedV t)^2-a*t*seedV t-
  29*(1-t^2)*seedV t*seedSlope t

def halfQ (c t:ℝ) : ℝ := (radicalB*t*seedV t+c)*seedV t*seedSlope t

theorem variable_residual_identity (a c:ℝ) {t:ℝ} (ht:0<t) (htT:t ≤ seedT) :
    seedAlphaAt t*(J/H)*(1-t^2)-(44/(1-seedAlphaAt t)-32)*(t^2*(seedV t)^2)-
      a*t*seedV t+(29*(1-t^2)+(radicalB*t*seedV t+c)*Real.sqrt (1-t^2))*(-(seedV t*seedSlope t))=
    variableP a t-Real.sqrt (1-t^2)*variableQ c t := by
  have hv := seedV_positive ⟨ht.le,htT⟩
  have he := VariableAlpha24.variable_alpha_residual_identity
    (z:=1-t^2) (c:=seedC) (t:=t) (v:=seedV t) (s:=seedSlope t)
    (p:=J/H) (C:=44) (D:=32) (R:=radicalB*t*seedV t+c) (r0:=a) (a:=29)
    (VariableAlpha24.parameterized_z_positive ht.le htT seedT_range.2)
    seedC_positive.ne' ht.ne' hv.ne'
  convert he using 1 <;> dsimp [seedAlphaAt,variableP,variableQ] <;> ring

theorem half_residual_identity (a c t:ℝ) :
    (1/2:ℝ)*(J/H)*(1-t^2)-(44/(1-(1/2:ℝ))-32)*(t^2*(seedV t)^2)-
      a*t*seedV t+(29*(1-t^2)+(radicalB*t*seedV t+c)*Real.sqrt (1-t^2))*(-(seedV t*seedSlope t))=
    halfP a t-Real.sqrt (1-t^2)*halfQ c t := by
  norm_num only
  dsimp [halfP,halfQ]
  ring

end KLSBelow25.QuarticCreation200000
#print axioms KLSBelow25.QuarticCreation200000.seedShape
#print axioms KLSBelow25.QuarticCreation200000.variable_residual_identity
