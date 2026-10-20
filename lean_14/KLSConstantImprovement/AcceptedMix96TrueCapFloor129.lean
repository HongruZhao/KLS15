import KLSConstantImprovement.AcceptedMix96Data
import KLSConstantImprovement.ScaledTrueCapTwoStageFloor129

/-! The mixed profile has firstweight aboveone. This exact specialization
uses the scaled two-stage obstruction, retaining the initial factorp.
It restricts this displayed scalar proof family, not the optimalKLSconstant.
Root alone compiles this draft. -/
noncomputable section
namespace KLSConstantImprovement.AcceptedMix96TrueCapFloor129
open KLSConstantImprovement.AcceptedMix96Data
set_option maxHeartbeats 5000000

theorem K_floor : 6+4*Real.sqrt 2 ≤ K := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs1 : Real.sqrt 2 ≤ (3/2 : ℝ) := by nlinarith
  have hk : (12 : ℝ) ≤ K := by norm_num [K]
  nlinarith

theorem small_three_base :
    t 2*(2/K^2)+t 3*((802604693/2000000 : ℝ)/(36*K^3)) ≤ C := by
  norm_num [t,rawMix,a,L,K,C,
    QuarticM48Profile20261020Data.t,QuarticM48Profile20261020Data.tTail,
    QuarticM32Profile20261020Data.t,QuarticM32Profile20261020Data.tTail]

theorem mixed_true_cap_endpoint_gt_129
    (p : ℝ) (V0 V1 V2 : ℝ → ℝ) (hp : 1 ≤ p)
    (hstep0 : ∀ s,1 ≤ s → p-(2/K^2)/p ≤ s → s ≤ p →
      V0 p ≤ t 2*(p-s)+s*V1 s)
    (hstep1 : ∀ r,1 ≤ r → r ≤ p → ∀ s,1 ≤ s →
      r-(2/K^2)/r ≤ s → s ≤ r → V1 r ≤ t 3*(r-s)+s*V2 s)
    (hboundary : V2 1=0) (hbudget : C < p*V0 p) :
    (129/10 : ℝ) < 1+K*p := by
  exact ScaledTrueCapTwoStageFloor129.scaled_true_cap_endpoint_gt_129
    K C (t 2) (t 3) p V0 V1 V2 K_floor
    (t_positive 2 (by omega)) (t_positive 3 (by omega)).le
    hp hstep0 hstep1 hboundary small_three_base hbudget

end KLSConstantImprovement.AcceptedMix96TrueCapFloor129
#print axioms KLSConstantImprovement.AcceptedMix96TrueCapFloor129.K_floor
#print axioms KLSConstantImprovement.AcceptedMix96TrueCapFloor129.small_three_base
#print axioms KLSConstantImprovement.AcceptedMix96TrueCapFloor129.mixed_true_cap_endpoint_gt_129
