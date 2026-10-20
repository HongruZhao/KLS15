import KLSConstantImprovement.ActualSubexponentialFamilyFloor
import KLSConstantImprovement.TrueCapTwoStageOrbitObstruction
import KLSConstantImprovement.RawCubicQuarticWeightedBudget

/-! One displayed interface joining the ACTUAL all-rank generator family
to the correctly normalized two-stage true-cap obstruction. This is a
proof-family endpoint restriction, NOT a lower bound on the optimal KLS
constant. The raw input is required to be at least the present raw cap;
an improved raw analytic input changes this particular obstruction. -/
noncomputable section
namespace KLSConstantImprovement.ActualTrueCapMethodFloor129
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
open KLSConstantImprovement.GeneralSubexponentialWeightedObservation
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

theorem actual_profile_true_cap_endpoint_gt_129
    (P : Parameters) (H A B : ℝ)
    (hcert : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (htwo : P.t 2=1) (hH : (802604693/2000000 : ℝ) ≤ H)
    (hsub : SubexponentialLowerWeight P.t)
    (N : ℕ)
    (hth : ∀ d,N ≤ d → P.theta d=0)
    (hl : ∀ d,N ≤ d → P.lambda d=0)
    (hzeta : ∀ d,N ≤ d → P.zeta d=0)
    (p : ℝ) (hp : 1 ≤ p) (V0 V1 V2 : ℝ → ℝ)
    (hstep0 : ∀ s,1 ≤ s → p-(2/P.K^2)/p ≤ s → s ≤ p →
      V0 p ≤ p-s+s*V1 s)
    (hstep1 : ∀ r,1 ≤ r → r ≤ p → ∀ s,1 ≤ s →
      r-(2/P.K^2)/r ≤ s → s ≤ r →
      V1 r ≤ P.t 3*(r-s)+s*V2 s)
    (hboundary : V2 1=0)
    (hbudget : P.C < p*V0 p) :
    (129/10 : ℝ) < 1+P.K*p := by
  have hK : 0 < P.K := hcert.K_positive
  have hKfloor := ActualSubexponentialFamilyFloor.K_lower_of_actual_subexponential_profile
    P hcert.K_positive hcert.C_nonneg hcert.c_positive.le
    hcert.young_positive hcert.weight_positive hcert.alpha_nonneg hcert.alpha_lt_one
    hsub N hth hl hzeta hcert.coefficient_lower
  have hw : 0 ≤ P.t 3 := (hcert.weight_positive 3 (by omega)).le
  have hsmall : P.t 3*(802604693/2000000 : ℝ)/(36*P.K^3) ≤
      P.t 3*H/(36*P.K^3) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hH hw) (by positivity)
  have hbase : 2/P.K^2+P.t 3*((802604693/2000000 : ℝ)/(36*P.K^3)) ≤ P.C := by
    calc
      _=2*P.t 2/P.K^2+P.t 3*(802604693/2000000 : ℝ)/(36*P.K^3) := by
        rw [htwo]
        ring
      _ ≤ 2*P.t 2/P.K^2+P.t 3*H/(36*P.K^3) := add_le_add_right hsmall _
      _ ≤ P.C := hcert.small_three_budget
  exact TrueCapTwoStageOrbitObstruction.true_cap_family_endpoint_gt_129
    P.K P.C (P.t 3) p V0 V1 V2 hKfloor hw hp hstep0 hstep1 hboundary hbase hbudget

end KLSConstantImprovement.ActualTrueCapMethodFloor129
#print axioms KLSConstantImprovement.ActualTrueCapMethodFloor129.actual_profile_true_cap_endpoint_gt_129
