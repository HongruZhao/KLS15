import KLSConstantImprovement.SyntheticEightDegreeBudget
import KLSConstantImprovement.SyntheticThirteenFiniteOrbit20261020
import KLSConstantImprovement.InfiniteValueMonotoneThreshold
import KLSConstantImprovement.ActualSubexponentialFamilyFloor
import KLSConstantImprovement.QuarticEndpointSyntheticCorner

/-! A stronger restriction on endpoints of the CURRENT quartic-head
generator/Bellman method. It uses a synthetic scalar orbit, not an
admissible-law extremizer. The head corner condition is explicit and is
proved separately for the displayed current cubic-to-quartic barrier.
Future stronger analytic supports need not satisfy that condition.

This is a method-family floor, not a lower bound for the KLS constant.
This isolated source draft has not been compiled by its author. -/

noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.ActualCurrentQuarticMethodFloor13
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
open KLSConstantImprovement.GeneralSubexponentialWeightedObservation
open KLSConstantImprovement.ProperInfiniteRatioPathSelection
open KLSConstantImprovement.SubexponentialTerminalSupremum
open KLSConstantImprovement.InfiniteValueMonotoneThreshold

theorem actual_current_head_endpoint_gt_thirteen
    (P : Parameters) (H A B : ℝ)
    (hcert : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (hH : (360 : ℝ) ≤ H) (hcorner : (265 / 4 : ℝ) + A * 10 ≤ B)
    (hsub : SubexponentialLowerWeight P.t)
    (N : ℕ) (hth : ∀ d, N ≤ d → P.theta d = 0)
    (hl : ∀ d, N ≤ d → P.lambda d = 0)
    (hzeta : ∀ d, N ≤ d → P.zeta d = 0)
    (p : ℝ) (hp : 1 ≤ p)
    (hstrict : P.C < p * infiniteValue (2 / P.K ^ 2) p (fun i => P.t (i + 2))) :
    (13 : ℝ) < 1 + P.K * p := by
  have hK := hcert.K_positive
  have hKfloor := ActualSubexponentialFamilyFloor.K_lower_of_actual_subexponential_profile
    P hK hcert.C_nonneg hcert.c_positive.le
    hcert.young_positive hcert.weight_positive hcert.alpha_nonneg hcert.alpha_lt_one
    hsub N hth hl hzeta hcert.coefficient_lower
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hslo : (7071 / 5000 : ℝ) < Real.sqrt 2 := by nlinarith
  have hKlo : (14571 / 1250 : ℝ) ≤ P.K := by nlinarith
  by_contra hfail
  have hprod : P.K * p ≤ 12 := by linarith
  have hK12 : P.K ≤ 12 := by nlinarith
  have hpHigh : p ≤ 12 / P.K :=
    (le_div_iff₀ hK).mpr (by simpa only [mul_comm] using hprod)
  let Z := SyntheticThirteenFiniteOrbit20261020.Z P.K
  let c := SyntheticThirteenFiniteOrbit20261020.c P.K
  let w : ℕ → ℝ := fun i => P.t (i + 2)
  obtain ⟨hZ0, hZ1, hZpos, hc, hrec, hcap, hupper, henv⟩ :=
    SyntheticThirteenFiniteOrbit20261020.uniform_scalar_orbit P.K hKlo hK12
  have hw : FullFloors w := by
    intro ρ hρ
    obtain ⟨τ, hτ, hlow⟩ := hsub ρ hρ
    exact ⟨τ, hτ, fun i => hlow (i + 2) (by omega)⟩
  have hbridge :
      (∑ d ∈ Finset.Icc 2 8, P.t d * SyntheticThirteenFiniteOrbit20261020.z d / P.K ^ d)
        ≤ P.C := by
    change (∑ d ∈ Finset.Icc 2 8, P.t d * SyntheticEightDegreeBudget.z d / P.K ^ d) ≤ P.C
    exact (SyntheticEightDegreeBudget.synthetic_budget_lt hcert hH hcorner).le
  have hbudget (j : ℕ) : WeightedOrbitBellmanTail.spend w c j ≤ P.C :=
    SyntheticThirteenFiniteOrbit20261020.spend_le_budget P.K P.C hK P.t
      (fun d hd => (hcert.weight_positive d hd).le) hbridge j
  have hZ1lower : p ≤ Z 1 := by
    change p ≤ SyntheticThirteenFiniteOrbit20261020.Z P.K 1
    rw [hZ1]
    exact hpHigh
  have hh := actual_initial_lt_of_strict_budget Z c w (by positivity : 0 ≤ 2 / P.K ^ 2)
    (floors_nonempty hw) hp (fun i => (hZpos i).le) hc hZ0
    (fun i _ _ => hrec i) hcap hbudget henv hstrict
  exact (not_lt_of_ge hZ1lower) hh

/-- Specialization to the current raw-cubic quartic barrier family. This
spells out which analytic head family the stronger method floor covers. -/
theorem current_barrier_endpoint_gt_thirteen
    (P : Parameters) (H J s : ℝ)
    (hcert : RawCubicQuarticWeightedBudget.ScalarCertificate P H (J * s / (16 * H)) (J / 576))
    (hH : (400 : ℝ) ≤ H) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hJ : 112 * H ≤ J * (1 - s))
    (hsub : SubexponentialLowerWeight P.t)
    (N : ℕ) (hth : ∀ d, N ≤ d → P.theta d = 0)
    (hl : ∀ d, N ≤ d → P.lambda d = 0)
    (hzeta : ∀ d, N ≤ d → P.zeta d = 0)
    (p : ℝ) (hp : 1 ≤ p)
    (hstrict : P.C < p * infiniteValue (2 / P.K ^ 2) p (fun i => P.t (i + 2))) :
    (13 : ℝ) < 1 + P.K * p := by
  exact actual_current_head_endpoint_gt_thirteen P H (J * s / (16 * H)) (J / 576)
    hcert (by linarith) (SyntheticEightDegreeBudget.current_barrier_corner H J s hH hs0 hs1 hJ)
    hsub N hth hl hzeta p hp hstrict

/-- For the actual endpoint-certificate head family, the corner condition
is discharged by its existing margin and nonnegativity fields. -/
theorem current_endpoint_certificate_endpoint_gt_thirteen
    (P : Parameters) (H J s a b c : ℝ)
    (hcert : RawCubicQuarticWeightedBudget.ScalarCertificate P H (J * s / (16 * H)) (J / 576))
    (hendpoint : RawCubicQuarticEndpointBarrier.EndpointCertificate H J s a b c)
    (hH : (400 : ℝ) ≤ H) (hsub : SubexponentialLowerWeight P.t)
    (N : ℕ) (hth : ∀ d, N ≤ d → P.theta d = 0)
    (hl : ∀ d, N ≤ d → P.lambda d = 0)
    (hzeta : ∀ d, N ≤ d → P.zeta d = 0)
    (p : ℝ) (hp : 1 ≤ p)
    (hstrict : P.C < p * infiniteValue (2 / P.K ^ 2) p (fun i => P.t (i + 2))) :
    (13 : ℝ) < 1 + P.K * p := by
  exact actual_current_head_endpoint_gt_thirteen P H (J * s / (16 * H)) (J / 576)
    hcert (by linarith)
    (QuarticEndpointSyntheticCorner.endpoint_contains_synthetic_corner hendpoint hH)
    hsub N hth hl hzeta p hp hstrict

end KLSConstantImprovement.ActualCurrentQuarticMethodFloor13

#print axioms KLSConstantImprovement.ActualCurrentQuarticMethodFloor13.actual_current_head_endpoint_gt_thirteen
#print axioms KLSConstantImprovement.ActualCurrentQuarticMethodFloor13.current_barrier_endpoint_gt_thirteen
#print axioms KLSConstantImprovement.ActualCurrentQuarticMethodFloor13.current_endpoint_certificate_endpoint_gt_thirteen
