import KLSConstantImprovement.ActualCurrentQuarticMethodFloor13068
import KLSConstantImprovement.AcceptedMix96MethodFloor13068
import KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint
import KLSConstantImprovement.QuarticM96MixFixedInfiniteScalarBracket20261020

/-! Exact direction of the 13.068 result and the remaining upper-bound target.

The 13.068 statements restrict proof certificates. They do not assert a
13.068 upper or lower bound for the universal Poincare constant. The final
epsilon theorem is conditional: an approximating family of actual universal
upper bounds has still to be constructed. All published predecessors remain
unchanged.
-/
noncomputable section
open scoped ENNReal
namespace KLSConstantImprovement.Verified13068Scope20261020

open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
open KLSConstantImprovement.GeneralSubexponentialWeightedObservation
open KLSConstantImprovement.ProperInfiniteRatioPathSelection

def requestedTarget : ℝ := 3267 / 250
def verifiedUpper : ℝ := 13810833 / 1000000

theorem best_verified_universal_upper :
    universalPoincareConstant ≤ (13810833 / 1000000 : ℝ≥0∞) :=
  QuarticM96MixTrueCapBellman20261020TightEndpoint.universal_poincare_upper

theorem requested_target_lt_fixed_profile :
    requestedTarget < QuarticM96MixFixedInfiniteScalarBracket20261020.fixedScalarEndpoint := by
  have h := QuarticM96MixFixedInfiniteScalarBracket20261020.fixed_endpoint_bounds.1
  norm_num [requestedTarget] at *
  linarith

theorem no_fixed_profile_endpoint_at_or_below_target :
    ¬ QuarticM96MixFixedInfiniteScalarBracket20261020.fixedScalarEndpoint ≤ requestedTarget :=
  not_le.mpr requested_target_lt_fixed_profile

theorem gap_between_verified_upper_and_requested_target :
    verifiedUpper - requestedTarget = (742833 / 1000000 : ℝ) := by
  norm_num [verifiedUpper, requestedTarget]

theorem fixed_profile_gap_from_requested_target :
    (742832 / 1000000 : ℝ) ≤
      QuarticM96MixFixedInfiniteScalarBracket20261020.fixedScalarEndpoint - requestedTarget := by
  have h := QuarticM96MixFixedInfiniteScalarBracket20261020.fixed_endpoint_bounds.1
  norm_num [requestedTarget] at *
  linarith

/-- A single covered current-head strict-budget certificate cannot have
endpoint at or below 13.068. This does not exclude an outer sequence tending
down to 13.068, and it is not a universal Poincare lower bound. -/
theorem no_current_head_certificate_at_or_below_target
    (P : Parameters) (H J s a b c : ℝ)
    (hcert : RawCubicQuarticWeightedBudget.ScalarCertificate P H (J * s / (16 * H)) (J / 576))
    (hendpoint : RawCubicQuarticEndpointBarrier.EndpointCertificate H J s a b c)
    (hH : (400 : ℝ) ≤ H) (hsub : SubexponentialLowerWeight P.t)
    (N : ℕ) (hth : ∀ d, N ≤ d → P.theta d = 0)
    (hl : ∀ d, N ≤ d → P.lambda d = 0)
    (hzeta : ∀ d, N ≤ d → P.zeta d = 0)
    (p : ℝ) (hp : 1 ≤ p) (hsmall : 1 + P.K * p ≤ requestedTarget) :
    ¬ P.C < p * infiniteValue (2 / P.K ^ 2) p (fun i => P.t (i + 2)) := by
  intro hstrict
  have hh := ActualCurrentQuarticMethodFloor13068.current_endpoint_certificate_endpoint_gt_thirteen068
    P H J s a b c hcert hendpoint hH hsub N hth hl hzeta p hp hstrict
  unfold requestedTarget at hsmall
  linarith

theorem no_current_mix_certificate_at_or_below_target
    (p : ℝ) (hp : 1 ≤ p)
    (hsmall : 1 + AcceptedMix96Data.K * p ≤ requestedTarget) :
    ¬ AcceptedMix96Data.C < p * infiniteValue (2 / AcceptedMix96Data.K ^ 2) p
      (fun i => AcceptedMix96Data.t (i + 2)) := by
  intro hstrict
  have hh := AcceptedMix96MethodFloor13068.method_floor_thirteen068 p hp hstrict
  unfold requestedTarget at hsmall
  linarith

/-- An explicit sufficient limiting obligation for the requested upper
bound. The hypothesis is OPEN; this theorem alone is not the upper bound. -/
theorem universal_target_of_all_epsilon_upper_bounds
    (h : ∀ ε : ℝ, 0 < ε →
      universalPoincareConstant ≤ ENNReal.ofReal (requestedTarget + ε)) :
    universalPoincareConstant ≤ ENNReal.ofReal requestedTarget := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεr : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hh := h (ε : ℝ) hεr
  rw [ENNReal.ofReal_add (p := requestedTarget) (q := (ε : ℝ))
    (by norm_num [requestedTarget]) ε.coe_nonneg] at hh
  simpa only [ENNReal.ofReal_coe_nnreal] using hh

end KLSConstantImprovement.Verified13068Scope20261020

#print axioms KLSConstantImprovement.Verified13068Scope20261020.best_verified_universal_upper
#print axioms KLSConstantImprovement.Verified13068Scope20261020.requested_target_lt_fixed_profile
#print axioms KLSConstantImprovement.Verified13068Scope20261020.no_fixed_profile_endpoint_at_or_below_target
#print axioms KLSConstantImprovement.Verified13068Scope20261020.gap_between_verified_upper_and_requested_target
#print axioms KLSConstantImprovement.Verified13068Scope20261020.fixed_profile_gap_from_requested_target
#print axioms KLSConstantImprovement.Verified13068Scope20261020.no_current_head_certificate_at_or_below_target
#print axioms KLSConstantImprovement.Verified13068Scope20261020.no_current_mix_certificate_at_or_below_target
#print axioms KLSConstantImprovement.Verified13068Scope20261020.universal_target_of_all_epsilon_upper_bounds
