import ResolventOperatorEndgame

/-! The actual canonical positive inverse. The abstract endgame no longer
needs an operator-inverse existence hypothesis. -/
noncomputable section
namespace KLSBelow25
open ContinuousLinearMap InnerProductSpace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem complex_positive_resolvent_isUnit
    (T : H →L[ℂ] H) (hT : T.IsPositive) {a : ℝ} (ha : 0 ≤ a) :
    IsUnit (1 + a • T) := by
  letI := InnerProductSpace.rclikeToReal ℂ H
  have hp : (T.restrictScalars ℝ).IsPositive := by
    refine ⟨hT.isSymmetric.restrictScalars, ?_⟩
    intro x
    exact hT.re_inner_nonneg_left x
  have hu := positive_resolvent_isUnit (T.restrictScalars ℝ) hp ha
  have hbij : Function.Bijective (1 + a • T.restrictScalars ℝ : H →L[ℝ] H) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hu
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr hbij

def canonicalIntegrationResolvent (R : H →L[ℂ] H) (L : E →L[ℂ] H) (a : ℝ) : H →L[ℂ] H :=
  Ring.inverse (1 + a • integrationGram R L)

def rationalIntegrationComparison (R : H →L[ℂ] H) (L : E →L[ℂ] H) (a : ℝ) : Prop :=
  ∀ v : H, ‖R v‖ ^ 2 ≤
    Complex.re ⟪(a⁻¹ • (1 - canonicalIntegrationResolvent R L a)) v, v⟫_ℂ

theorem canonicalIntegrationResolvent_inverse
    (R : H →L[ℂ] H) (L : E →L[ℂ] H) {a : ℝ} (ha : 0 ≤ a) :
    (1 + a • integrationGram R L) * canonicalIntegrationResolvent R L a = 1 :=
  Ring.mul_inverse_cancel _
    (complex_positive_resolvent_isUnit _ (integrationGram_isPositive R L) ha)

theorem canonical_operator_endpoint_twentyFive
    (R : H →L[ℂ] H) (L : E →L[ℂ] H) {a : ℝ} (ha : 0 < a)
    (hcomparison : rationalIntegrationComparison R L a)
    (hobs1 : ‖R.comp L‖ ^ 2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖(R ^ (j + 2)).comp L‖ ^ 2 ≤ (121 / 4 : ℝ) * (223 / 10 : ℝ) ^ j) :
    1 + ‖R‖ ^ 2 ≤ 25 :=
  resolvent_operator_endpoint_twentyFive R L (canonicalIntegrationResolvent R L a)
    ha (canonicalIntegrationResolvent_inverse R L ha.le) hcomparison hobs1 hobs

theorem canonical_operator_endpoint_twentyFour886
    (R : H →L[ℂ] H) (L : E →L[ℂ] H) {a : ℝ} (ha : 0 < a)
    (hcomparison : rationalIntegrationComparison R L a)
    (hobs1 : ‖R.comp L‖ ^ 2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖(R ^ (j + 2)).comp L‖ ^ 2 ≤ (121 / 4 : ℝ) * (2221 / 100 : ℝ) ^ j) :
    1 + ‖R‖ ^ 2 ≤ (12443 / 500 : ℝ) :=
  resolvent_operator_endpoint_twentyFour886 R L (canonicalIntegrationResolvent R L a)
    ha (canonicalIntegrationResolvent_inverse R L ha.le) hcomparison hobs1 hobs

#print axioms complex_positive_resolvent_isUnit
#print axioms canonicalIntegrationResolvent_inverse
#print axioms canonical_operator_endpoint_twentyFive
#print axioms canonical_operator_endpoint_twentyFour886
end KLSBelow25
