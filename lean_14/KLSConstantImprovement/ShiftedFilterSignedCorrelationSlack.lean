import KLSConstantImprovement.SourceMainProjectionLossConditionalPayoff

/-! SAME-source signed BL correlation, without a favorable cross sign.
The actual spectral form calculus and d=D12 identification are paper inputs.
The scalar quarter-band and response consequences are formal here.
No positive uniform correlation credit or new variance/CP cap is asserted. -/
noncomputable section
namespace KLSConstantImprovement.ShiftedFilterSignedCorrelationSlack

theorem centered_shifted_multiplier_band {lambda : ℝ} (hl : 1 ≤ lambda) :
    -(1/4:ℝ) ≤ 1/(lambda+1)-(1/4:ℝ) ∧
      1/(lambda+1)-(1/4:ℝ) ≤ (1/4:ℝ) := by
  have hd : 0 < lambda+1 := by linarith
  have h0 : 0 ≤ 1/(lambda+1) := by positivity
  have h1 : 1/(lambda+1) ≤ (1/2:ℝ) := by
    apply (div_le_iff₀ hd).mpr
    linarith
  constructor <;> linarith

theorem signed_filter_band {c d t : ℝ} (ht : 0 ≤ t)
    (hband : (c-d/4)^2 ≤ t^2/16) :
    (d-t)/4 ≤ c ∧ c ≤ (d+t)/4 := by
  constructor <;> nlinarith

theorem direct_correlation_slack_nonnegative {d t : ℝ}
    (ht : 0 ≤ t) (hd : d^2 ≤ t^2) : 0 ≤ t+d := by
  nlinarith

theorem response_retains_quarter_direct_slack
    {I W r c d t xi losses : ℝ}
    (hShifted : I ≤ W+r-c-xi/2-losses)
    (hLower : (d-t)/4 ≤ c) :
    I ≤ W+r+t/2-(t+d)/4-xi/2-losses := by
  linarith

theorem signed_response_eliminates_direct_slack
    {I W r c d t xi losses k : ℝ}
    (hShifted : I ≤ W+r-c-xi/2-losses)
    (hLower : (d-t)/4 ≤ c) (hComp : W+2*k=3*(r-d)) :
    I ≤ (13/12:ℝ)*W+(3/4:ℝ)*r+t/4+k/6-xi/2-losses := by
  linarith

theorem signed_slack_main_credit_implies_response
    {I W r c d t xi losses D g k q : ℝ}
    (hShifted : I ≤ W+r-c-xi/2-losses)
    (hLower : (d-t)/4 ≤ c)
    (hPaid : xi/2+losses+(4/7:ℝ)*D+(t+d)/4 ≥
      W-r+t/2-(27/4:ℝ)*g-(8/7:ℝ)*(1+Real.sqrt 2)*k-
        (2/7:ℝ)*Real.sqrt 2*q) :
    I ≤ 2*r+(27/4:ℝ)*g+(8/7:ℝ)*(1+Real.sqrt 2)*k+
      (2/7:ℝ)*Real.sqrt 2*q+(4/7:ℝ)*D := by
  have h := response_retains_quarter_direct_slack hShifted hLower
  linarith

end KLSConstantImprovement.ShiftedFilterSignedCorrelationSlack
#print axioms KLSConstantImprovement.ShiftedFilterSignedCorrelationSlack.centered_shifted_multiplier_band
#print axioms KLSConstantImprovement.ShiftedFilterSignedCorrelationSlack.signed_filter_band
#print axioms KLSConstantImprovement.ShiftedFilterSignedCorrelationSlack.direct_correlation_slack_nonnegative
#print axioms KLSConstantImprovement.ShiftedFilterSignedCorrelationSlack.response_retains_quarter_direct_slack
#print axioms KLSConstantImprovement.ShiftedFilterSignedCorrelationSlack.signed_response_eliminates_direct_slack
#print axioms KLSConstantImprovement.ShiftedFilterSignedCorrelationSlack.signed_slack_main_credit_implies_response
