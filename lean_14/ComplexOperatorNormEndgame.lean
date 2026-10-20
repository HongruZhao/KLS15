import OperatorNormEndgame
import SpectralPowerEnvelope

/-! The endgame with an actual complex spectral-radius bound, rather than
an assumed power envelope.  Compatible tensor realization and the deduction
of this spectral bound from curvature remain separate obligations. -/
noncomputable section
namespace KLSBelow25
variable {H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem complex_operator_norm_sq_le_of_spectralRadius
    (R : H →L[ℂ] H) (L : E →L[ℂ] H)
    {B K s : ℝ} (hB : 0 < B) (hK : 0 < K) (hs : 0 < s)
    (hDelta : 0 < s ^ 2 - K * s - 2)
    (hGap : 2 * B * s < (s ^ 2 - K * s - 2) ^ 2)
    (hcomparison : ∀ v : H, ‖R v‖ ^ 2 ≤
      ‖ContinuousLinearMap.adjoint R v‖ ^ 2 + ‖ContinuousLinearMap.adjoint L v‖ ^ 2)
    (hobs1 : ‖R.comp L‖ ^ 2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖(R ^ (j + 2)).comp L‖ ^ 2 ≤ B * K ^ j)
    (hspec : spectralRadius ℂ (ContinuousLinearMap.adjoint R) ≤ ENNReal.ofReal (Real.sqrt K)) :
    ‖R‖ ^ 2 ≤ s := by
  apply operator_norm_sq_le_of_power_envelope R L hB hK hs hDelta hGap
    hcomparison hobs1 hobs
  intro rho hrho
  obtain ⟨M, hM⟩ := squared_power_envelope_of_spectralRadius_le
    (ContinuousLinearMap.adjoint R) hK hspec rho hrho
  exact ⟨M, fun j => hM (j + 1)⟩

theorem complex_operator_endpoint_twentyFive
    (R : H →L[ℂ] H) (L : E →L[ℂ] H)
    (hcomparison : ∀ v : H, ‖R v‖ ^ 2 ≤
      ‖ContinuousLinearMap.adjoint R v‖ ^ 2 + ‖ContinuousLinearMap.adjoint L v‖ ^ 2)
    (hobs1 : ‖R.comp L‖ ^ 2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖(R ^ (j + 2)).comp L‖ ^ 2 ≤ (121 / 4 : ℝ) * (223 / 10 : ℝ) ^ j)
    (hspec : spectralRadius ℂ (ContinuousLinearMap.adjoint R) ≤ ENNReal.ofReal (Real.sqrt (223 / 10))) :
    1 + ‖R‖ ^ 2 ≤ 25 := by
  have hb := complex_operator_norm_sq_le_of_spectralRadius R L
    (B := 121 / 4) (K := 223 / 10) (s := 24)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hcomparison hobs1 hobs hspec
  linarith

theorem complex_operator_endpoint_twentyFour886
    (R : H →L[ℂ] H) (L : E →L[ℂ] H)
    (hcomparison : ∀ v : H, ‖R v‖ ^ 2 ≤
      ‖ContinuousLinearMap.adjoint R v‖ ^ 2 + ‖ContinuousLinearMap.adjoint L v‖ ^ 2)
    (hobs1 : ‖R.comp L‖ ^ 2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖(R ^ (j + 2)).comp L‖ ^ 2 ≤ (121 / 4 : ℝ) * (2221 / 100 : ℝ) ^ j)
    (hspec : spectralRadius ℂ (ContinuousLinearMap.adjoint R) ≤ ENNReal.ofReal (Real.sqrt (2221 / 100))) :
    1 + ‖R‖ ^ 2 ≤ (12443 / 500 : ℝ) := by
  have hb := complex_operator_norm_sq_le_of_spectralRadius R L
    (B := 121 / 4) (K := 2221 / 100) (s := 11943 / 500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hcomparison hobs1 hobs hspec
  linarith

#print axioms complex_operator_norm_sq_le_of_spectralRadius
#print axioms complex_operator_endpoint_twentyFive
#print axioms complex_operator_endpoint_twentyFour886
end KLSBelow25
