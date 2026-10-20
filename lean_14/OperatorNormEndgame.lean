import AdjointOrbitRecurrence
import ScalarNormalization

/-! The bounded-operator norm endgame.  The every-rate power envelope is
an explicit spectral obligation.  These results do not assert existence
of the actual-law compatible tensor operators or their comparison. -/
noncomputable section
open InnerProductSpace AdjointOrbitRecurrence
namespace KLSBelow25
variable {𝕜 H E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

theorem operator_norm_sq_le_of_power_envelope
    (R : H →L[𝕜] H) (L : E →L[𝕜] H)
    {B K s : ℝ} (hB : 0 < B) (hK : 0 < K) (hs : 0 < s)
    (hDelta : 0 < s ^ 2 - K * s - 2)
    (hGap : 2 * B * s < (s ^ 2 - K * s - 2) ^ 2)
    (hcomparison : ∀ v : H, ‖R v‖ ^ 2 ≤
      ‖ContinuousLinearMap.adjoint R v‖ ^ 2 + ‖ContinuousLinearMap.adjoint L v‖ ^ 2)
    (hobs1 : ‖R.comp L‖ ^ 2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖(R ^ (j + 2)).comp L‖ ^ 2 ≤ B * K ^ j)
    (henvelope : ∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ j : ℕ,
      ‖(ContinuousLinearMap.adjoint R) ^ (j + 1)‖ ^ 2 ≤ M * (K * rho) ^ (j + 1)) :
    ‖R‖ ^ 2 ≤ s := by
  have hunit : ∀ f : H, ‖f‖ = 1 → energy R f 1 ≤ s := by
    intro f hf
    have hzero : energy R f 0 = 1 := by simp [energy, hf]
    apply scalar_orbit_bound hB hK hs hDelta hGap (energy R f)
    · have hrec := energy_recurrence_unit R L hcomparison hf 0
        (by rw [hzero]; norm_num)
      simp only [zero_add, pow_one, hzero, div_one] at hrec
      linarith [hobs1]
    · intro j hj _hj1
      have hrec := energy_recurrence_unit R L hcomparison hf (j + 1) hj
      have hob := hobs j
      simp only [show j + 1 + 1 = j + 2 by omega,
        show j + 1 + 2 = j + 3 by omega] at hrec
      linarith
    · intro rho hrho
      obtain ⟨M, hM⟩ := henvelope rho hrho
      refine ⟨M, fun j => ?_⟩
      have ho := ((ContinuousLinearMap.adjoint R) ^ (j + 1)).le_opNorm f
      rw [hf, mul_one] at ho
      have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr ho
      exact hsq.trans (hM j)
  have hnorm : ‖ContinuousLinearMap.adjoint R‖ ≤ Real.sqrt s := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro f hf
    have hu := hunit f hf
    have he : energy R f 1 = ‖ContinuousLinearMap.adjoint R f‖ ^ 2 := by
      simp [energy, orbit]
    rw [he] at hu
    exact (Real.le_sqrt (norm_nonneg _) hs.le).mpr hu
  rw [ContinuousLinearMap.adjoint.norm_map] at hnorm
  have hsq := (sq_le_sq₀ (norm_nonneg R) (Real.sqrt_nonneg s)).mpr hnorm
  rwa [Real.sq_sqrt hs.le] at hsq

theorem operator_endpoint_twentyFive
    (R : H →L[𝕜] H) (L : E →L[𝕜] H)
    (hcomparison : ∀ v : H, ‖R v‖ ^ 2 ≤
      ‖ContinuousLinearMap.adjoint R v‖ ^ 2 + ‖ContinuousLinearMap.adjoint L v‖ ^ 2)
    (hobs1 : ‖R.comp L‖ ^ 2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖(R ^ (j + 2)).comp L‖ ^ 2 ≤ (121 / 4 : ℝ) * (223 / 10 : ℝ) ^ j)
    (henvelope : ∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ j : ℕ,
      ‖(ContinuousLinearMap.adjoint R) ^ (j + 1)‖ ^ 2 ≤ M * ((223 / 10 : ℝ) * rho) ^ (j + 1)) :
    1 + ‖R‖ ^ 2 ≤ 25 := by
  have hb := operator_norm_sq_le_of_power_envelope R L
    (B := 121 / 4) (K := 223 / 10) (s := 24)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hcomparison hobs1 hobs henvelope
  linarith

theorem operator_endpoint_twentyFour886
    (R : H →L[𝕜] H) (L : E →L[𝕜] H)
    (hcomparison : ∀ v : H, ‖R v‖ ^ 2 ≤
      ‖ContinuousLinearMap.adjoint R v‖ ^ 2 + ‖ContinuousLinearMap.adjoint L v‖ ^ 2)
    (hobs1 : ‖R.comp L‖ ^ 2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖(R ^ (j + 2)).comp L‖ ^ 2 ≤ (121 / 4 : ℝ) * (2221 / 100 : ℝ) ^ j)
    (henvelope : ∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ j : ℕ,
      ‖(ContinuousLinearMap.adjoint R) ^ (j + 1)‖ ^ 2 ≤ M * ((2221 / 100 : ℝ) * rho) ^ (j + 1)) :
    1 + ‖R‖ ^ 2 ≤ (12443 / 500 : ℝ) := by
  have hb := operator_norm_sq_le_of_power_envelope R L
    (B := 121 / 4) (K := 2221 / 100) (s := 11943 / 500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hcomparison hobs1 hobs henvelope
  linarith

#print axioms operator_norm_sq_le_of_power_envelope
#print axioms operator_endpoint_twentyFive
#print axioms operator_endpoint_twentyFour886
end KLSBelow25
