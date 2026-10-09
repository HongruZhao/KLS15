import ScalarBootstrapNormalization
import ResolventOperatorEndgame

/-! The improved numerical scalar endgame, under the same operator comparison
and unchanged actual coefficient-observation envelope. -/
noncomputable section
open InnerProductSpace AdjointOrbitRecurrence
namespace KLSBelow25
variable {𝕜 H E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

theorem operator_norm_sq_le_of_scalar_orbit_bound
    (R : H →L[𝕜] H) (L : E →L[𝕜] H)
    {B K s : ℝ} (hs : 0 < s)
    (hscalarBound : ∀ u : ℕ → ℝ, (u 1^2-2 ≤ u 2) →
      (∀ j : ℕ, 0 < u (j+1) → 0 < u (j+2) →
        u (j+2)^2/u (j+1)-B*K^j ≤ u (j+3)) →
      (∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ j : ℕ,
        u (j+1) ≤ M*(K*rho)^(j+1)) → u 1 ≤ s)
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
    apply hscalarBound (energy R f)
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

theorem operator_norm_sq_le_248764_of_power_envelope
    (R : H →L[𝕜] H) (L : E →L[𝕜] H)
    (hcomparison : ∀ v : H, ‖R v‖ ^ 2 ≤
      ‖ContinuousLinearMap.adjoint R v‖ ^ 2 + ‖ContinuousLinearMap.adjoint L v‖ ^ 2)
    (hobs1 : ‖R.comp L‖ ^ 2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖(R ^ (j + 2)).comp L‖ ^ 2 ≤ (121/4 : ℝ)*(2221/100 : ℝ)^j)
    (henvelope : ∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ j : ℕ,
      ‖(ContinuousLinearMap.adjoint R) ^ (j+1)‖^2 ≤ M*((2221/100 : ℝ)*rho)^(j+1)) :
    ‖R‖^2 ≤ (59691/2500 : ℝ) := by
  exact operator_norm_sq_le_of_scalar_orbit_bound R L (by norm_num)
    scalar_orbit_bound_248764 hcomparison hobs1 hobs henvelope

section Complex
variable {H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
open ContinuousLinearMap

theorem complex_operator_norm_sq_le_248764_of_spectralRadius
    (R : H →L[ℂ] H) (L : E →L[ℂ] H)
    (hcomparison : ∀ v : H, ‖R v‖^2 ≤ ‖R.adjoint v‖^2+‖L.adjoint v‖^2)
    (hobs1 : ‖R.comp L‖^2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖(R^(j+2)).comp L‖^2 ≤ (121/4 : ℝ)*(2221/100 : ℝ)^j)
    (hspec : spectralRadius ℂ R.adjoint ≤ ENNReal.ofReal (Real.sqrt (2221/100))) :
    ‖R‖^2 ≤ (59691/2500 : ℝ) := by
  apply operator_norm_sq_le_248764_of_power_envelope R L hcomparison hobs1 hobs
  intro rho hrho
  obtain ⟨M,hM⟩ := squared_power_envelope_of_spectralRadius_le
    R.adjoint (by norm_num : 0 < (2221/100 : ℝ)) hspec rho hrho
  exact ⟨M, fun j => hM (j+1)⟩

theorem resolvent_operator_endpoint_twentyFour8764
    (R : H →L[ℂ] H) (L : E →L[ℂ] H) (U : H →L[ℂ] H)
    {a : ℝ} (ha : 0 < a)
    (hU : (1+a • integrationGram R L)*U = 1)
    (hcomparison : ∀ v : H, ‖R v‖^2 ≤ Complex.re ⟪(a⁻¹ • (1-U)) v,v⟫_ℂ)
    (hobs1 : ‖R.comp L‖^2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖(R^(j+2)).comp L‖^2 ≤ (121/4 : ℝ)*(2221/100 : ℝ)^j) :
    1+‖R‖^2 ≤ (62191/2500 : ℝ) := by
  rcases subsingleton_or_nontrivial H with hsub | hn
  · have hR : R = 0 := Subsingleton.elim _ _
    norm_num [hR]
  · have hlinear := linear_curvature_comparison_of_resolvent R L U ha hU hcomparison
    have hscalar := scalar_curvature_comparison_of_resolvent R L U ha hU hcomparison
    have hspec : spectralRadius ℂ R.adjoint ≤ ENNReal.ofReal (Real.sqrt (2221/100)) := by
      apply spectralRadius_le_of_scalar_comparison R.adjoint L.adjoint ha (by norm_num) 2
      · simpa only [adjoint_adjoint] using hscalar
      · intro m hm
        have he : m-2+2=m := Nat.sub_add_cancel hm
        calc
          ‖L.adjoint.comp (R.adjoint^m)‖^2 = ‖(R^m).comp L‖^2 := by
            rw [AdjointOrbitRecurrence.observation_adjoint_norm]
          _ ≤ (121/4 : ℝ)*(2221/100 : ℝ)^(m-2) := by
            simpa only [he] using hobs (m-2)
          _ = ((121/4 : ℝ)/(2221/100 : ℝ)^2)*(2221/100 : ℝ)^m := by
            rw [← he,pow_add]
            norm_num
            ring
    have hb := complex_operator_norm_sq_le_248764_of_spectralRadius R L hlinear hobs1 hobs hspec
    linarith
end Complex

#print axioms operator_norm_sq_le_of_scalar_orbit_bound
#print axioms operator_norm_sq_le_248764_of_power_envelope
#print axioms complex_operator_norm_sq_le_248764_of_spectralRadius
#print axioms resolvent_operator_endpoint_twentyFour8764
end KLSBelow25
