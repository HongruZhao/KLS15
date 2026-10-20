import ResolventOperatorComparison
import ScalarComparisonSpectralRadius
import ComplexOperatorNormEndgame

/-! Complete abstract operator endgame at25 and24.886, from the actual
positive resolvent comparison and observation bounds. No spectral-radius,
power-envelope or approximate-eigenvector hypotheses remain. Identifying
these operators with the compatible tensor maps of an actual measure is
still a separate mathematical obligation. -/
noncomputable section
namespace KLSBelow25
open ContinuousLinearMap InnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem operator_norm_sq_le_of_resolvent
    (R : H →L[ℂ] H) (L : E →L[ℂ] H) (U : H →L[ℂ] H)
    {a B K s : ℝ} (ha : 0 < a) (hB : 0 < B) (hK : 0 < K) (hs : 0 < s)
    (hDelta : 0 < s ^ 2 - K * s - 2)
    (hGap : 2 * B * s < (s ^ 2 - K * s - 2) ^ 2)
    (hU : (1 + a • integrationGram R L) * U = 1)
    (hcomparison : ∀ v : H, ‖R v‖ ^ 2 ≤
      Complex.re ⟪(a⁻¹ • (1 - U)) v, v⟫_ℂ)
    (hobs1 : ‖R.comp L‖ ^ 2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖(R ^ (j + 2)).comp L‖ ^ 2 ≤ B * K ^ j) :
    ‖R‖ ^ 2 ≤ s := by
  rcases subsingleton_or_nontrivial H with hsub | hn
  · have hR : R = 0 := Subsingleton.elim _ _
    simpa [hR] using hs.le
  · have hlinear := linear_curvature_comparison_of_resolvent R L U ha hU hcomparison
    have hscalar := scalar_curvature_comparison_of_resolvent R L U ha hU hcomparison
    have hspec : spectralRadius ℂ R.adjoint ≤ ENNReal.ofReal (Real.sqrt K) := by
      apply spectralRadius_le_of_scalar_comparison R.adjoint L.adjoint ha hK 2
      · simpa only [adjoint_adjoint] using hscalar
      · intro m hm
        have he : m - 2 + 2 = m := Nat.sub_add_cancel hm
        calc
          ‖L.adjoint.comp (R.adjoint ^ m)‖ ^ 2 = ‖(R ^ m).comp L‖ ^ 2 := by
            rw [AdjointOrbitRecurrence.observation_adjoint_norm]
          _ ≤ B * K ^ (m - 2) := by simpa only [he] using hobs (m - 2)
          _ = (B / K ^ 2) * K ^ m := by
            rw [← he, pow_add]
            field_simp <;> simp
    exact complex_operator_norm_sq_le_of_spectralRadius R L hB hK hs
      hDelta hGap hlinear hobs1 hobs hspec

theorem resolvent_operator_endpoint_twentyFive
    (R : H →L[ℂ] H) (L : E →L[ℂ] H) (U : H →L[ℂ] H)
    {a : ℝ} (ha : 0 < a)
    (hU : (1 + a • integrationGram R L) * U = 1)
    (hcomparison : ∀ v : H, ‖R v‖ ^ 2 ≤
      Complex.re ⟪(a⁻¹ • (1 - U)) v, v⟫_ℂ)
    (hobs1 : ‖R.comp L‖ ^ 2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖(R ^ (j + 2)).comp L‖ ^ 2 ≤ (121 / 4 : ℝ) * (223 / 10 : ℝ) ^ j) :
    1 + ‖R‖ ^ 2 ≤ 25 := by
  have hb := operator_norm_sq_le_of_resolvent R L U ha
    (B := 121 / 4) (K := 223 / 10) (s := 24)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hU hcomparison hobs1 hobs
  linarith

theorem resolvent_operator_endpoint_twentyFour886
    (R : H →L[ℂ] H) (L : E →L[ℂ] H) (U : H →L[ℂ] H)
    {a : ℝ} (ha : 0 < a)
    (hU : (1 + a • integrationGram R L) * U = 1)
    (hcomparison : ∀ v : H, ‖R v‖ ^ 2 ≤
      Complex.re ⟪(a⁻¹ • (1 - U)) v, v⟫_ℂ)
    (hobs1 : ‖R.comp L‖ ^ 2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖(R ^ (j + 2)).comp L‖ ^ 2 ≤ (121 / 4 : ℝ) * (2221 / 100 : ℝ) ^ j) :
    1 + ‖R‖ ^ 2 ≤ (12443 / 500 : ℝ) := by
  have hb := operator_norm_sq_le_of_resolvent R L U ha
    (B := 121 / 4) (K := 2221 / 100) (s := 11943 / 500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hU hcomparison hobs1 hobs
  linarith

#print axioms operator_norm_sq_le_of_resolvent
#print axioms resolvent_operator_endpoint_twentyFive
#print axioms resolvent_operator_endpoint_twentyFour886
end KLSBelow25
