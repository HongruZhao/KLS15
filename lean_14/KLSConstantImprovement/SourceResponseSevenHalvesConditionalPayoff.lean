import KLSConstantImprovement.TensorGramQuarticSourceDeficit
import KLSConstantImprovement.SourceThirdAdjointResponse

/-! A conditional payoff of the paid source main bound. The actual
same-source variance split, third-adjoint projection and original-law
main identification remain analytic inputs. The full response7/2
premise is open. No unconditional variance or Poincare claim follows. -/
noncomputable section
namespace KLSConstantImprovement.SourceResponseSevenHalvesConditionalPayoff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem source_split_rational_young (a f : E) :
    9 * ‖a + f‖^2 ≤ 13 * ‖a‖^2 + (117/4 : ℝ) * ‖f‖^2 := by
  have hc : inner ℝ a f ≤ ‖a‖ * ‖f‖ :=
    (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hy := sq_nonneg ((2/3 : ℝ) * ‖a‖ - (3/2 : ℝ) * ‖f‖)
  rw [norm_add_sq_real]
  nlinarith

theorem response_seven_halves_exact_raw_cap (a f : E) {V J N : ℝ}
    (hvariance : V = 9 * ‖a + f‖^2)
    (hprojection : ‖a‖^2 ≤ J)
    (hmain : J ≤ (9 + 6 * Real.sqrt 2) * N)
    (hresponse : ‖f‖^2 ≤ (7/2 : ℝ) * N) :
    V ≤ (1755/8 + 78 * Real.sqrt 2) * N := by
  have hy := source_split_rational_young a f
  nlinarith

theorem exact_cap_lt_three_thirty :
    (1755/8 + 78 * Real.sqrt (2:ℝ)) < 330 := by
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  nlinarith

theorem response_seven_halves_gives_raw330 (a f : E) {V J N : ℝ}
    (hN : 0 ≤ N)
    (hvariance : V = 9 * ‖a + f‖^2)
    (hprojection : ‖a‖^2 ≤ J)
    (hmain : J ≤ (9 + 6 * Real.sqrt 2) * N)
    (hresponse : ‖f‖^2 ≤ (7/2 : ℝ) * N) :
    V ≤ 330 * N := by
  have h := response_seven_halves_exact_raw_cap a f
    hvariance hprojection hmain hresponse
  exact h.trans (mul_le_mul_of_nonneg_right exact_cap_lt_three_thirty.le hN)

theorem response_seven_halves_gives_cubic336 (a f : E) {V J N : ℝ}
    (hN : 0 ≤ N)
    (hvariance : V = 9 * ‖a + f‖^2)
    (hprojection : ‖a‖^2 ≤ J)
    (hmain : J ≤ (9 + 6 * Real.sqrt 2) * N)
    (hresponse : ‖f‖^2 ≤ (7/2 : ℝ) * N) :
    V ≤ 336 * N := by
  have h := response_seven_halves_gives_raw330 a f hN
    hvariance hprojection hmain hresponse
  linarith

end KLSConstantImprovement.SourceResponseSevenHalvesConditionalPayoff
#print axioms KLSConstantImprovement.SourceResponseSevenHalvesConditionalPayoff.source_split_rational_young
#print axioms KLSConstantImprovement.SourceResponseSevenHalvesConditionalPayoff.response_seven_halves_exact_raw_cap
#print axioms KLSConstantImprovement.SourceResponseSevenHalvesConditionalPayoff.exact_cap_lt_three_thirty
#print axioms KLSConstantImprovement.SourceResponseSevenHalvesConditionalPayoff.response_seven_halves_gives_raw330
#print axioms KLSConstantImprovement.SourceResponseSevenHalvesConditionalPayoff.response_seven_halves_gives_cubic336
