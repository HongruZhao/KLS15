import KLSConstantImprovement.OriginalSourceWeightedTraceCost
import KLSConstantImprovement.SourceResponseSevenHalvesConditionalPayoff

/-! The correlation-aware trace-cost target suffices for raw336.
The actual same-source Riesz representation, variance split, projection
and paid main/disk identifications remain explicit. The numerical cost
bound C_e <= 3(p3+gamma3)/2 is OPEN. No universal endpoint is asserted. -/
noncomputable section
namespace KLSConstantImprovement.SourceCorrelatedTraceCostConditionalPayoff

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem correlated_cost_response_cap (f : E) (b : F) (r : E → F)
    {C K N : ℝ}
    (hcontract : ∀ v, ‖r v‖ ≤ ‖v‖)
    (hrep : ∀ v, inner ℝ f v = inner ℝ b (r v))
    (hcost : ‖b‖^2 = C)
    (hcorrelated : C ≤ (3/2 : ℝ) * K)
    (hdisk : K ≤ (1 + Real.sqrt 2) * N) :
    ‖f‖^2 ≤ (3/2 : ℝ) * (1 + Real.sqrt 2) * N := by
  have h := OriginalSourceWeightedTraceCost.same_response_le_weighted_trace_cost
    f b r hcontract hrep hcost
  nlinarith

theorem correlated_cost_exact_raw_cap (a f : E) {V J N : ℝ}
    (hvariance : V = 9 * ‖a + f‖^2)
    (hprojection : ‖a‖^2 ≤ J)
    (hmain : J ≤ (9 + 6 * Real.sqrt 2) * N)
    (hresponse : ‖f‖^2 ≤ (3/2 : ℝ) * (1 + Real.sqrt 2) * N) :
    V ≤ ((1287 + 975 * Real.sqrt 2)/8) * N := by
  have h := SourceResponseSevenHalvesConditionalPayoff.source_split_rational_young a f
  nlinarith

theorem correlated_cost_cap_lt_three_thirty_six :
    ((1287 + 975 * Real.sqrt (2:ℝ))/8) < 336 := by
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  nlinarith

theorem same_source_correlated_cost_gives_raw336
    (a f : E) (b : F) (r : E → F) {C K V J N : ℝ}
    (hN : 0 ≤ N)
    (hcontract : ∀ v, ‖r v‖ ≤ ‖v‖)
    (hrep : ∀ v, inner ℝ f v = inner ℝ b (r v))
    (hcost : ‖b‖^2 = C)
    (hcorrelated : C ≤ (3/2 : ℝ) * K)
    (hdisk : K ≤ (1 + Real.sqrt 2) * N)
    (hvariance : V = 9 * ‖a + f‖^2)
    (hprojection : ‖a‖^2 ≤ J)
    (hmain : J ≤ (9 + 6 * Real.sqrt 2) * N) :
    V ≤ 336 * N := by
  have hf := correlated_cost_response_cap f b r hcontract hrep hcost hcorrelated hdisk
  have hv := correlated_cost_exact_raw_cap a f hvariance hprojection hmain hf
  exact hv.trans (mul_le_mul_of_nonneg_right correlated_cost_cap_lt_three_thirty_six.le hN)

end KLSConstantImprovement.SourceCorrelatedTraceCostConditionalPayoff
#print axioms KLSConstantImprovement.SourceCorrelatedTraceCostConditionalPayoff.correlated_cost_response_cap
#print axioms KLSConstantImprovement.SourceCorrelatedTraceCostConditionalPayoff.correlated_cost_exact_raw_cap
#print axioms KLSConstantImprovement.SourceCorrelatedTraceCostConditionalPayoff.correlated_cost_cap_lt_three_thirty_six
#print axioms KLSConstantImprovement.SourceCorrelatedTraceCostConditionalPayoff.same_source_correlated_cost_gives_raw336
