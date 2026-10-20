import Mathlib

/-! Finite coefficients for an actual smooth near-Gaussian counterexample
to E||e_T||² <= Lambda(Qhalf,Qhalf)-N. The source/target cutoff,
log-concavity, whitening and positive-perturbation realization are paper
proofs and are not formalized here. No current response gate is refuted. -/
namespace KLSConstantImprovement.SmoothTraceGramNormalizationObstructionScalar

theorem trace_and_gram_coefficients :
    (36+4:ℝ)=40 ∧ (10+18+2*Real.sqrt 20:ℝ)=28+4*Real.sqrt 5 := by
  have h5 := Real.sqrt_nonneg (5:ℝ)
  have h20 := Real.sqrt_nonneg (20:ℝ)
  have hs5 := Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
  have hs20 := Real.sq_sqrt (show (0:ℝ)≤20 by norm_num)
  constructor
  · norm_num
  · have h : Real.sqrt (20:ℝ)=2*Real.sqrt 5 := by nlinarith
    rw [h]
    ring

theorem positive_smooth_comparison_gap : (0:ℝ)<40-(28+4*Real.sqrt 5) := by
  have hp := Real.sqrt_nonneg (5:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
  nlinarith

theorem positive_gram_gap_coefficient : (0:ℝ)<(28+4*Real.sqrt 5)-32 := by
  have hp := Real.sqrt_nonneg (5:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
  nlinarith

end KLSConstantImprovement.SmoothTraceGramNormalizationObstructionScalar
#print axioms KLSConstantImprovement.SmoothTraceGramNormalizationObstructionScalar.trace_and_gram_coefficients
#print axioms KLSConstantImprovement.SmoothTraceGramNormalizationObstructionScalar.positive_smooth_comparison_gap
#print axioms KLSConstantImprovement.SmoothTraceGramNormalizationObstructionScalar.positive_gram_gap_coefficient
