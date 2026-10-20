import Mathlib

/-! Exact arithmetic for the original two-exponential inverse-skew domain
guardrail. Actual Exp moments, infinite weighted norm and the noncompact
boundary identification are proved on paper and are not formalized here.
No valid compact-source null or cross identity is refuted. -/
namespace KLSConstantImprovement.InverseSkewExponentialBoundaryScalar

theorem inverse_skew_squared_coefficient :
    (24-6*6+11*2-6*1+1:ℝ)=5 ∧ (0:ℝ)<5 := by norm_num

theorem literal_and_formal_cross_disagree :
    (-6+4*2-4*1+1:ℝ)+(2-3*1+2)=0 ∧
    -(2-1*1-1*1+1*1:ℝ) = -1 ∧ (0:ℝ) ≠ -1 := by norm_num

theorem pointwise_divergence_does_not_pay_natural_pairing :
    (6-2*2+1:ℝ)=3 ∧ (0:ℝ)<3 := by norm_num

end KLSConstantImprovement.InverseSkewExponentialBoundaryScalar
#print axioms KLSConstantImprovement.InverseSkewExponentialBoundaryScalar.inverse_skew_squared_coefficient
#print axioms KLSConstantImprovement.InverseSkewExponentialBoundaryScalar.literal_and_formal_cross_disagree
#print axioms KLSConstantImprovement.InverseSkewExponentialBoundaryScalar.pointwise_divergence_does_not_pay_natural_pairing
