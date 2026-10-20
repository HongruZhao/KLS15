import Mathlib

/-!
Fresh, uncompiled scalar stage owned by original_upper_recovery6.

This proves the rational Gram conversion used by the actual two-cone
cap8/raw216/cross36 theorem. It does not prove the actual-law moment
identification, the polynomial Bernstein/Sylvester certificates, or the
observation-map/adjoint norm transfer. Those inputs remain explicit.

The companion original-law source is
literature/original-upper-recovery6-two-cone-raw216-curvature3.md.
The exact all-parameter certificate is
constant-improvement/optimization/original_upper_recovery6_two_cone_certificate.json.

For the intended original law: a,b > 0 and a+b >= a*b; the measure is
the actual convex maximum density on the positive quadrant, or its
centered affine whitening. G22,G33,G23 are the literal original centered
quadratic/cubic variances and covariance; N2,N3 are the same-law affine
covariance tensor metrics. The theorem about an original sum below keeps
the literal variance identity and all three moment bounds as hypotheses.
No unconditional general-law conclusion is asserted by this draft.
-/

noncomputable section

namespace KLSConstantImprovement.OriginalUpperRecovery6Draft

theorem twice_cross_le_sum {A B c : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : c ^ 2 ≤ A * B) :
    2 * c ≤ A + B := by
  have hsum : 0 ≤ A + B := add_nonneg hA hB
  have hsq : (2 * c) ^ 2 ≤ (A + B) ^ 2 := by
    nlinarith [sq_nonneg (A - B)]
  by_cases hc0 : c ≤ 0
  · linarith
  · have hcpos : 0 < c := lt_of_not_ge hc0
    exact (sq_le_sq₀ (by linarith : 0 ≤ 2 * c) hsum).mp hsq

theorem support311_slack :
    ((311 : ℝ) - 8 * 14) * (311 - 216) - 1296 * 14 = 761 := by
  norm_num

theorem support1754_slack :
    ((1754 : ℝ) - 8 * 198) * (1754 - 216) - 1296 * 198 = 4852 := by
  norm_num

theorem polynomial_gram_support311
    {N2 N3 G22 G23 G33 : ℝ}
    (hN2 : 0 ≤ N2) (hN3 : 0 ≤ N3)
    (hquad : G22 ≤ 8 * N2) (hcubic : G33 ≤ 216 * N3)
    (hcross : G23 ^ 2 ≤ 1296 * N2 * N3) :
    G22 + 2 * G23 + G33 ≤ (311 / 14 : ℝ) * N2 + 311 * N3 := by
  have hpaid : G23 ^ 2 ≤ ((199 / 14 : ℝ) * N2) * (95 * N3) := by
    nlinarith [mul_nonneg hN2 hN3]
  have h2 : 2 * G23 ≤ (199 / 14 : ℝ) * N2 + 95 * N3 :=
    twice_cross_le_sum (by positivity) (by positivity) hpaid
  linarith

theorem polynomial_gram_support1754
    {N2 N3 G22 G23 G33 : ℝ}
    (hN2 : 0 ≤ N2) (hN3 : 0 ≤ N3)
    (hquad : G22 ≤ 8 * N2) (hcubic : G33 ≤ 216 * N3)
    (hcross : G23 ^ 2 ≤ 1296 * N2 * N3) :
    G22 + 2 * G23 + G33 ≤ (1754 / 198 : ℝ) * N2 + 1754 * N3 := by
  have hpaid : G23 ^ 2 ≤ ((85 / 99 : ℝ) * N2) * (1538 * N3) := by
    nlinarith [mul_nonneg hN2 hN3]
  have h2 : 2 * G23 ≤ (85 / 99 : ℝ) * N2 + 1538 * N3 :=
    twice_cross_le_sum (by positivity) (by positivity) hpaid
  linarith

/-- The original measure and original polynomial variance remain explicit.
The caller must supply the same-law metric, variance, and covariance bridge. -/
theorem original_polynomial_sum_support311
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (q P : Ω → ℝ)
    {N2 N3 G22 G23 G33 : ℝ}
    (hOriginalVariance : ProbabilityTheory.variance (fun x => q x + P x) μ =
      G22 + 2 * G23 + G33)
    (hN2 : 0 ≤ N2) (hN3 : 0 ≤ N3)
    (hquad : G22 ≤ 8 * N2) (hcubic : G33 ≤ 216 * N3)
    (hcross : G23 ^ 2 ≤ 1296 * N2 * N3) :
    ProbabilityTheory.variance (fun x => q x + P x) μ ≤
      (311 / 14 : ℝ) * N2 + 311 * N3 := by
  rw [hOriginalVariance]
  exact polynomial_gram_support311 hN2 hN3 hquad hcubic hcross

/-- This is a scalar support conversion, with the original-law bridge retained. -/
theorem original_polynomial_sum_support1754
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (q P : Ω → ℝ)
    {N2 N3 G22 G23 G33 : ℝ}
    (hOriginalVariance : ProbabilityTheory.variance (fun x => q x + P x) μ =
      G22 + 2 * G23 + G33)
    (hN2 : 0 ≤ N2) (hN3 : 0 ≤ N3)
    (hquad : G22 ≤ 8 * N2) (hcubic : G33 ≤ 216 * N3)
    (hcross : G23 ^ 2 ≤ 1296 * N2 * N3) :
    ProbabilityTheory.variance (fun x => q x + P x) μ ≤
      (1754 / 198 : ℝ) * N2 + 1754 * N3 := by
  rw [hOriginalVariance]
  exact polynomial_gram_support1754 hN2 hN3 hquad hcubic hcross

end KLSConstantImprovement.OriginalUpperRecovery6Draft

#print axioms KLSConstantImprovement.OriginalUpperRecovery6Draft.twice_cross_le_sum
#print axioms KLSConstantImprovement.OriginalUpperRecovery6Draft.polynomial_gram_support311
#print axioms KLSConstantImprovement.OriginalUpperRecovery6Draft.polynomial_gram_support1754
#print axioms KLSConstantImprovement.OriginalUpperRecovery6Draft.original_polynomial_sum_support311
#print axioms KLSConstantImprovement.OriginalUpperRecovery6Draft.original_polynomial_sum_support1754
