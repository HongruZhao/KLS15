import KLSConstantImprovement.ActualCubicMatrixFactorization405

/-! The actual cubic variance is bounded by the genuine quadratic row
matrix energy. The only remaining hypothesis here is the explicit
bounded mass of its own cubic natural inverse. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace ProbabilityTheory
open scoped BigOperators
namespace KLSConstantImprovement.ActualCubicHilbertUpper405
open KLS ActualBoundedCanonicalSource ActualCubicRepresenter
open ActualCubicSourceDatum405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualQuadraticHilbertMatrix405 ActualCubicMatrixFactorization405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem six_pairing_upper (u w : E) {v : ℝ} (hw : ‖w‖ ^ 2 ≤ v)
    (hv : v = 6 * inner ℝ u w) : v ≤ 36 * ‖u‖ ^ 2 := by
  have hnonneg : 0 ≤ v := (sq_nonneg ‖w‖).trans hw
  have hc := real_inner_le_norm u w
  have hlin : v ≤ 6 * ‖u‖ * ‖w‖ := by nlinarith only [hc, hv]
  have hs := pow_le_pow_left₀ hnonneg hlin 2
  have hp := mul_le_mul_of_nonneg_left hw (show 0 ≤ 36 * ‖u‖ ^ 2 by positivity)
  by_cases hz : v = 0
  · rw [hz]; positivity
  · have hvpos : 0 < v := lt_of_le_of_ne hnonneg (Ne.symm hz)
    nlinarith only [hs, hp, hvpos]

theorem split_three_fifths_young (a f : E) :
    9 * ‖a + f‖ ^ 2 ≤ (72 / 5 : ℝ) * ‖a‖ ^ 2 + 24 * ‖f‖ ^ 2 := by
  have hc := real_inner_le_norm a f
  have hy := sq_nonneg (3 * ‖a‖ - 5 * ‖f‖)
  rw [norm_add_sq_real]
  nlinarith only [hc, hy]

theorem six_pairing_split_upper (u a f w : E) {v : ℝ}
    (hw : ‖w‖ ^ 2 ≤ v) (hv : v = 6 * inner ℝ u w)
    (hf : a + f = (2 : ℝ) • u) :
    v ≤ (72 / 5 : ℝ) * ‖a‖ ^ 2 + 24 * ‖f‖ ^ 2 := by
  have hwhole := six_pairing_upper u w hw hv
  have hy := split_three_fifths_young a f
  rw [hf, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hy
  nlinarith only [hwhole, hy]
end Hilbert

theorem actual_cubic_variance_le_whole_matrix_of_mass_bound (d : SourceData μ)
    (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (actualCubicDatum d T)) x ≤ C) :
    variance (tensorPolynomial μ T) μ ≤
      36 * ∫ x, actualQuadraticMatrixCost d T x ∂potentialMeasure d.potential := by
  obtain ⟨W, hW, hv⟩ := exists_actual_cubic_matrix_pairing_of_mass_bound d hn hμ T hT12 hT23 hC hM
  have hp := six_pairing_upper (actualQuadraticHilbert d T) W hW hv
  rwa [actualQuadraticHilbert_norm] at hp

end KLSConstantImprovement.ActualCubicHilbertUpper405
#print axioms KLSConstantImprovement.ActualCubicHilbertUpper405.six_pairing_upper
#print axioms KLSConstantImprovement.ActualCubicHilbertUpper405.split_three_fifths_young
#print axioms KLSConstantImprovement.ActualCubicHilbertUpper405.actual_cubic_variance_le_whole_matrix_of_mass_bound
