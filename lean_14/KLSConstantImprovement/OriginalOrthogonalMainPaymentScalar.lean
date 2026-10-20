import Mathlib

/-! Retain diagonal/off-diagonal orthogonality before paying the regression
correction. The original ODECO joint-kernel and same-response bridge remains
an analytic input; this file proves the Hilbert and scalar deductions only. -/

noncomputable section
namespace KLSConstantImprovement.OriginalOrthogonalMainPaymentScalar

theorem orthogonal_three_term_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (core off correction : E) (core2 off2 correctionRoot : ℝ)
    (horth : inner ℝ core off = 0)
    (hcore : ‖core‖ ^ 2 ≤ core2) (hoff : ‖off‖ ^ 2 ≤ off2)
    (hcorr : ‖correction‖ ≤ correctionRoot) :
    ‖core + off + (3 / 2 : ℝ) • correction‖ ≤
      Real.sqrt (core2 + off2) + (3 / 2 : ℝ) * correctionRoot := by
  have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero core off horth
  have hnonneg : 0 ≤ core2 + off2 := by
    nlinarith [sq_nonneg ‖core‖, sq_nonneg ‖off‖]
  have hsum : ‖core + off‖ ≤ Real.sqrt (core2 + off2) := by
    nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg (core2 + off2),
      norm_nonneg (core + off)]
  calc
    ‖core + off + (3 / 2 : ℝ) • correction‖ ≤
        ‖core + off‖ + ‖(3 / 2 : ℝ) • correction‖ := norm_add_le _ _
    _ = ‖core + off‖ + (3 / 2 : ℝ) * ‖correction‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      norm_num
    _ ≤ Real.sqrt (core2 + off2) + (3 / 2 : ℝ) * correctionRoot := by
      linarith

theorem orthogonal_full_main_critical_norm
    (mainRoot coreRoot off2 correctionRoot r : ℝ)
    (htriangle : mainRoot ≤ Real.sqrt (coreRoot ^ 2 + off2) +
      (3 / 2 : ℝ) * correctionRoot)
    (hoff : off2 ≤ 713 * Real.sqrt 2 * r ^ 2)
    (hcorr : correctionRoot ≤ 4 * r) :
    mainRoot ≤ Real.sqrt (coreRoot ^ 2 + 713 * Real.sqrt 2 * r ^ 2) +
      6 * r := by
  have hs := Real.sqrt_le_sqrt (add_le_add (le_refl (coreRoot ^ 2)) hoff)
  linarith

theorem orthogonal_bound_improves_triangle
    (coreRoot r : ℝ) (hcore : 0 ≤ coreRoot) (hr : 0 ≤ r) :
    Real.sqrt (coreRoot ^ 2 + 713 * Real.sqrt 2 * r ^ 2) + 6 * r ≤
      coreRoot + 38 * r := by
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hconst : 713 * Real.sqrt 2 ≤ 1024 := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hconst (sq_nonneg r)
  have hprod := mul_nonneg hcore hr
  have hrad : coreRoot ^ 2 + 713 * Real.sqrt 2 * r ^ 2 ≤
      (coreRoot + 32 * r) ^ 2 := by nlinarith
  have hroot := Real.sqrt_le_sqrt hrad
  rw [Real.sqrt_sq (by positivity : 0 ≤ coreRoot + 32 * r)] at hroot
  linarith

end KLSConstantImprovement.OriginalOrthogonalMainPaymentScalar
#print axioms KLSConstantImprovement.OriginalOrthogonalMainPaymentScalar.orthogonal_three_term_norm
#print axioms KLSConstantImprovement.OriginalOrthogonalMainPaymentScalar.orthogonal_full_main_critical_norm
#print axioms KLSConstantImprovement.OriginalOrthogonalMainPaymentScalar.orthogonal_bound_improves_triangle
