import Mathlib

/-! Same actual response chi/F source-curvature charge. The literal
product/adjoint/Gram/domain inputs are analytic, not hidden axioms.
No dimension-free numerical response cap is concluded. -/
namespace ResponseFunctionPairedCurvatureCharge

theorem positive_generator_Gram_compensation
    (g m n : ℝ) (hgram : 0 ≤ g + 16 * m + 8 * n) :
    g + 8 * m + 4 * n ≥ g / 2 := by
  linarith

theorem source_curvature_charge_eq
    (ch p g n kh m s : ℝ)
    (hchain : ch = p + g - 2 * kh + 2 * (m + s) + 4 * n)
    (hadjoint : kh = m + s + n) :
    ch = p + g + 2 * n := by
  linarith

theorem source_curvature_Gram_bound
    (ch p g n m : ℝ) (hid : ch = p + g + 2 * n)
    (hgram : 0 ≤ g + 4 * m + 4 * n) :
    g + 2 * p ≤ 2 * ch + 4 * m := by
  linarith

theorem retains_same_source_metric_production
    (ch p g n kh m s : ℝ)
    (hid : ch = p + g + 2 * n)
    (hadjoint : kh = m + s + n) :
    m = kh - ch / 2 + (p + g) / 2 - s := by
  linarith

end ResponseFunctionPairedCurvatureCharge

#print axioms ResponseFunctionPairedCurvatureCharge.positive_generator_Gram_compensation
#print axioms ResponseFunctionPairedCurvatureCharge.source_curvature_charge_eq
#print axioms ResponseFunctionPairedCurvatureCharge.source_curvature_Gram_bound
#print axioms ResponseFunctionPairedCurvatureCharge.retains_same_source_metric_production
