import Mathlib

/- Scalar consequences of an original common-field identity. The joint-H
regression, the same Poisson/Stein pairing and the actual marginal comparison
are explicit premises, not an unconditional original-law Lean bridge. -/

namespace KLSConstantImprovement.OriginalCombinedMainCancellationScalar

theorem combined_pairing_cancellation
    (cR yPair ePair : ℝ) (hreg : yPair = ePair - cR / 2) :
    3 * cR + 6 * yPair = 6 * ePair := by
  linarith

theorem affine_error_energy_paid
    (c y delta d e : ℝ) (hreg : e = y + c / 4)
    (hpaid : c + 4 * delta + 4 * y ≤ (8 / 3 : ℝ) * d) :
    e ≤ (2 / 3 : ℝ) * d - delta := by
  linarith

theorem combined_projected_pairing_square
    (p e d delta energy : ℝ) (henergy : 0 ≤ energy)
    (he : e ≤ (2 / 3 : ℝ) * d - delta)
    (hcauchy : p ^ 2 ≤ 36 * e * energy) :
    p ^ 2 ≤ (24 * d - 36 * delta) * energy := by
  have hm := mul_le_mul_of_nonneg_right he henergy
  nlinarith

theorem diagonal_hessian_consumption
    (V a b sDiag sOff correction curvature core : ℝ)
    (hid : V = 2 * a + 2 * b - sDiag - sOff + correction - curvature)
    (hdiag : 2 * a - sDiag ≤ core) :
    V ≤ core + 2 * b - sOff + correction - curvature := by
  linarith

#print axioms KLSConstantImprovement.OriginalCombinedMainCancellationScalar.combined_pairing_cancellation
#print axioms KLSConstantImprovement.OriginalCombinedMainCancellationScalar.affine_error_energy_paid
#print axioms KLSConstantImprovement.OriginalCombinedMainCancellationScalar.combined_projected_pairing_square
#print axioms KLSConstantImprovement.OriginalCombinedMainCancellationScalar.diagonal_hessian_consumption

end KLSConstantImprovement.OriginalCombinedMainCancellationScalar
