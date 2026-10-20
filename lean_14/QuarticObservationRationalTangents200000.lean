import ActualCorrelatedQuarticTangentCaps200000

/-! Rational polynomial parameters give exact tangent data.  At rational
t, all quantities on the right are rational and require no numerical
evaluation of the implicit inverse branch. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set
namespace KLSBelow25.QuarticCreation200000

theorem seedPhi_polynomial_parameter {t : ℝ} (ht : 0 ≤ t) (hT : t < seedT) :
    seedPhi (t^2*(seedV t)^2) = 1-t^2 := by
  have hp : RadicalBarrier.parameter (1-t^2) = t := by
    unfold RadicalBarrier.parameter
    rw [sub_sub_cancel, Real.sqrt_sq ht]
  apply seedInverseBarrier.phi_eq_of_root
  · change 1-t^2 ∈ Ioo (1-seedT^2) 2
    have hsq : t^2 < seedT^2 := by nlinarith [seedT_range.1]
    exact ⟨by linarith, by nlinarith [sq_nonneg t]⟩
  · change RadicalBarrier.value seedV (1-t^2) = t^2*(seedV t)^2
    simp only [RadicalBarrier.value, hp, sub_sub_cancel]

theorem seedParameter_polynomial_parameter {t : ℝ} (ht : 0 ≤ t) (hT : t < seedT) :
    seedParameter (t^2*(seedV t)^2) = t := by
  rw [seedParameter, seedPhi_polynomial_parameter ht hT]
  unfold RadicalBarrier.parameter
  rw [sub_sub_cancel, Real.sqrt_sq ht]

theorem deriv_seedPhi_polynomial_parameter {t : ℝ} (ht : 0 ≤ t) (hT : t < seedT)
    (hu : t^2*(seedV t)^2 ≤ 1) :
    deriv seedPhi (t^2*(seedV t)^2) = (-(seedV t*seedSlope t))⁻¹ := by
  have hm : t^2*(seedV t)^2 ∈ Icc (0 : ℝ) 1 := ⟨by positivity, hu⟩
  rw [(hasDerivAt_seedPhi hm).deriv, seedParameter_polynomial_parameter ht hT]

end KLSBelow25.QuarticCreation200000
#print axioms KLSBelow25.QuarticCreation200000.seedPhi_polynomial_parameter
#print axioms KLSBelow25.QuarticCreation200000.deriv_seedPhi_polynomial_parameter
