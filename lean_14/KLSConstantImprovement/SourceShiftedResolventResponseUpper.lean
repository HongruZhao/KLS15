import KLSConstantImprovement.SourceRetainedLossResponseConditionalPayoff

/-! Finite consequences of the actual regular-source shifted resolvent.
The bounded Dirichlet-form resolvent, matched BL spectral estimate,
positive production pairing, scalar response and literal cubic bindings
are independently reviewed paper proofs, explicit in these signatures.
This module does not formalize those analytic bindings or a new original
Poincare endpoint. The stronger retained production is not discarded. -/
noncomputable section
namespace KLSConstantImprovement.SourceShiftedResolventResponseUpper

theorem retained_response_production
    {i m force prod w r z xi skew loss curv : ℝ}
    (hResponse : i ≤ m-skew-loss-curv)
    (hMetric : m = 2*force-prod)
    (hForcing : 2*force ≤ w+r+z/2)
    (hProduction : xi/2 ≤ prod) :
    i ≤ w+r+z/2-xi/2-skew-loss-curv := by
  linarith

theorem coarse_same_response_cap
    {i w r z xi skew loss curv N : ℝ}
    (hN : 0 ≤ N)
    (hResponse : i ≤ w+r+z/2-xi/2-skew-loss-curv)
    (hKernel : w ≤ 3*(1+Real.sqrt 2)*N)
    (hMean : r ≤ 2*N) (hDisk : z ≤ N)
    (hXi : 0 ≤ xi) (hSkew : 0 ≤ skew)
    (hLoss : 0 ≤ loss) (hCurv : 0 ≤ curv) :
    i ≤ (11/2+3*Real.sqrt 2)*N := by
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem literal_cubic_raw480 (a f : E) {V J N : ℝ}
    (hN : 0 ≤ N) (hVariance : V = 9*‖a+f‖^2)
    (hProjection : ‖a‖^2 ≤ J)
    (hMain : J ≤ (9+6*Real.sqrt 2)*N)
    (hResponse : ‖f‖^2 ≤ (11/2+3*Real.sqrt 2)*N) :
    V ≤ 480*N := by
  have hc : inner ℝ a f ≤ ‖a‖*‖f‖ :=
    (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hy := sq_nonneg (3*‖a‖-4*‖f‖)
  have hYoung : 9*‖a+f‖^2 ≤ (63/4:ℝ)*‖a‖^2+21*‖f‖^2 := by
    rw [norm_add_sq_real]
    nlinarith
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hu : Real.sqrt (2:ℝ) ≤ 99/70 := by nlinarith
  have hpay := mul_le_mul_of_nonneg_right hu hN
  nlinarith

end KLSConstantImprovement.SourceShiftedResolventResponseUpper

#print axioms KLSConstantImprovement.SourceShiftedResolventResponseUpper.retained_response_production
#print axioms KLSConstantImprovement.SourceShiftedResolventResponseUpper.coarse_same_response_cap
#print axioms KLSConstantImprovement.SourceShiftedResolventResponseUpper.literal_cubic_raw480
