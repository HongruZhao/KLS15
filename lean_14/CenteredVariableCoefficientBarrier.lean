import CenteredScalarTerminalNormalization
import VariableCoefficientBarrier

/-! A scalar generator parameter may be chosen independently at each
maximizing energy ratio. No regularity of this parameter is required: it is
never differentiated. Only the actual barrier phi is varied. -/
noncomputable section
open Set
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

 structure CenteredVariableCoefficientInductionBarrier (k : ℕ) (h : ℕ → ℝ) where
  phi : ℝ → ℝ
  alpha : ℝ → ℝ
  continuous : ContinuousOn phi (Icc 0 1)
  positive : ∀ u ∈ Icc (0 : ℝ) 1, 0 < phi u
  antitone : AntitoneOn phi (Icc (0 : ℝ) 1)
  concave : ConcaveOn ℝ (Icc 0 1) phi
  hasDeriv : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt phi (deriv phi u) u
  derivative_negative : ∀ u ∈ Icc (0 : ℝ) 1, deriv phi u < 0
  zero : phi 0 = 1
  alpha_unit : ∀ u ∈ Icc (0 : ℝ) 1, alpha u ∈ Ioo (0 : ℝ) 1
  criterion : ∀ u ∈ Icc (0 : ℝ) 1,
    (-deriv phi u/phi u)*(alpha u*h (k+1)/h k*phi u-
      ((4/(1-alpha u)-2)*(k : ℝ)^2+((4/(1-alpha u)-2)-3)*k+1)*u-
      2*actualLowerConvolution h k/Real.sqrt (h k)*Real.sqrt u) >
      2*(k+1 : ℝ)^2-(k+1 : ℝ)+1+
        2*actualLowerConvolution h (k+1)/Real.sqrt (h (k+1)*phi u)

 theorem CenteredVariableCoefficientInductionBarrier.q_positive {k : ℕ} {h : ℕ → ℝ}
    (b : CenteredVariableCoefficientInductionBarrier k h) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 < -deriv b.phi u/b.phi u :=
  div_pos (neg_pos.mpr (b.derivative_negative u hu)) (b.positive u hu)


end KLS.DeterministicBridgeNext
