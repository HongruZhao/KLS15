import Mathlib

/-! Scalar reductions for the retained Hessian moment estimates.
All PDE, interpolation, and whole-cubic residual inputs remain explicit
hypotheses. These theorems alone do not assert a universal cubic cap.
-/
noncomputable section
namespace KLSConstantImprovement.HessianMomentScalar
set_option maxHeartbeats 2000000

theorem directional_factor (t : ℝ) :
    64/9 - 6*(1-t^2)*(1+t) = (t-1/3)^2*(6*t+10) := by ring

theorem directional_third_moment {m₂ m₃ t : ℝ}
    (ht : 0 ≤ t) (h₂ : t^2=1-m₂/2)
    (h₃ : m₃ ≤ 3*m₂*(1+t)) : m₃ ≤ 64/9 := by
  have h := mul_nonneg (sq_nonneg (t-1/3)) (show 0 ≤ 6*t+10 by linarith)
  rw [← directional_factor] at h
  nlinarith

theorem projection_third_moment {r m₂ m₃ s : ℝ}
    (hr : 0 ≤ r) (_hs : 0 ≤ s)
    (hcircle : (m₂-r)^2+s^2 ≤ r^2)
    (h₃ : m₃ ≤ 3*(m₂+s)) : m₃ ≤ 3*(1+Real.sqrt 2)*r := by
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt₂ : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hproduct : 0 ≤ Real.sqrt 2*r := mul_nonneg hsqrt hr
  have hpair : (m₂-r+s)^2 ≤ 2*r^2 := by
    nlinarith [sq_nonneg (m₂-r-s)]
  have hsum : m₂-r+s ≤ Real.sqrt 2*r := by
    by_contra hh
    have hp : 0 < m₂-r+s := by linarith
    have hmul := mul_pos (sub_pos.mpr (lt_of_not_ge hh))
      (show 0 < m₂-r+s+Real.sqrt 2*r by linarith)
    nlinarith
  nlinarith

theorem third_sandwich_absorption {M Q C : ℝ}
    (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (hpde : M ≤ 4*C) (hinterpolation : C^3 ≤ 2*Q^2*M) :
    M ≤ 8*Real.sqrt 2*Q := by
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt₂ : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hcubed : M^3 ≤ (4*C)^3 := (pow_le_pow_left₀ hM hpde 3)
  have hsq : M^2 ≤ 128*Q^2 := by
    by_cases hzero : M=0
    · rw [hzero]
      nlinarith [sq_nonneg Q]
    · have hpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
      nlinarith
  have hboundpos : 0 ≤ 8*Real.sqrt 2*Q := by positivity
  by_contra hh
  have hmul := mul_pos (sub_pos.mpr (lt_of_not_ge hh))
    (show 0 < M+8*Real.sqrt 2*Q by linarith)
  nlinarith

theorem affine_trace_charge {N W J : ℝ}
    (hN : 0 ≤ N) (hW : W ≤ 8*Real.sqrt 2*N)
    (hJ : J ≤ (1+Real.sqrt 2)*W) : J ≤ (16+8*Real.sqrt 2)*N := by
  have hfactor : 0 ≤ 1+Real.sqrt 2 := by positivity
  have h := mul_le_mul_of_nonneg_left hW hfactor
  have hsqrt₂ : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem affine_trace_coefficient_lt_poisson_target :
    (16+8*Real.sqrt 2 : ℝ) < 112/3 := by
  have h₂ := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h₀ := Real.sqrt_nonneg (2:ℝ)
  nlinarith

theorem residual_ninety_gives_cubic336 {N V J : ℝ}
    (hN : 0 ≤ N) (hJ : J ≤ (16+8*Real.sqrt 2)*N)
    (hresidual : V-9*J ≤ 90*N) : V ≤ 336*N := by
  have h₂ := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h₀ := Real.sqrt_nonneg (2:ℝ)
  have hcoef : (234+72*Real.sqrt 2 : ℝ) < 336 := by nlinarith
  have h := mul_le_mul_of_nonneg_right hcoef.le hN
  nlinarith

theorem centered_exponential_calibration :
    (216 : ℝ)-9*14=90 ∧ (6 : ℝ) ≤ 8*Real.sqrt 2 := by
  constructor
  · norm_num
  · have h₂ := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have h₀ := Real.sqrt_nonneg (2:ℝ)
    nlinarith

end KLSConstantImprovement.HessianMomentScalar
#print axioms KLSConstantImprovement.HessianMomentScalar.directional_factor
#print axioms KLSConstantImprovement.HessianMomentScalar.directional_third_moment
#print axioms KLSConstantImprovement.HessianMomentScalar.projection_third_moment
#print axioms KLSConstantImprovement.HessianMomentScalar.third_sandwich_absorption
#print axioms KLSConstantImprovement.HessianMomentScalar.affine_trace_charge
#print axioms KLSConstantImprovement.HessianMomentScalar.affine_trace_coefficient_lt_poisson_target
#print axioms KLSConstantImprovement.HessianMomentScalar.residual_ninety_gives_cubic336
#print axioms KLSConstantImprovement.HessianMomentScalar.centered_exponential_calibration
