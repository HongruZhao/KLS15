import KLSConstantImprovement.TensorGramQuarticSourceDeficit

/-! A sufficient Rayleigh estimate for the literal canonical cubic.
The SAME actual polynomial, geometric closed operator, weighted Bochner,
and Cauchy bindings are analytic inputs. The Rayleigh49/25 premise is
OPEN universally. No higher source gap for arbitrary functions or Hessian
fields is asserted, and no unconditional raw336 or Poincare claim follows. -/
noncomputable section
namespace KLSConstantImprovement.RelaxedLiteralCubicRayleighPayoff

theorem variance_from_relaxed_rayleigh {V energy operatorSq J : ℝ}
    (hV : 0 ≤ V) (hJ : 0 ≤ J)
    (hbochner : operatorSq=energy+36*J)
    (hcauchy : energy^2 ≤ V*operatorSq)
    (hrayleigh : (49/25:ℝ)*V ≤ energy) :
    V ≤ (1875/98:ℝ)*J := by
  by_cases hz : V=0
  · rw [hz]
    positivity
  have hp : 0 < V := lt_of_le_of_ne hV (Ne.symm hz)
  have he : 0 ≤ energy+(24/25:ℝ)*V := by linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hrayleigh) he
  have hsq : energy^2 ≤ V*(energy+36*J) := by
    simpa [hbochner] using hcauchy
  by_contra h
  have hbad : (1875/98:ℝ)*J < V := lt_of_not_ge h
  have hstrict := mul_pos hp (sub_pos.mpr hbad)
  nlinarith

theorem rational_trace_support {N J q : ℝ}
    (hN : 0 ≤ N) (hq : 0 ≤ q)
    (hmain : Real.sqrt 2*J+q ≤ (12+9*Real.sqrt 2)*N) :
    J ≤ (612/35:ℝ)*N := by
  have hcap := TensorGramQuarticSourceDeficit.affine_trace_disk_cap hq hmain
  have hs := Real.sqrt_nonneg (2:ℝ)
  have hs2 : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hup : Real.sqrt (2:ℝ) ≤ 99/70 := by nlinarith
  have hscaled := mul_nonneg hN (sub_nonneg.mpr hup)
  nlinarith

theorem conditional_raw_cubic_cap {N V energy operatorSq J q : ℝ}
    (hN : 0 ≤ N) (hV : 0 ≤ V) (hJ : 0 ≤ J) (hq : 0 ≤ q)
    (hmain : Real.sqrt 2*J+q ≤ (12+9*Real.sqrt 2)*N)
    (hbochner : operatorSq=energy+36*J)
    (hcauchy : energy^2 ≤ V*operatorSq)
    (hrayleigh : (49/25:ℝ)*V ≤ energy) :
    V ≤ (114750/343:ℝ)*N ∧ V ≤ 336*N := by
  have hv := variance_from_relaxed_rayleigh hV hJ hbochner hcauchy hrayleigh
  have hj := rational_trace_support hN hq hmain
  constructor <;> nlinarith

theorem rational_raw_coefficient_below_three_thirty_six :
    (114750/343:ℝ) < 336 := by norm_num

end KLSConstantImprovement.RelaxedLiteralCubicRayleighPayoff
#print axioms KLSConstantImprovement.RelaxedLiteralCubicRayleighPayoff.variance_from_relaxed_rayleigh
#print axioms KLSConstantImprovement.RelaxedLiteralCubicRayleighPayoff.rational_trace_support
#print axioms KLSConstantImprovement.RelaxedLiteralCubicRayleighPayoff.conditional_raw_cubic_cap
#print axioms KLSConstantImprovement.RelaxedLiteralCubicRayleighPayoff.rational_raw_coefficient_below_three_thirty_six
