import KLSConstantImprovement.ActualObservationFourthDeficit

/-! Scalar consequence of the original critical-observation curvature payment.
The original tilted-law and Gaussian-damping identifications are explicit
inputs. This proves no positive-deficit extension or new universal endpoint. -/

noncomputable section
namespace KLSConstantImprovement.CriticalObservationCubicBarrierScalar

theorem critical_observation_bound {X R d j e : ℝ}
    (hpair : 8 * X = 18 * j + e)
    (hj : j ^ 2 ≤ 8 * R)
    (he : e ^ 2 ≤ 672 * d)
    (hbudget : R + d ≤ 8 * X)
    (hcreation : 3 * R ≤ 16 * X) :
    X ≤ (89896 / 225 : ℝ) := by
  have hsq : (8 * X) ^ 2 = (18 * j + e) ^ 2 := congrArg (fun z : ℝ => z ^ 2) hpair
  have hweighted : 64 * X ^ 2 ≤ (88128 / 25 : ℝ) * R + (7616 / 3 : ℝ) * d := by
    nlinarith [sq_nonneg ((54 / 5 : ℝ) * j - (5 / 3 : ℝ) * e)]
  have hquadratic : 64 * X ^ 2 ≤ (5753344 / 225 : ℝ) * X := by
    linarith
  by_contra! hbad
  have hX : 0 < X := lt_trans (by norm_num : (0 : ℝ) < 89896 / 225) hbad
  have hprod := mul_pos hX (sub_pos.mpr hbad)
  nlinarith

theorem critical_observation_lt_fourhundred {X R d j e : ℝ}
    (hpair : 8 * X = 18 * j + e)
    (hj : j ^ 2 ≤ 8 * R)
    (he : e ^ 2 ≤ 672 * d)
    (hbudget : R + d ≤ 8 * X)
    (hcreation : 3 * R ≤ 16 * X) :
    X < 400 := by
  have h := critical_observation_bound hpair hj he hbudget hcreation
  linarith

end KLSConstantImprovement.CriticalObservationCubicBarrierScalar
#print axioms KLSConstantImprovement.CriticalObservationCubicBarrierScalar.critical_observation_bound
#print axioms KLSConstantImprovement.CriticalObservationCubicBarrierScalar.critical_observation_lt_fourhundred
