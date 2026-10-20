import KLSConstantImprovement.CriticalObservationCubicBarrierScalar

/-! The accepted distinct-slot cap4 sharpens the critical observation
curvature charge from672d to416d, excluding the current E3>=360 barrier.
Actual tilt/damping identifications and exact observation criticality
remain explicit inputs; no positive-deficit extension is asserted. -/

noncomputable section
namespace KLSConstantImprovement.SharpCriticalObservationCubicBarrierScalar

theorem critical_observation_bound {X R d j e : ℝ}
    (hpair : 8 * X = 18 * j + e)
    (hj : j ^ 2 ≤ 8 * R)
    (he : e ^ 2 ≤ 416 * d)
    (hbudget : R + d ≤ 8 * X)
    (hcreation : 3 * R ≤ 16 * X) :
    X ≤ (2490 / 7 : ℝ) := by
  have hsq : (8 * X) ^ 2 = (18 * j + e) ^ 2 := congrArg (fun z : ℝ => z ^ 2) hpair
  have hweighted : 64 * X ^ 2 ≤ (23328 / 7 : ℝ) * R + 1872 * d := by
    nlinarith [sq_nonneg ((36 / 7 : ℝ) * j - e)]
  have hquadratic : 64 * X ^ 2 ≤ (159360 / 7 : ℝ) * X := by
    linarith
  by_contra! hbad
  have hX : 0 < X := lt_trans (by norm_num : (0 : ℝ) < 2490 / 7) hbad
  have hprod := mul_pos hX (sub_pos.mpr hbad)
  nlinarith

theorem below_current_lower_barrier {X R d j e : ℝ}
    (hpair : 8 * X = 18 * j + e)
    (hj : j ^ 2 ≤ 8 * R)
    (he : e ^ 2 ≤ 416 * d)
    (hbudget : R + d ≤ 8 * X)
    (hcreation : 3 * R ≤ 16 * X) :
    X < 360 := by
  have h := critical_observation_bound hpair hj he hbudget hcreation
  linarith

theorem excludes_high_sector {X R d j e : ℝ}
    (hpair : 8 * X = 18 * j + e)
    (hj : j ^ 2 ≤ 8 * R)
    (he : e ^ 2 ≤ 416 * d)
    (hbudget : R + d ≤ 8 * X)
    (hcreation : 3 * R ≤ 16 * X) (hhigh : 360 ≤ X) : False := by
  exact (not_lt_of_ge hhigh) (below_current_lower_barrier hpair hj he hbudget hcreation)

end KLSConstantImprovement.SharpCriticalObservationCubicBarrierScalar
#print axioms KLSConstantImprovement.SharpCriticalObservationCubicBarrierScalar.critical_observation_bound
#print axioms KLSConstantImprovement.SharpCriticalObservationCubicBarrierScalar.below_current_lower_barrier
#print axioms KLSConstantImprovement.SharpCriticalObservationCubicBarrierScalar.excludes_high_sector
