import KLSConstantImprovement.SharpCriticalObservationCubicBarrierScalar

/-! Retain the affine same-test energy in the exactly critical observation
sector. The original tilt, damping and observation identifications remain
explicit scalar inputs. No near-critical observation estimate is asserted. -/

noncomputable section
namespace KLSConstantImprovement.AffineCriticalObservationBarrierScalar
set_option maxHeartbeats 3000000

def bound : ℝ := 196644168 / 565543

theorem two_square_elimination {X J d R a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (haff : (2 * X - J) ^ 2 ≤ a * (8 * X - d - R))
    (hdef : (8 * X - 6 * J) ^ 2 ≤ b * d)
    (hangle : J ^ 2 ≤ 72 * R) :
    (288 + b + 16 * a) * X ^ 2 ≤ 2 * (72 * b + 2592 * a + a * b) * X := by
  let L := 72 * b * (2 * X - J) ^ 2 +
    72 * a * (8 * X - 6 * J) ^ 2 + a * b * J ^ 2
  let H := 72 * b + 2592 * a + a * b
  let D := 288 + b + 16 * a
  have hL : L ≤ 576 * a * b * X := by
    have h1 := mul_le_mul_of_nonneg_left haff (by positivity : 0 ≤ 72 * b)
    have h2 := mul_le_mul_of_nonneg_left hdef (by positivity : 0 ≤ 72 * a)
    have h3 := mul_le_mul_of_nonneg_left hangle (by positivity : 0 ≤ a * b)
    dsimp [L]
    nlinarith
  have hH : 0 < H := by dsimp [H]; positivity
  have hHL := mul_le_mul_of_nonneg_left hL hH.le
  have hid : H * L = (H * J - 144 * (b + 24 * a) * X) ^ 2 +
      288 * a * b * D * X ^ 2 := by
    dsimp [H,L,D]
    ring
  have hpaid : (288 * a * b) * (D * X ^ 2) ≤
      (288 * a * b) * (2 * H * X) := by
    nlinarith [sq_nonneg (H * J - 144 * (b + 24 * a) * X)]
  exact (mul_le_mul_iff_of_pos_left (by positivity : 0 < 288 * a * b)).mp hpaid

theorem critical_observation_bound {X J d R r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (haff : (2 * X - J) ^ 2 ≤
      (36 * ((71727 / 5000 : ℝ) - r - 2)) * (8 * X - d - R))
    (hdef : (8 * X - 6 * J) ^ 2 ≤ (352 + 64 * r) * d)
    (hangle : J ^ 2 ≤ 72 * R) : X ≤ bound := by
  let a := 36 * ((71727 / 5000 : ℝ) - r - 2)
  let b := 352 + 64 * r
  let H := 72 * b + 2592 * a + a * b
  let D := 288 + b + 16 * a
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hquadratic : D * X ^ 2 ≤ 2 * H * X :=
    two_square_elimination ha hb haff hdef hangle
  have hidentity : bound * D - 2 * H =
      64 * (72 * (1-r) ^ 2 +
        (8 * bound - 3456 + 72 * (71727 / 5000 : ℝ)) * (1-r)) := by
    dsimp [D,H,a,b,bound]
    ring
  have hcoefficient : 0 ≤ 8 * bound - 3456 + 72 * (71727 / 5000 : ℝ) := by
    norm_num [bound]
  have hdiff : 0 ≤ bound * D - 2 * H := by
    rw [hidentity]
    exact mul_nonneg (by norm_num) (add_nonneg (by positivity)
      (mul_nonneg hcoefficient (sub_nonneg.mpr hr1)))
  by_contra! hbad
  have hX : 0 < X := lt_trans (by norm_num [bound] : (0 : ℝ) < bound) hbad
  have hupper := mul_le_mul_of_nonneg_right (sub_nonneg.mp hdiff) hX.le
  have hprod := mul_pos (mul_pos hD hX) (sub_pos.mpr hbad)
  nlinarith

theorem critical_observation_lt348 {X J d R r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (haff : (2 * X - J) ^ 2 ≤
      (36 * ((71727 / 5000 : ℝ) - r - 2)) * (8 * X - d - R))
    (hdef : (8 * X - 6 * J) ^ 2 ≤ (352 + 64 * r) * d)
    (hangle : J ^ 2 ≤ 72 * R) : X < 348 := by
  have h := critical_observation_bound hr0 hr1 haff hdef hangle
  unfold bound at h
  linarith

end KLSConstantImprovement.AffineCriticalObservationBarrierScalar
#print axioms KLSConstantImprovement.AffineCriticalObservationBarrierScalar.two_square_elimination
#print axioms KLSConstantImprovement.AffineCriticalObservationBarrierScalar.critical_observation_bound
#print axioms KLSConstantImprovement.AffineCriticalObservationBarrierScalar.critical_observation_lt348
