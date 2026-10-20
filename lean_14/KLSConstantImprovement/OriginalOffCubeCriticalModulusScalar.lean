import Mathlib

/- Scalar receipts for the same original joint-H ODECO off-cube modulus.
Matrix functional variance, positive-map interpolation, fractional trace
closure, original off-square and directional inputs remain explicit. -/

namespace KLSConstantImprovement.OriginalOffCubeCriticalModulusScalar

theorem fourth_power_sandwich_cap
    (M Q : ℝ) (hM : 0 ≤ M) (hQ : 0 ≤ Q)
    (hclosure : M ^ 4 ≤ (64 * Q) ^ 4) : M ≤ 64 * Q := by
  by_contra h
  have hlt : 64 * Q < M := lt_of_not_ge h
  have hb : 0 ≤ 64 * Q := by positivity
  have hmp : 0 < M := lt_of_le_of_lt hb hlt
  have hs : 0 < M + 64 * Q := by linarith
  have hs2 : 0 < M ^ 2 + (64 * Q) ^ 2 := by
    nlinarith [mul_pos hmp hmp, sq_nonneg (64 * Q)]
  have hp : 0 < (M - 64 * Q) * (M + 64 * Q) *
      (M ^ 2 + (64 * Q) ^ 2) :=
    mul_pos (mul_pos (sub_pos.mpr hlt) hs) hs2
  have heq : (M - 64 * Q) * (M + 64 * Q) *
      (M ^ 2 + (64 * Q) ^ 2) = M ^ 4 - (64 * Q) ^ 4 := by ring
  rw [heq] at hp
  linarith

theorem off_cube_budget
    (a2 a3 a35 N d : ℝ) (hd : 0 ≤ d)
    (hholder : a3 ^ 3 ≤ a2 * a35 ^ 2)
    (hoff : a2 ≤ d / 4)
    (hmoment : a35 ^ 2 ≤ 4096 * N ^ 2) :
    a3 ^ 3 ≤ 1024 * N ^ 2 * d := by
  have hproduct : a2 * a35 ^ 2 ≤ (d / 4) * (4096 * N ^ 2) :=
    mul_le_mul hoff hmoment (sq_nonneg a35) (by positivity)
  nlinarith

theorem full_odeco_third_modulus
    (w diagonal a3 N d s : ℝ)
    (htriangle : w ≤ diagonal + a3)
    (hdiagonal : diagonal ≤ 6 * N + 3 * s + (3 / 4 : ℝ) * d) :
    w ≤ 6 * N + 3 * s + (3 / 4 : ℝ) * d + a3 := by
  linarith

#print axioms KLSConstantImprovement.OriginalOffCubeCriticalModulusScalar.fourth_power_sandwich_cap
#print axioms KLSConstantImprovement.OriginalOffCubeCriticalModulusScalar.off_cube_budget
#print axioms KLSConstantImprovement.OriginalOffCubeCriticalModulusScalar.full_odeco_third_modulus

end KLSConstantImprovement.OriginalOffCubeCriticalModulusScalar
