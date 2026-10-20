import Mathlib

/-! Exact scalar arithmetic of an actual truncated-exponential generic
function obstruction. Law/source/Riesz/whitening are explicit paper
bindings. The special fully symmetric quadratic response is not refuted. -/
namespace GenericCompatibleConnectionObstruction

theorem truncated_exponential_excess_positive
    (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 10000) :
    0 < 7 - 1336 * q - 21522 * q ^ 2 + 2096 * q ^ 3 + 19 * q ^ 4 := by
  have hq2 : q ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := by nlinarith
  have hq3 : 0 ≤ q ^ 3 := by positivity
  have hq4 : 0 ≤ q ^ 4 := by positivity
  nlinarith

theorem affine_whitening_keeps_source_energy_violation
    (c2 energy sigma2 : ℝ) (he : 0 ≤ energy)
    (hs : sigma2 ≤ 1) (hbad : energy < c2) : sigma2 * energy < c2 := by
  nlinarith

end GenericCompatibleConnectionObstruction

#print axioms GenericCompatibleConnectionObstruction.truncated_exponential_excess_positive
#print axioms GenericCompatibleConnectionObstruction.affine_whitening_keeps_source_energy_violation
