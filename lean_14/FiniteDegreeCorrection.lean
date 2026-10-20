import Mathlib
import OptimizedBarrier2492

/-! The all-finite-degree scalar correction used after the limiting barrier.
This does not assume or assert the analytic Appell induction criterion. -/

namespace KLSBelow25

theorem affine_positive_of_endpoint {b d t : ℝ}
    (hb : 0 < b) (hend : 0 < b + d / 4)
    (ht : 0 ≤ t) (htop : t ≤ 1 / 4) : 0 < b + t * d := by
  by_cases hd : 0 ≤ d
  · nlinarith [mul_nonneg ht hd]
  · have hd' : d ≤ 0 := le_of_not_ge hd
    have hm := mul_le_mul_of_nonpos_right htop hd'
    nlinarith

end KLSBelow25

namespace OptimizedBarrier2492

/-- With v=q*u, rho=r/sqrt(phi), sigma=r*q*sqrt(u), this is exactly
M_k-M_infinity. The statement covers every t in (0,1/4], so every rank k>=3. -/
theorem finite_degree_correction_positive {v rho sigma t : ℝ}
    (hv : 0 ≤ v) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) (htop : t ≤ 1 / 4) :
    0 < t * (1 + (A + 3) * v + (1 - 2 * delta) * rho +
      (3 - 2 * delta) * sigma) +
      t ^ 2 * (-5 * v + (2 - 2 * delta) * rho - 2) := by
  let bc := 1 + (A + 3) * v + (1 - 2 * delta) * rho +
    (3 - 2 * delta) * sigma
  let dc := -5 * v + (2 - 2 * delta) * rho - 2
  have hb : 0 < bc := by
    dsimp [bc]
    norm_num [A, delta]
    positivity
  have hend : 0 < bc + dc / 4 := by
    have he : bc + dc / 4 = 1 / 2 + (A + 7 / 4) * v +
        (3 / 2 - 5 * delta / 2) * rho + (3 - 2 * delta) * sigma := by
      dsimp [bc, dc]
      ring
    rw [he]
    norm_num [A, delta]
    positivity
  have hp := KLSBelow25.affine_positive_of_endpoint hb hend ht.le htop
  have hm := mul_pos ht hp
  dsimp [bc, dc] at hm
  nlinarith

#print axioms finite_degree_correction_positive

end OptimizedBarrier2492
