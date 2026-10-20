import KLSConstantImprovement.ConstantTailFiniteHitting

/-! Closed form for the greedy path of the accepted affine cap chord. -/
noncomputable section
namespace KLSConstantImprovement.ChordTailExplicitPath
open KLSConstantImprovement.ProperConstantTailRecursion
open KLSConstantImprovement.ConstantTailFiniteHitting

theorem clipped_affine (m A u : ℝ) (hm : 0 ≤ m) (hA : 0 ≤ A) :
    max 0 (m*max 0 u-A)=max 0 (m*u-A) := by
  by_cases hu : 0 ≤ u
  · rw [max_eq_right hu]
  · have hu' : u ≤ 0 := (lt_of_not_ge hu).le
    have hp : m*u-A ≤ 0 := by
      linarith [mul_nonpos_of_nonneg_of_nonpos hm hu']
    rw [max_eq_left hu',mul_zero,zero_sub,
      max_eq_left (by linarith : -A ≤ 0),max_eq_left hp]

/-- The positive fixed point of the affine map is R.  Clipping at zero
commutes with each step because both A and its slope are nonnegative. -/
theorem chord_path_formula {A R x : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hx : 0 ≤ x) (n : ℕ) :
    path (chordStep A R) n x=max 0 (R+(1+A/R)^n*(x-R)) := by
  have hm : 0 ≤ 1+A/R := by positivity
  have hfixed : (1+A/R)*R-A=R := by
    field_simp [ne_of_gt hR]
    ring
  induction n with
  | zero =>
      change x=max 0 (R+(1+A/R)^0*(x-R))
      rw [pow_zero,one_mul,show R+(x-R)=x by ring,max_eq_right hx]
  | succ n ih =>
      rw [path_succ,ih]
      unfold chordStep
      rw [clipped_affine _ _ _ hm hA]
      congr 1
      rw [pow_succ]
      linear_combination hfixed

end KLSConstantImprovement.ChordTailExplicitPath
#print axioms KLSConstantImprovement.ChordTailExplicitPath.chord_path_formula
