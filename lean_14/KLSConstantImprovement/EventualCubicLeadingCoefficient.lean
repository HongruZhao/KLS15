import Mathlib

/-! Standalone Archimedean bridge for the current scalar certificate family.
This draft has not been compiled. No claim about the optimal KLS constant
follows without the separately stated eventual-tail identity and scope. -/
noncomputable section
namespace KLSConstantImprovement.EventualCubicLeadingCoefficient

/-- A cubic nonnegative at all sufficiently large natural arguments has
nonnegative cubic coefficient. The proof uses an explicit Archimedean bound. -/
theorem leading_nonneg
    (q a b z : ℝ) (D : ℕ)
    (hP : ∀ n : ℕ, D ≤ n →
      0 ≤ q*(n : ℝ)^3+a*(n : ℝ)^2+b*(n : ℝ)+z) :
    0 ≤ q := by
  by_contra hq0
  have hq : q < 0 := lt_of_not_ge hq0
  have hnegq : 0 < -q := neg_pos.mpr hq
  let M : ℝ := |a| + |b| + |z|
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max (D : ℝ) (max (1 : ℝ) (M/(-q))))
  have hDn : (D : ℝ) < (n : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hn
  have hDn' : D ≤ n := by exact_mod_cast hDn.le
  have hn1 : (1 : ℝ) < (n : ℝ) :=
    lt_of_le_of_lt
      ((le_max_left (1 : ℝ) (M/(-q))).trans
        (le_max_right (D : ℝ) (max (1 : ℝ) (M/(-q))))) hn
  have hnq : M/(-q) < (n : ℝ) :=
    lt_of_le_of_lt
      ((le_max_right (1 : ℝ) (M/(-q))).trans
        (le_max_right (D : ℝ) (max (1 : ℝ) (M/(-q))))) hn
  let x : ℝ := n
  have hx1 : 1 < x := hn1
  have hx0 : 0 ≤ x := by linarith
  have hx2 : x ≤ x^2 := by nlinarith [sq_nonneg (x-1)]
  have hx2one : 1 ≤ x^2 := hx1.le.trans hx2
  have hax : a*x^2 ≤ |a| * x^2 :=
    mul_le_mul_of_nonneg_right (le_abs_self a) (sq_nonneg x)
  have hbx : b*x ≤ |b| * x^2 := by
    calc
      b*x ≤ |b| * x := mul_le_mul_of_nonneg_right (le_abs_self b) hx0
      _ ≤ |b| * x^2 := mul_le_mul_of_nonneg_left hx2 (abs_nonneg b)
  have hzx : z ≤ |z| * x^2 := by
    calc
      z ≤ |z| := le_abs_self z
      _ = |z| * 1 := by ring
      _ ≤ |z| * x^2 := mul_le_mul_of_nonneg_left hx2one (abs_nonneg z)
  have hlower : a*x^2+b*x+z ≤ M*x^2 := by
    dsimp only [M]
    nlinarith only [hax,hbx,hzx]
  have hM : M < x*(-q) := (div_lt_iff₀ hnegq).mp hnq
  have hlinear : q*x+M < 0 := by nlinarith only [hM]
  have hx2pos : 0 < x^2 := sq_pos_of_pos (by linarith)
  have hnegative : q*x^3+M*x^2 < 0 := by
    have hh := mul_neg_of_pos_of_neg hx2pos hlinear
    have he : x^2*(q*x+M)=q*x^3+M*x^2 := by ring
    rwa [he] at hh
  have hnonneg := hP n hDn'
  change 0 ≤ q*x^3+a*x^2+b*x+z at hnonneg
  linarith only [hlower,hnegative,hnonneg]

/-- The all-rank coefficient lower bound supplies the polynomial sign after
clearing the positive tail denominator d-1. No fixed cutoff is required. -/
theorem leading_nonneg_of_eventual_coefficient_lower
    (coefficient : ℕ → ℝ) (c q a b z : ℝ) (D : ℕ)
    (hlower : ∀ d : ℕ, D ≤ d → c ≤ coefficient d)
    (hidentity : ∀ d : ℕ, D ≤ d →
      ((d : ℝ)-1)*(coefficient d-c)=
        q*(d : ℝ)^3+a*(d : ℝ)^2+b*(d : ℝ)+z) :
    0 ≤ q := by
  apply leading_nonneg q a b z (max D 1)
  intro d hd
  have hDd : D ≤ d := (Nat.le_max_left D 1).trans hd
  have hd1 : 1 ≤ d := (Nat.le_max_right D 1).trans hd
  have hd1r : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  calc
    0 ≤ ((d : ℝ)-1)*(coefficient d-c) :=
      mul_nonneg (sub_nonneg.mpr hd1r) (sub_nonneg.mpr (hlower d hDd))
    _ = _ := hidentity d hDd

end KLSConstantImprovement.EventualCubicLeadingCoefficient

#print axioms KLSConstantImprovement.EventualCubicLeadingCoefficient.leading_nonneg
#print axioms KLSConstantImprovement.EventualCubicLeadingCoefficient.leading_nonneg_of_eventual_coefficient_lower
