import KLSConstantImprovement.RawCubicWeightedBudget

/-! A same-test cubic/quartic support can pay a rank-four generator
deficit. This is a finite scalar head reduction; the actual law support
and original-class weighted induction are separate declarations.
-/
noncomputable section
open Set
open scoped BigOperators
namespace KLSConstantImprovement.RawCubicQuarticWeightedHead
open TriplePositiveEnergyWeightedBudget
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def cubicCoefficient (P : Parameters) : ℝ :=
  (P.c - coefficient P 3) * P.t 3 / P.K ^ 3

def quarticCoefficient (P : Parameters) : ℝ :=
  (P.c - coefficient P 4) * P.t 4 / P.K ^ 4

def headBound (P : Parameters) (H A B : ℝ) : ℝ :=
  (P.c + head P) * (2 * P.t 2 / P.K ^ 2) +
    max (cubicCoefficient P - quarticCoefficient P * A) 0 * (H / 36) +
      quarticCoefficient P * B

theorem support_head_payment (P : Parameters) {H A B y z : ℝ}
    (hK : P.K ≠ 0) (hy : 0 ≤ y) (hycap : y ≤ H / 36)
    (hsupport : z + A * y ≤ B) (hQ4 : 0 ≤ quarticCoefficient P) :
    (P.c - coefficient P 3) * (P.t 3 * y / P.K ^ 3) +
      (P.c - coefficient P 4) * (P.t 4 * z / P.K ^ 4) ≤
        max (cubicCoefficient P - quarticCoefficient P * A) 0 * (H / 36) +
          quarticCoefficient P * B := by
  have hq := mul_le_mul_of_nonneg_left hsupport hQ4
  have hrem := mul_le_mul_of_nonneg_right
    (le_max_left (cubicCoefficient P - quarticCoefficient P * A) 0) hy
  have hcap := mul_le_mul_of_nonneg_left hycap
    (le_max_right (cubicCoefficient P - quarticCoefficient P * A) 0)
  have hrewrite :
      (P.c - coefficient P 3) * (P.t 3 * y / P.K ^ 3) +
        (P.c - coefficient P 4) * (P.t 4 * z / P.K ^ 4) =
          cubicCoefficient P * y + quarticCoefficient P * z := by
    unfold cubicCoefficient quarticCoefficient
    ring
  rw [hrewrite]
  nlinarith

theorem finite_energy_head_reduction (P : Parameters)
    (e : ℕ → ℝ) (N : ℕ) (hN : 4 ≤ N)
    (hcoeff : ∀ d, 5 ≤ d → P.c ≤ coefficient P d)
    (he : ∀ d ∈ Finset.Icc 5 N, 0 ≤ e d)
    (hgen : (∑ d ∈ Finset.Icc 3 N, coefficient P d * e d) -
      head P * e 2 ≤ 0) :
    P.c * (∑ d ∈ Finset.Icc 2 N, e d) -
      (P.c + head P) * e 2 - (P.c - coefficient P 3) * e 3 -
        (P.c - coefficient P 4) * e 4 ≤ 0 := by
  classical
  have htail : P.c * (∑ d ∈ Finset.Icc 5 N, e d) ≤
      ∑ d ∈ Finset.Icc 5 N, coefficient P d * e d := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun d hd => mul_le_mul_of_nonneg_right
      (hcoeff d (Finset.mem_Icc.mp hd).1) (he d hd)
  have hs4 : Finset.Icc 4 N = insert 4 (Finset.Icc 5 N) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hs3 : Finset.Icc 3 N = insert 3 (Finset.Icc 4 N) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hs2 : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hn4 : 4 ∉ Finset.Icc 5 N := by simp
  have hn3 : 3 ∉ Finset.Icc 4 N := by simp
  have hn2 : 2 ∉ Finset.Icc 3 N := by simp
  rw [hs3, Finset.sum_insert hn3, hs4, Finset.sum_insert hn4] at hgen
  rw [hs2, Finset.sum_insert hn2, hs3, Finset.sum_insert hn3,
    hs4, Finset.sum_insert hn4]
  nlinarith

theorem finite_energy_sum_lt_budget (P : Parameters) {H A B y z : ℝ}
    (hK : 0 < P.K) (hc : 0 < P.c)
    (hcoeff : ∀ d, 5 ≤ d → P.c ≤ coefficient P d)
    (hhead : 0 ≤ P.c + head P) (hQ4 : 0 ≤ quarticCoefficient P)
    (hmargin : headBound P H A B < P.c * P.C)
    (e : ℕ → ℝ) (N : ℕ) (hN : 4 ≤ N)
    (he : ∀ d ∈ Finset.Icc 5 N, 0 ≤ e d)
    (he2 : e 2 ≤ 2 * P.t 2 / P.K ^ 2)
    (he3 : e 3 = P.t 3 * y / P.K ^ 3)
    (he4 : e 4 = P.t 4 * z / P.K ^ 4)
    (hy : 0 ≤ y) (hycap : y ≤ H / 36) (hsupport : z + A * y ≤ B)
    (hgen : (∑ d ∈ Finset.Icc 3 N, coefficient P d * e d) -
      head P * e 2 ≤ 0) :
    (∑ d ∈ Finset.Icc 2 N, e d) < P.C := by
  have hg := finite_energy_head_reduction P e N hN hcoeff he hgen
  have h2 := mul_le_mul_of_nonneg_left he2 hhead
  have h34 := support_head_payment P hK.ne' hy hycap hsupport hQ4
  rw [← he3, ← he4] at h34
  unfold headBound at hmargin
  by_contra hn
  have hM := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hc.le
  nlinarith

end KLSConstantImprovement.RawCubicQuarticWeightedHead
#print axioms KLSConstantImprovement.RawCubicQuarticWeightedHead.support_head_payment
#print axioms KLSConstantImprovement.RawCubicQuarticWeightedHead.finite_energy_head_reduction
#print axioms KLSConstantImprovement.RawCubicQuarticWeightedHead.finite_energy_sum_lt_budget
