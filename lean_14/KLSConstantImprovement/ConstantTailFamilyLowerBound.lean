import Mathlib

/-! A necessary lower bound for the present constant-tail scalar certificate
family only. This is not a lower bound for the optimal universal KLS constant.
It does not assert global optimality of any numerical nomination. -/
noncomputable section
namespace KLSConstantImprovement.ConstantTailFamilyLowerBound

theorem K_lower_of_tail_coefficient
    (K C y alpha : ℝ) (hK : 0 < K) (hC : 0 < C) (hy : 0 < y)
    (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (hq : 0 ≤ K*alpha-4/(1-alpha)+2-K*C/y) :
    6+4*Real.sqrt 2 < K := by
  have ht : 0 < 1-alpha := by linarith
  have hpay : 0 < K*C/y := by positivity
  have hmain : 4/(1-alpha) < K*alpha+2 := by linarith
  have hmul : 4 < (K*alpha+2)*(1-alpha) :=
    (div_lt_iff₀ ht).mp hmain
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  by_contra hfail
  have hcap : K ≤ 6+4*Real.sqrt 2 := le_of_not_gt hfail
  have haProd : 0 ≤ alpha*(1-alpha) := mul_nonneg ha ht.le
  have hweak := mul_le_mul_of_nonneg_right hcap haProd
  have hid :
      (6+4*Real.sqrt 2)*alpha*(1-alpha)+2*(1-alpha)-4 =
        -(((2+Real.sqrt 2)*alpha-Real.sqrt 2)^2) := by
    ring_nf
    simp only [hs]
    ring
  have hsq := sq_nonneg ((2+Real.sqrt 2)*alpha-Real.sqrt 2)
  nlinarith

theorem endpoint_lower_of_tail_coefficient
    (K C y alpha p : ℝ) (hK : 0 < K) (hC : 0 < C) (hy : 0 < y)
    (ha : 0 ≤ alpha) (ha1 : alpha < 1) (hp : 1 ≤ p)
    (hq : 0 ≤ K*alpha-4/(1-alpha)+2-K*C/y) :
    7+4*Real.sqrt 2 < 1+K*p := by
  have hk := K_lower_of_tail_coefficient K C y alpha hK hC hy ha ha1 hq
  have hm := mul_le_mul_of_nonneg_left hp hK.le
  nlinarith

end KLSConstantImprovement.ConstantTailFamilyLowerBound
#print axioms KLSConstantImprovement.ConstantTailFamilyLowerBound.K_lower_of_tail_coefficient
#print axioms KLSConstantImprovement.ConstantTailFamilyLowerBound.endpoint_lower_of_tail_coefficient
