import Mathlib
namespace HookCurlPriceCoupling

theorem paired_hook_charge
    (q h ht x y k : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hgram : k ^ 2 ≤ x * y)
    (hh : h = x + y + 2 * k) (hht : ht = x + y - 2 * k)
    (hq : 3 * x / 2 + y / 2 ≤ q) : 9 * h / 20 ≤ q + 3 * ht / 4 := by
  have hs : 0 ≤ 9 * x + 4 * y - 12 * k := by
    rcases eq_or_lt_of_le hx with hx0 | hxp
    · have hk : k = 0 := by nlinarith [sq_nonneg k]
      simp only [← hx0, hk]
      linarith
    · have hm : 0 ≤ x * (9 * x + 4 * y - 12 * k) := by
        nlinarith [sq_nonneg (3 * x - 2 * k)]
      by_contra hn
      have hv : 9 * x + 4 * y - 12 * k < 0 := lt_of_not_ge hn
      have hp := mul_neg_of_pos_of_neg hxp hv
      linarith
  linarith

theorem center_hook_price
    (d h k center : ℝ) (hd : 0 ≤ d) (hh : 0 ≤ h)
    (hgram : k ^ 2 ≤ d * h)
    (hcenter : d + k + h / 4 ≤ 4 * center) :
    9 * d / 14 ≤ 9 * h / 20 + 4 * center := by
  have hs : 0 ≤ 25 * d + 70 * k + 49 * h := by
    rcases eq_or_lt_of_le hd with hd0 | hdp
    · have hk : k = 0 := by nlinarith [sq_nonneg k]
      simp only [← hd0, hk]
      linarith
    · have hm : 0 ≤ d * (25 * d + 70 * k + 49 * h) := by
        nlinarith [sq_nonneg (5 * d + 7 * k)]
      by_contra hn
      have hv : 25 * d + 70 * k + 49 * h < 0 := lt_of_not_ge hn
      have hp := mul_neg_of_pos_of_neg hdp hv
      linarith
  linarith

theorem target_skew_price_financed
    (q ht h d center s price : ℝ) (hd : 0 ≤ d)
    (hhook : 9 * h / 20 ≤ q + 3 * ht / 4)
    (hcenter : 9 * d / 14 ≤ 9 * h / 20 + 4 * center)
    (hprice : price = s + 3 * d / 8) :
    price ≤ s + q + 3 * ht / 4 + 4 * center := by
  linarith

end HookCurlPriceCoupling
#print axioms HookCurlPriceCoupling.paired_hook_charge
#print axioms HookCurlPriceCoupling.center_hook_price
#print axioms HookCurlPriceCoupling.target_skew_price_financed
