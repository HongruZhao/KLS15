import Mathlib

/-! Finite scalar block payments for the original orthogonal-product,
all-symmetric-tensor compatible combined-energy bound. Ordinary scalar
CP4/tensorization, original marginal upper moments, signed independent
third contraction, tensor block decomposition, and Hessian-Riesz/domain
identification remain analytic inputs. CP4 is a separately cited scalar
theorem, not inferred from the centered-exponential benchmark. -/
noncomputable section
namespace KLSConstantImprovement.OriginalProductAllTensorCombinedEnergy

theorem diagonal_block_margin {m fourth : ℝ}
    (hm : m^2 ≤ 4) (hf : fourth ≤ 6 + (3/4 : ℝ)*m^2) :
    36*(fourth-1)+20 ≤ 224+21*m^2 := by nlinarith

theorem repeated_pair_margin (x y cross fourthA fourthB : ℝ)
    (hc0 : -4 ≤ cross) (hc1 : cross ≤ 4)
    (hfa : fourthA ≤ 9) (hfb : fourthB ≤ 9) :
    36*((fourthA+3)*x^2+(fourthB+3)*y^2)+156*(x^2+y^2) ≤
      672*(x^2+y^2)+42*cross*x*y := by
  have hcross : -2*(x^2+y^2) ≤ cross*x*y := by
    by_cases hxy : 0 ≤ x*y
    · have hp := mul_le_mul_of_nonneg_right hc0 hxy
      nlinarith [sq_nonneg (x-y)]
    · have hxy0 : x*y ≤ 0 := by linarith
      have hp := mul_le_mul_of_nonpos_right hc1 hxy0
      nlinarith [sq_nonneg (x+y)]
  have ha := mul_le_mul_of_nonneg_right hfa (sq_nonneg x)
  have hb := mul_le_mul_of_nonneg_right hfb (sq_nonneg y)
  nlinarith

theorem distinct_block_margin {N : ℝ} (hN : 0 ≤ N) :
    72*N+20*N ≤ 224*N := by linarith

theorem combined_energy_product_payment {energy quad N signed : ℝ}
    (hriesz : energy ≤ 36*quad)
    (hblocks : 36*quad+20*N ≤ 224*N+21*signed) :
    energy ≤ 204*N+21*signed := by linarith

end KLSConstantImprovement.OriginalProductAllTensorCombinedEnergy
#print axioms KLSConstantImprovement.OriginalProductAllTensorCombinedEnergy.diagonal_block_margin
#print axioms KLSConstantImprovement.OriginalProductAllTensorCombinedEnergy.repeated_pair_margin
#print axioms KLSConstantImprovement.OriginalProductAllTensorCombinedEnergy.distinct_block_margin
#print axioms KLSConstantImprovement.OriginalProductAllTensorCombinedEnergy.combined_energy_product_payment
