import KLSConstantImprovement.ActualCovariantKatoAlgebra405

/-! Exact pointwise square for the full, uncapped positive-part test in
a weak Kato subsolution. No tail of a capped test is discarded. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualWeakKatoExcessAlgebra405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ}

def excessSlope (t : ℝ) : ℝ := if 0 < t then 1 else if t < 0 then 0 else 1/2

theorem excessSlope_nonnegative (t : ℝ) : 0 ≤ excessSlope t := by
  unfold excessSlope
  split_ifs <;> norm_num

theorem excess_rhs_identity (w B χ : ℝ) :
    (B-w/2) * (χ^2 * max (w-2*B) 0) = -(1/2 : ℝ) * (χ^2 * max (w-2*B) 0 ^ 2) := by
  by_cases h : 0 ≤ w-2*B
  · rw [max_eq_left h]
    ring
  · rw [max_eq_right (le_of_not_ge h)]
    ring

theorem full_excess_test_pointwise (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : J.PosSemidef) (v z : Fin n → ℝ) {w B : ℝ}
    (hw : 0 ≤ w) (hB : 0 ≤ B) (χ : ℝ) :
    (J *ᵥ v) ⬝ᵥ (fun i => 2*χ*z i*max (w-2*B) 0 +
      χ^2*excessSlope (w-2*B)*v i) ≥ -w^2 * (z ⬝ᵥ (J *ᵥ z)) := by
  have hG : 0 ≤ v ⬝ᵥ (J *ᵥ v) := by simpa only [star_trivial] using hJ.dotProduct_mulVec_nonneg v
  have hQ : 0 ≤ z ⬝ᵥ (J *ᵥ z) := by simpa only [star_trivial] using hJ.dotProduct_mulVec_nonneg z
  have hsym := hJ.isHermitian.isSymm
  have hcross : z ⬝ᵥ (J *ᵥ v) = v ⬝ᵥ (J *ᵥ z) := hsym.dotProduct_mulVec_comm
  have he (e a : ℝ) :
      (J *ᵥ v) ⬝ᵥ (fun i => 2*χ*z i*e + χ^2*a*v i) =
        χ^2*a*(v ⬝ᵥ (J *ᵥ v)) + 2*χ*e*(v ⬝ᵥ (J *ᵥ z)) := by
    change (∑ i, (J *ᵥ v) i * (2*χ*z i*e + χ^2*a*v i)) = _
    have hsum : (∑ i, (J *ᵥ v) i * (2*χ*z i*e + χ^2*a*v i)) =
        χ^2*a*(v ⬝ᵥ (J *ᵥ v)) + 2*χ*e*(z ⬝ᵥ (J *ᵥ v)) := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum, hcross]
  rw [he]
  by_cases h : 0 < w-2*B
  · rw [excessSlope, if_pos h, max_eq_left h.le, mul_one]
    have hsquare : 0 ≤ (χ • v + (w-2*B) • z) ⬝ᵥ
        (J *ᵥ (χ • v + (w-2*B) • z)) := by
      simpa only [star_trivial] using hJ.dotProduct_mulVec_nonneg (χ • v + (w-2*B) • z)
    have hform : (χ • v + (w-2*B) • z) ⬝ᵥ
        (J *ᵥ (χ • v + (w-2*B) • z)) =
        χ^2*(v ⬝ᵥ (J *ᵥ v)) + 2*χ*(w-2*B)*(v ⬝ᵥ (J *ᵥ z)) +
          (w-2*B)^2*(z ⬝ᵥ (J *ᵥ z)) := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul, hcross]
      ring
    rw [hform] at hsquare
    have hbound : (w-2*B)^2 ≤ w^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hbound hQ
    linarith
  · simp only [max_eq_right (le_of_not_gt h), mul_zero, zero_mul, add_zero]
    have hn : 0 ≤ χ^2*excessSlope (w-2*B)*(v ⬝ᵥ (J *ᵥ v)) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (excessSlope_nonnegative _)) hG
    nlinarith

end KLSConstantImprovement.ActualWeakKatoExcessAlgebra405
#print axioms KLSConstantImprovement.ActualWeakKatoExcessAlgebra405.excessSlope_nonnegative
#print axioms KLSConstantImprovement.ActualWeakKatoExcessAlgebra405.excess_rhs_identity
#print axioms KLSConstantImprovement.ActualWeakKatoExcessAlgebra405.full_excess_test_pointwise
