import KLSConstantImprovement.ActualRadialMatrixCalculus405

/-! Uniform rational coefficient bounds used to remove the joint-variable
truncation on compact sets where H has a positive lower bound. These finite
inequalities do not assume a bound on u. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.ActualIntrinsicRatioBounds405
open ActualRadialMatrixCalculus405
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positive_denom_of_radial_lower {a f : ℝ} (ha : 0 < a) (v : ι → ℝ)
    (hf : 1 + a * radialSquare v ≤ f) : 0 < f := by
  have hr := radialSquare_nonnegative v
  nlinarith [mul_nonneg ha.le hr]

theorem radial_pair_ratio_le {a f : ℝ} (ha : 0 < a) (v : ι → ℝ)
    (hf : 1 + a * radialSquare v ≤ f) (i j : ι) : |v i * v j| / f ≤ a⁻¹ := by
  have hfp := positive_denom_of_radial_lower ha v hf
  have hp := abs_coordinate_product_le_radialSquare v i j
  have hm : a * |v i * v j| ≤ f := by
    nlinarith [mul_le_mul_of_nonneg_left hp ha.le]
  apply (div_le_iff₀ hfp).mpr
  calc
    _ = a⁻¹ * (a * |v i * v j|) := by rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr ha.le)

theorem radial_coordinate_ratio_le {a f : ℝ} (ha : 0 < a) (v : ι → ℝ)
    (hf : 1 + a * radialSquare v ≤ f) (i : ι) : |v i| / f ≤ 1 + a⁻¹ := by
  have hfp := positive_denom_of_radial_lower ha v hf
  have hr := radialSquare_nonnegative v
  have hi := coordinate_sq_le_radialSquare v i
  have hab : |v i| ≤ 1 + radialSquare v := by
    nlinarith [sq_nonneg (|v i| - 1), sq_abs (v i)]
  apply (div_le_iff₀ hfp).mpr
  calc
    _ ≤ 1 + radialSquare v := hab
    _ ≤ 1 + radialSquare v + a⁻¹ + a * radialSquare v := by
      linarith [inv_nonneg.mpr ha.le, mul_nonneg ha.le hr]
    _ = (1 + a⁻¹) * (1 + a * radialSquare v) := by field_simp [ha.ne'] <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hf (by positivity)

theorem radial_triple_ratio_le {a f : ℝ} (ha : 0 < a) (v : ι → ℝ)
    (hf : 1 + a * radialSquare v ≤ f) (i j k : ι) :
    |v i * v j * v k| / f ^ 2 ≤ a⁻¹ * (1 + a⁻¹) := by
  have hfp := positive_denom_of_radial_lower ha v hf
  have he : |v i * v j * v k| / f ^ 2 = (|v i * v j| / f) * (|v k| / f) := by
    rw [abs_mul]
    field_simp [hfp.ne']
  rw [he]
  exact mul_le_mul (radial_pair_ratio_le ha v hf i j)
    (radial_coordinate_ratio_le ha v hf k) (div_nonneg (abs_nonneg _) hfp.le)
    (inv_nonneg.mpr ha.le)

theorem radial_four_ratio_le {a f : ℝ} (ha : 0 < a) (v : ι → ℝ)
    (hf : 1 + a * radialSquare v ≤ f) (i j k l : ι) :
    |v i * v j * (v k * v l)| / f ^ 2 ≤ a⁻¹ ^ 2 := by
  have hfp := positive_denom_of_radial_lower ha v hf
  have he : |v i * v j * (v k * v l)| / f ^ 2 =
      (|v i * v j| / f) * (|v k * v l| / f) := by
    rw [abs_mul]
    field_simp [hfp.ne']
  rw [he, pow_two]
  exact mul_le_mul (radial_pair_ratio_le ha v hf i j)
    (radial_pair_ratio_le ha v hf k l) (div_nonneg (abs_nonneg _) hfp.le)
    (inv_nonneg.mpr ha.le)

end KLSConstantImprovement.ActualIntrinsicRatioBounds405
#print axioms KLSConstantImprovement.ActualIntrinsicRatioBounds405.radial_pair_ratio_le
#print axioms KLSConstantImprovement.ActualIntrinsicRatioBounds405.radial_coordinate_ratio_le
#print axioms KLSConstantImprovement.ActualIntrinsicRatioBounds405.radial_triple_ratio_le
#print axioms KLSConstantImprovement.ActualIntrinsicRatioBounds405.radial_four_ratio_le
