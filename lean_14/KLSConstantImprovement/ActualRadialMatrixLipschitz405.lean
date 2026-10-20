import KLSConstantImprovement.ActualRadialMatrixCalculus405

/-! Global Lipschitz bounds for the common-radial bounded matrix test.
The constants are only used for legitimate weak composition domains. -/
noncomputable section
open scoped BigOperators NNReal
namespace KLSConstantImprovement.ActualRadialMatrixLipschitz405
open ActualVectorDifferential405 ActualRadialMatrixCalculus405
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem radial_coordinate_ratio_bound {δ : ℝ} (hδ : 0 < δ) (v : ι → ℝ) (r : ι) :
    |v r| / radialDenom δ v ≤ 1 + δ⁻¹ := by
  have hd := radialDenom_positive hδ.le v
  have hs := radialSquare_nonnegative v
  have hr := coordinate_sq_le_radialSquare v r
  have hab : |v r| ≤ 1 + radialSquare v := by
    have h := sq_nonneg (|v r| - 1)
    have hsabs : |v r| ^ 2 = v r ^ 2 := sq_abs _
    nlinarith
  apply (div_le_iff₀ hd).mpr
  calc
    _ ≤ 1 + radialSquare v := hab
    _ ≤ 1 + radialSquare v + δ⁻¹ + δ * radialSquare v := by
      linarith [inv_nonneg.mpr hδ.le, mul_nonneg hδ.le hs]
    _ = (1 + δ⁻¹) * radialDenom δ v := by
      unfold radialDenom
      field_simp <;> ring

theorem radialMatrixEntry_partial_bound {δ : ℝ} (hδ : 0 < δ)
    (i j r : ι) (v : ι → ℝ) :
    ‖vectorPartial (radialMatrixEntry δ i j) r v‖ ≤ 4 * (1 + δ⁻¹) := by
  let w : ι → ℝ := Pi.single r 1
  have hw (k : ι) : |w k| ≤ 1 := by
    dsimp [w]
    by_cases h : r = k <;> simp [Pi.single_apply, h]
  have hpair : (∑ k, v k * w k) = v r := by simp [w, Pi.single_apply, eq_comm]
  have hd := radialDenom_positive hδ.le v
  have hc0 : 0 ≤ 1 + δ⁻¹ := by positivity
  have hi := radial_coordinate_ratio_bound hδ v i
  have hj := radial_coordinate_ratio_bound hδ v j
  have hr := radial_coordinate_ratio_bound hδ v r
  have hfirst : |(w i * v j + v i * w j) / radialDenom δ v| ≤ 2 * (1 + δ⁻¹) := by
    rw [abs_div, abs_of_pos hd]
    calc
      _ ≤ (|w i| * |v j| + |v i| * |w j|) / radialDenom δ v := by
        gcongr
        simpa only [abs_mul] using abs_add_le (w i * v j) (v i * w j)
      _ ≤ (|v j| + |v i|) / radialDenom δ v := by
        apply div_le_div_of_nonneg_right _ hd.le
        apply add_le_add
        · simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw i) (abs_nonneg (v j))
        · simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw j) (abs_nonneg (v i))
      _ = |v j| / radialDenom δ v + |v i| / radialDenom δ v := add_div _ _ _
      _ ≤ _ := by linarith
  have hsecondEq : |(2 * δ * v i * v j * v r) / radialDenom δ v ^ 2| =
      2 * δ * |radialMatrixEntry δ i j v| * (|v r| / radialDenom δ v) := by
    simp only [radialMatrixEntry, abs_div, abs_mul, abs_of_pos hd, abs_of_pos hδ,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow]
    field_simp <;> ring
  have hsecond : |(2 * δ * v i * v j * v r) / radialDenom δ v ^ 2| ≤ 2 * (1 + δ⁻¹) := by
    rw [hsecondEq]
    calc
      _ ≤ 2 * δ * δ⁻¹ * (1 + δ⁻¹) := by
        gcongr
        exact radialMatrixEntry_bound hδ i j v
      _ = _ := by field_simp <;> ring
  change |fderiv ℝ (radialMatrixEntry δ i j) v w| ≤ _
  rw [radialMatrixEntry_differential hδ.le i j v w, hpair]
  exact (abs_sub _ _).trans (by linarith)

def radialMatrixLipschitzConstant (δ : ℝ) : ℝ≥0 :=
  Real.toNNReal ((Fintype.card ι : ℝ) * (4 * (1 + δ⁻¹)))

theorem radialMatrixEntry_lipschitz {δ : ℝ} (hδ : 0 < δ) (i j : ι) :
    LipschitzWith (radialMatrixLipschitzConstant (ι := ι) δ) (radialMatrixEntry δ i j) := by
  have hC : 0 ≤ (Fintype.card ι : ℝ) * (4 * (1 + δ⁻¹)) := by positivity
  apply lipschitzWith_of_nnnorm_fderiv_le ((radialMatrixEntry_contDiff hδ.le i j).differentiable one_ne_zero)
  intro v
  change ‖fderiv ℝ (radialMatrixEntry δ i j) v‖ ≤ (radialMatrixLipschitzConstant (ι := ι) δ : ℝ)
  rw [radialMatrixLipschitzConstant, Real.coe_toNNReal _ hC]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro w
  rw [fderiv_eq_sum_vectorPartial]
  calc
    _ ≤ ∑ r, ‖vectorPartial (radialMatrixEntry δ i j) r v * w r‖ := norm_sum_le _ _
    _ ≤ ∑ r : ι, (4 * (1 + δ⁻¹)) * ‖w‖ := by
      apply Finset.sum_le_sum
      intro r _
      rw [norm_mul]
      exact mul_le_mul (radialMatrixEntry_partial_bound hδ i j r v)
        (norm_le_pi_norm w r) (norm_nonneg _) (by positivity)
    _ = (Fintype.card ι : ℝ) * (4 * (1 + δ⁻¹)) * ‖w‖ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end KLSConstantImprovement.ActualRadialMatrixLipschitz405

#print axioms KLSConstantImprovement.ActualRadialMatrixLipschitz405.radial_coordinate_ratio_bound
#print axioms KLSConstantImprovement.ActualRadialMatrixLipschitz405.radialMatrixEntry_partial_bound
#print axioms KLSConstantImprovement.ActualRadialMatrixLipschitz405.radialMatrixEntry_lipschitz
