import KLSConstantImprovement.ActualVectorDifferential405
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! The literal radial matrix test vvᵀ/(1+δ|v|²). One common radial
denominator preserves the aggregate matrix curvature contraction. -/
noncomputable section
open Matrix
open scoped BigOperators ContDiff
namespace KLSConstantImprovement.ActualRadialMatrixCalculus405
open ActualVectorDifferential405
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def radialSquare (v : ι → ℝ) : ℝ := ∑ k, v k ^ 2

def radialDenom (δ : ℝ) (v : ι → ℝ) : ℝ := 1 + δ * radialSquare v

def radialMatrixEntry (δ : ℝ) (i j : ι) (v : ι → ℝ) : ℝ :=
  v i * v j / radialDenom δ v

theorem radialSquare_nonnegative (v : ι → ℝ) : 0 ≤ radialSquare v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem coordinate_sq_le_radialSquare (v : ι → ℝ) (i : ι) : v i ^ 2 ≤ radialSquare v :=
  Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ i)

theorem radialDenom_positive {δ : ℝ} (hδ : 0 ≤ δ) (v : ι → ℝ) :
    0 < radialDenom δ v := by
  have hs := radialSquare_nonnegative v
  dsimp [radialDenom]
  positivity

theorem radialMatrixEntry_contDiff {δ : ℝ} (hδ : 0 ≤ δ) (i j : ι) :
    ContDiff ℝ 1 (radialMatrixEntry δ i j) := by
  have hd : ContDiff ℝ 1 (radialDenom δ : (ι → ℝ) → ℝ) := by
    unfold radialDenom radialSquare
    fun_prop
  exact ((contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ j)).div hd
    (fun v => (radialDenom_positive hδ v).ne')

theorem radialMatrixEntry_zero (δ : ℝ) (i j : ι) : radialMatrixEntry δ i j 0 = 0 := by
  simp only [radialMatrixEntry, Pi.zero_apply, zero_mul, zero_div]

theorem abs_coordinate_product_le_radialSquare (v : ι → ℝ) (i j : ι) :
    |v i * v j| ≤ radialSquare v := by
  have hi := coordinate_sq_le_radialSquare v i
  have hj := coordinate_sq_le_radialSquare v j
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (v i + v j)]
  · nlinarith [sq_nonneg (v i - v j)]

theorem radialMatrixEntry_bound {δ : ℝ} (hδ : 0 < δ) (i j : ι) (v : ι → ℝ) :
    |radialMatrixEntry δ i j v| ≤ δ⁻¹ := by
  have hd := radialDenom_positive hδ.le v
  have hp := abs_coordinate_product_le_radialSquare v i j
  have hm : δ * |v i * v j| ≤ radialDenom δ v := by
    dsimp [radialDenom]
    nlinarith
  rw [radialMatrixEntry, abs_div, abs_of_pos hd, div_le_iff₀ hd]
  calc
    _ = δ⁻¹ * (δ * |v i * v j|) := by rw [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hδ.le)

theorem radialMatrixEntry_differential {δ : ℝ} (hδ : 0 ≤ δ) (i j : ι)
    (v w : ι → ℝ) :
    fderiv ℝ (radialMatrixEntry δ i j) v w =
      (w i * v j + v i * w j) / radialDenom δ v -
        (2 * δ * v i * v j * (∑ k, v k * w k)) / radialDenom δ v ^ 2 := by
  have ht (k : ι) : HasDerivAt (fun t : ℝ => v k + t * w k) (w k) 0 := by
    simpa only [one_mul, id_eq] using ((hasDerivAt_id (0 : ℝ)).mul_const (w k)).const_add (v k)
  have hsum : HasDerivAt (fun t : ℝ => ∑ k, (v k + t * w k) ^ 2)
      (∑ k, 2 * v k * w k) 0 := by
    convert HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (ht k).pow 2) using 1 <;> simp
  have hden : HasDerivAt (fun t : ℝ => 1 + δ * ∑ k, (v k + t * w k) ^ 2)
      (δ * ∑ k, 2 * v k * w k) 0 := (hsum.const_mul δ).const_add 1
  have hdn : (1 + δ * ∑ k, (v k + (0 : ℝ) * w k) ^ 2) ≠ 0 := by
    simpa only [radialDenom, radialSquare, zero_mul, add_zero] using (radialDenom_positive hδ v).ne'
  have hq := ((ht i).mul (ht j)).div hden hdn
  have hcurve : HasDerivAt (fun t : ℝ => v + t • w) w 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  have hc : HasDerivAt (fun t : ℝ => radialMatrixEntry δ i j (v + t • w))
      (fderiv ℝ (radialMatrixEntry δ i j) v w) 0 := by
    simpa only [Function.comp_def] using
      ((radialMatrixEntry_contDiff hδ i j).differentiable one_ne_zero v).hasFDerivAt.comp_hasDerivAt_of_eq
        0 hcurve (by simp)
  have hq' : HasDerivAt (fun t : ℝ => radialMatrixEntry δ i j (v + t • w))
      (((w i * v j + v i * w j) * radialDenom δ v -
        v i * v j * (δ * ∑ k, 2 * v k * w k)) / radialDenom δ v ^ 2) 0 := by
    convert hq using 1 <;>
      simp only [radialMatrixEntry, radialDenom, radialSquare, Pi.add_apply,
        Pi.smul_apply, Pi.mul_apply, Pi.div_apply, smul_eq_mul, zero_mul, add_zero] <;> rfl
  have hs : (∑ k, 2 * v k * w k) = 2 * ∑ k, v k * w k := by
    simp only [Finset.mul_sum, mul_assoc]
  rw [hc.unique hq', hs]
  have hd := (radialDenom_positive hδ v).ne'
  field_simp <;> ring

end KLSConstantImprovement.ActualRadialMatrixCalculus405

#print axioms KLSConstantImprovement.ActualRadialMatrixCalculus405.radialMatrixEntry_contDiff
#print axioms KLSConstantImprovement.ActualRadialMatrixCalculus405.radialMatrixEntry_bound
#print axioms KLSConstantImprovement.ActualRadialMatrixCalculus405.radialMatrixEntry_differential
