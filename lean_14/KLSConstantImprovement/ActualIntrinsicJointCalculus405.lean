import KLSConstantImprovement.ActualIntrinsicJointWeakTests405
import KLSConstantImprovement.ActualRadialMatrixCalculus405

/-! The intrinsic joint test before compactification, with its literal
finite-dimensional differential. Uniform lower bounds on the actual H on
compact source sets control its value independently of both regularizations.
No derivative of the raw source Hessian is used in this finite calculus. -/
noncomputable section
open Filter Matrix
open scoped BigOperators Topology ContDiff
namespace KLSConstantImprovement.ActualIntrinsicJointCalculus405
open KLS ActualIntrinsicJointWeakTests405 ActualVectorDifferential405 ActualRadialMatrixCalculus405 ActualSmoothScalarTruncation405
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def intrinsicJointRawEntry (δ ε : ℝ) (i j : Fin n) (v : JointIndex n → ℝ) : ℝ :=
  v (.inl i) * v (.inl j) / intrinsicJointDenom δ ε v

def jointMassDirectional (v w : JointIndex n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    ((w (.inl i) * v (.inr (i,j)) + v (.inl i) * w (.inr (i,j))) * v (.inl j) +
      (v (.inl i) * v (.inr (i,j))) * w (.inl j))

theorem intrinsicJointRawEntry_contDiff {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε)
    (i j : Fin n) : ContDiff ℝ 1 (intrinsicJointRawEntry δ ε i j) := by
  have hm : ContDiff ℝ 1 (jointMass : (JointIndex n → ℝ) → ℝ) := by
    unfold jointMass
    fun_prop
  have hr : ContDiff ℝ 1 (fun v : JointIndex n → ℝ => Real.sqrt (jointMass v ^ 2 + ε ^ 2)) :=
    ((hm.pow 2).add contDiff_const).sqrt (fun v => by nlinarith [sq_nonneg (jointMass v)])
  have hd : ContDiff ℝ 1 (intrinsicJointDenom δ ε : (JointIndex n → ℝ) → ℝ) :=
    contDiff_const.add (contDiff_const.mul hr)
  exact ((contDiff_apply ℝ ℝ (.inl i)).mul (contDiff_apply ℝ ℝ (.inl j))).div hd
    (fun v => (intrinsicJointDenom_positive hδ v).ne')

theorem intrinsicJointRawEntry_differential {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε)
    (i j : Fin n) (v w : JointIndex n → ℝ) :
    fderiv ℝ (intrinsicJointRawEntry δ ε i j) v w =
      (w (.inl i) * v (.inl j) + v (.inl i) * w (.inl j)) / intrinsicJointDenom δ ε v -
        (δ * v (.inl i) * v (.inl j) * jointMass v * jointMassDirectional v w) /
          (Real.sqrt (jointMass v ^ 2 + ε ^ 2) * intrinsicJointDenom δ ε v ^ 2) := by
  have ht (a : JointIndex n) : HasDerivAt (fun t : ℝ => v a + t * w a) (w a) 0 := by
    simpa only [one_mul, id_eq] using ((hasDerivAt_id (0 : ℝ)).mul_const (w a)).const_add (v a)
  have hm : HasDerivAt (fun t : ℝ => jointMass (v + t • w)) (jointMassDirectional v w) 0 := by
    have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
        ((ht (.inl i)).mul (ht (.inr (i,j)))).mul (ht (.inl j))))
    simpa [jointMass, jointMassDirectional, Pi.mul_apply] using hs
  have hn : jointMass v ^ 2 + ε ^ 2 ≠ 0 := by nlinarith [sq_nonneg (jointMass v)]
  have hroot := ((hm.pow 2).add_const (ε ^ 2)).sqrt (by simpa using hn)
  have hd := (hroot.const_mul δ).const_add 1
  have hdn : intrinsicJointDenom δ ε v ≠ 0 := (intrinsicJointDenom_positive hδ v).ne'
  have hq := ((ht (.inl i)).mul (ht (.inl j))).div hd (by simpa [intrinsicJointDenom, Pi.pow_apply] using hdn)
  have hcurve : HasDerivAt (fun t : ℝ => v + t • w) w 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  have hc : HasDerivAt (fun t : ℝ => intrinsicJointRawEntry δ ε i j (v + t • w))
      (fderiv ℝ (intrinsicJointRawEntry δ ε i j) v w) 0 := by
    simpa only [Function.comp_def] using
      ((intrinsicJointRawEntry_contDiff hδ hε i j).differentiable one_ne_zero v).hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve (by simp)
  have hq' : HasDerivAt (fun t : ℝ => intrinsicJointRawEntry δ ε i j (v + t • w))
      (((w (.inl i) * v (.inl j) + v (.inl i) * w (.inl j)) * intrinsicJointDenom δ ε v -
        (v (.inl i) * v (.inl j)) *
          (δ * ((2 * jointMass v * jointMassDirectional v w) /
            (2 * Real.sqrt (jointMass v ^ 2 + ε ^ 2))))) /
        intrinsicJointDenom δ ε v ^ 2) 0 := by
    convert hq using 1 <;> (try funext t) <;>
      simp [intrinsicJointRawEntry, intrinsicJointDenom, Pi.mul_apply, Pi.pow_apply, Pi.div_apply]
  rw [hc.unique hq']
  have hs : Real.sqrt (jointMass v ^ 2 + ε ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (jointMass v)])).ne'
  field_simp <;> ring

theorem jointBump_nonnegative_le_one (k : ℕ) (v : JointIndex n → ℝ) :
    0 ≤ jointBump k v ∧ jointBump k v ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg fun _ _ => scalarBump.nonneg
  · exact Finset.prod_le_one₀ (fun _ _ => scalarBump.nonneg) (fun _ _ => scalarBump.le_one)

theorem intrinsicJointRawEntry_bound {δ ε c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (i j : Fin n) (v : JointIndex n → ℝ)
    (hM : c * (∑ a : Fin n, v (.inl a) ^ 2) ≤ jointMass v) :
    |intrinsicJointRawEntry δ ε i j v| ≤ (δ * c)⁻¹ := by
  let r : ℝ := ∑ a : Fin n, v (.inl a) ^ 2
  have hr : 0 ≤ r := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmn : 0 ≤ jointMass v := (mul_nonneg hc.le hr).trans hM
  have hs : jointMass v ≤ Real.sqrt (jointMass v ^ 2 + ε ^ 2) := by
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ε])
  have hp : |v (.inl i) * v (.inl j)| ≤ r :=
    abs_coordinate_product_le_radialSquare (fun a : Fin n => v (.inl a)) i j
  have hd := intrinsicJointDenom_positive hδ.le (ε := ε) v
  have hm : (δ * c) * |v (.inl i) * v (.inl j)| ≤ intrinsicJointDenom δ ε v := by
    dsimp only [intrinsicJointDenom]
    have hmul := mul_le_mul_of_nonneg_left hM hδ.le
    have hmul' := mul_le_mul_of_nonneg_left hs hδ.le
    nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg hδ.le hc.le)]
  rw [intrinsicJointRawEntry, abs_div, abs_of_pos hd, div_le_iff₀ hd]
  calc
    _ = (δ * c)⁻¹ * ((δ * c) * |v (.inl i) * v (.inl j)|) := by
      rw [← mul_assoc, inv_mul_cancel₀ (mul_pos hδ hc).ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr (mul_nonneg hδ.le hc.le))

theorem intrinsicJointMatrixEntry_uniform_bound {δ ε c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (k : ℕ) (i j : Fin n) (v : JointIndex n → ℝ)
    (hM : c * (∑ a : Fin n, v (.inl a) ^ 2) ≤ jointMass v) :
    |intrinsicJointMatrixEntry δ ε k i j v| ≤ (δ * c)⁻¹ := by
  change |jointBump k v * intrinsicJointRawEntry δ ε i j v| ≤ _
  rw [abs_mul, abs_of_nonneg (jointBump_nonnegative_le_one k v).1]
  calc
    _ ≤ 1 * (δ * c)⁻¹ := mul_le_mul (jointBump_nonnegative_le_one k v).2
      (intrinsicJointRawEntry_bound hδ hc i j v hM) (abs_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := one_mul _

end KLSConstantImprovement.ActualIntrinsicJointCalculus405
#print axioms KLSConstantImprovement.ActualIntrinsicJointCalculus405.intrinsicJointRawEntry_contDiff
#print axioms KLSConstantImprovement.ActualIntrinsicJointCalculus405.intrinsicJointRawEntry_differential
#print axioms KLSConstantImprovement.ActualIntrinsicJointCalculus405.intrinsicJointRawEntry_bound
#print axioms KLSConstantImprovement.ActualIntrinsicJointCalculus405.intrinsicJointMatrixEntry_uniform_bound
