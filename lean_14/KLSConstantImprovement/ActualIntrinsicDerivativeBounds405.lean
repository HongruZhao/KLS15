import KLSConstantImprovement.ActualIntrinsicJointCalculus405
import KLSConstantImprovement.ActualIntrinsicRatioBounds405

/-! Uniform bounds for the genuine joint derivatives on the actual positive
metric range. No bound on u is assumed. The lower metric bound is local and
will only be used on compact source sets. -/
noncomputable section
open Matrix
open scoped BigOperators ContDiff
namespace KLSConstantImprovement.ActualIntrinsicDerivativeBounds405
open KLS ActualIntrinsicJointWeakTests405 ActualIntrinsicJointCalculus405
open ActualIntrinsicRatioBounds405 ActualRadialMatrixCalculus405 ActualVectorDifferential405
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def jointDerivativeRatioBound (n : ℕ) (G a : ℝ) : ℝ :=
  ∑ _i : Fin n, ∑ _j : Fin n, (2 * G * (1 + a⁻¹) + a⁻¹)

theorem jointDerivativeRatioBound_nonnegative {G a : ℝ} (hG : 0 ≤ G) (ha : 0 < a) :
    0 ≤ jointDerivativeRatioBound n G a := by
  unfold jointDerivativeRatioBound
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem jointMassDirectional_ratio_le {a f G : ℝ} (ha : 0 < a) (hG : 0 ≤ G)
    (v w : JointIndex n → ℝ)
    (hf : 1 + a * radialSquare (fun i : Fin n => v (.inl i)) ≤ f)
    (hH : ∀ i j, |v (.inr (i,j))| ≤ G) (hw : ∀ b, |w b| ≤ 1) :
    |jointMassDirectional v w| / f ≤ jointDerivativeRatioBound n G a := by
  have hfp := positive_denom_of_radial_lower ha (fun i : Fin n => v (.inl i)) hf
  have hc (i : Fin n) : |v (.inl i)| / f ≤ 1 + a⁻¹ :=
    radial_coordinate_ratio_le ha (fun i : Fin n => v (.inl i)) hf i
  have hp (i j : Fin n) : |v (.inl i) * v (.inl j)| / f ≤ a⁻¹ :=
    radial_pair_ratio_le ha (fun i : Fin n => v (.inl i)) hf i j
  have ht (i j : Fin n) :
      |((w (.inl i) * v (.inr (i,j)) + v (.inl i) * w (.inr (i,j))) * v (.inl j) +
        (v (.inl i) * v (.inr (i,j))) * w (.inl j))| / f ≤
          2 * G * (1 + a⁻¹) + a⁻¹ := by
    have h1 : |w (.inl i) * v (.inr (i,j)) * v (.inl j)| / f ≤ G * (1 + a⁻¹) := by
      calc
        _ = (|w (.inl i)| * |v (.inr (i,j))|) * (|v (.inl j)| / f) := by
          simp only [abs_mul]; ring
        _ ≤ (1 * G) * (1 + a⁻¹) := mul_le_mul
          (mul_le_mul (hw _) (hH i j) (abs_nonneg _) (by norm_num))
          (hc j) (div_nonneg (abs_nonneg _) hfp.le) (by positivity)
        _ = _ := by ring
    have h2 : |v (.inl i) * w (.inr (i,j)) * v (.inl j)| / f ≤ a⁻¹ := by
      calc
        _ = |w (.inr (i,j))| * (|v (.inl i) * v (.inl j)| / f) := by
          simp only [abs_mul]; ring
        _ ≤ 1 * a⁻¹ := mul_le_mul (hw _) (hp i j)
          (div_nonneg (abs_nonneg _) hfp.le) (by norm_num)
        _ = _ := one_mul _
    have h3 : |(v (.inl i) * v (.inr (i,j))) * w (.inl j)| / f ≤ G * (1 + a⁻¹) := by
      calc
        _ = (|v (.inr (i,j))| * |w (.inl j)|) * (|v (.inl i)| / f) := by
          simp only [abs_mul]; ring
        _ ≤ (G * 1) * (1 + a⁻¹) := mul_le_mul
          (mul_le_mul (hH i j) (hw _) (abs_nonneg _) hG)
          (hc i) (div_nonneg (abs_nonneg _) hfp.le) (by positivity)
        _ = _ := by ring
    have he : |((w (.inl i) * v (.inr (i,j)) + v (.inl i) * w (.inr (i,j))) * v (.inl j) +
        (v (.inl i) * v (.inr (i,j))) * w (.inl j))| ≤
          |w (.inl i) * v (.inr (i,j)) * v (.inl j)| +
          |v (.inl i) * w (.inr (i,j)) * v (.inl j)| +
          |(v (.inl i) * v (.inr (i,j))) * w (.inl j)| := by
      rw [add_mul]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have h := div_le_div_of_nonneg_right he hfp.le
    rw [add_div, add_div] at h
    linarith
  calc
    _ ≤ (∑ i : Fin n, ∑ j : Fin n,
        |((w (.inl i) * v (.inr (i,j)) + v (.inl i) * w (.inr (i,j))) * v (.inl j) +
          (v (.inl i) * v (.inr (i,j))) * w (.inl j))|) / f := by
      apply div_le_div_of_nonneg_right _ hfp.le
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i : Fin n, ∑ j : Fin n,
        |((w (.inl i) * v (.inr (i,j)) + v (.inl i) * w (.inr (i,j))) * v (.inl j) +
          (v (.inl i) * v (.inr (i,j))) * w (.inl j))| / f := by
      simp only [Finset.sum_div]
    _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ht i j

theorem intrinsicJointRawEntry_uniform_directional_bound {δ ε c G : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hc : 0 < c) (hG : 0 ≤ G)
    (i j : Fin n) (v w : JointIndex n → ℝ)
    (hM : c * (∑ a : Fin n, v (.inl a) ^ 2) ≤ jointMass v)
    (hH : ∀ a b, |v (.inr (a,b))| ≤ G) (hw : ∀ b, |w b| ≤ 1) :
    |fderiv ℝ (intrinsicJointRawEntry δ ε i j) v w| ≤
      2 * (1 + (δ * c)⁻¹) + δ * (δ * c)⁻¹ * jointDerivativeRatioBound n G (δ * c) := by
  let f := intrinsicJointDenom δ ε v
  let s := Real.sqrt (jointMass v ^ 2 + ε ^ 2)
  have ha : 0 < δ * c := mul_pos hδ hc
  have hs : 0 < s := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (jointMass v)])
  have hfp : 0 < f := intrinsicJointDenom_positive hδ.le v
  have hsr : |jointMass v| ≤ s := by
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_abs (jointMass v), sq_nonneg ε])
  have hf : 1 + (δ * c) * radialSquare (fun a : Fin n => v (.inl a)) ≤ f := by
    have hm : jointMass v ≤ s := (le_abs_self _).trans hsr
    dsimp only [f, intrinsicJointDenom]
    change 1 + (δ * c) * (∑ a : Fin n, v (.inl a) ^ 2) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hM hδ.le,
      mul_le_mul_of_nonneg_left hm hδ.le]
  have hfirst : |w (.inl i) * v (.inl j) + v (.inl i) * w (.inl j)| / f ≤
      2 * (1 + (δ * c)⁻¹) := by
    have hi := radial_coordinate_ratio_le ha (fun a : Fin n => v (.inl a)) hf i
    have hj := radial_coordinate_ratio_le ha (fun a : Fin n => v (.inl a)) hf j
    have h1 : |w (.inl i) * v (.inl j)| / f ≤ 1 + (δ * c)⁻¹ := by
      rw [abs_mul, mul_div_assoc]
      exact (mul_le_mul (hw _) hj (div_nonneg (abs_nonneg _) hfp.le) (by norm_num)).trans_eq (one_mul _)
    have h2 : |v (.inl i) * w (.inl j)| / f ≤ 1 + (δ * c)⁻¹ := by
      rw [mul_comm (v (.inl i)), abs_mul, mul_div_assoc]
      exact (mul_le_mul (hw _) hi (div_nonneg (abs_nonneg _) hfp.le) (by norm_num)).trans_eq (one_mul _)
    have ht := div_le_div_of_nonneg_right (abs_add_le (w (.inl i) * v (.inl j))
      (v (.inl i) * w (.inl j))) hfp.le
    rw [add_div] at ht
    linarith
  have hmratio : |jointMass v| / s ≤ 1 := (div_le_one hs).mpr hsr
  have hdratio := jointMassDirectional_ratio_le ha hG v w hf hH hw
  have hpratio := radial_pair_ratio_le ha (fun a : Fin n => v (.inl a)) hf i j
  have hsecond : |δ * v (.inl i) * v (.inl j) * jointMass v * jointMassDirectional v w| /
      (s * f ^ 2) ≤ δ * (δ * c)⁻¹ * jointDerivativeRatioBound n G (δ * c) := by
    calc
      _ = δ * (|v (.inl i) * v (.inl j)| / f) * (|jointMass v| / s) *
          (|jointMassDirectional v w| / f) := by
        simp only [abs_mul, abs_of_pos hδ]
        field_simp [hfp.ne', hs.ne'] <;> ring
      _ ≤ (δ * (δ * c)⁻¹) * 1 * jointDerivativeRatioBound n G (δ * c) :=
        mul_le_mul (mul_le_mul
          (mul_le_mul_of_nonneg_left hpratio hδ.le) hmratio
          (div_nonneg (abs_nonneg _) hs.le) (by positivity)) hdratio
          (div_nonneg (abs_nonneg _) hfp.le) (by positivity)
      _ = _ := by ring
  rw [intrinsicJointRawEntry_differential hδ.le hε i j v w]
  calc
    _ ≤ |(w (.inl i) * v (.inl j) + v (.inl i) * w (.inl j)) / f| +
        |(δ * v (.inl i) * v (.inl j) * jointMass v * jointMassDirectional v w) /
          (s * f ^ 2)| := abs_sub _ _
    _ = |w (.inl i) * v (.inl j) + v (.inl i) * w (.inl j)| / f +
        |δ * v (.inl i) * v (.inl j) * jointMass v * jointMassDirectional v w| /
          (s * f ^ 2) := by rw [abs_div, abs_div, abs_of_pos hfp, abs_of_pos (by positivity : 0 < s * f ^ 2)]
    _ ≤ _ := add_le_add hfirst hsecond

theorem intrinsicJointRawEntry_uniform_partial_bound {δ ε c G : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hc : 0 < c) (hG : 0 ≤ G)
    (i j : Fin n) (v : JointIndex n → ℝ)
    (hM : c * (∑ a : Fin n, v (.inl a) ^ 2) ≤ jointMass v)
    (hH : ∀ a b, |v (.inr (a,b))| ≤ G) (b : JointIndex n) :
    ‖vectorPartial (intrinsicJointRawEntry δ ε i j) b v‖ ≤
      2 * (1 + (δ * c)⁻¹) + δ * (δ * c)⁻¹ * jointDerivativeRatioBound n G (δ * c) := by
  rw [Real.norm_eq_abs]
  apply intrinsicJointRawEntry_uniform_directional_bound hδ hε hc hG i j v _ hM hH
  intro a
  by_cases h : a = b <;> simp [Pi.single_apply, h]

end KLSConstantImprovement.ActualIntrinsicDerivativeBounds405
#print axioms KLSConstantImprovement.ActualIntrinsicDerivativeBounds405.jointMassDirectional_ratio_le
#print axioms KLSConstantImprovement.ActualIntrinsicDerivativeBounds405.intrinsicJointRawEntry_uniform_directional_bound
#print axioms KLSConstantImprovement.ActualIntrinsicDerivativeBounds405.intrinsicJointRawEntry_uniform_partial_bound
