import Mathlib

/-! Exact scalar consequences of the fixed-tensor tilt-deficit identities.
The universal lower-curvature estimate is an explicit theorem hypothesis.
Signed trace square S is never replaced by a squared norm or assumed positive.
-/
noncomputable section
namespace KLSConstantImprovement.DeficitCurvatureScalar
set_option maxHeartbeats 2000000

theorem deficit_variance_identity {J V F S N K6 : ℝ}
    (hJ : J=12*F+12*S-K6) (hV : V=K6+9*F+9*S+6*N) :
    J+V=21*F+21*S+6*N := by linarith

theorem curvature_conversion {J V F S N k : ℝ}
    (hidentity : J+V=21*F+21*S+6*N)
    (hcurvature : -k*(6*N-F) ≤ J) :
    V ≤ (21-k)*F+21*S+(6+6*k)*N := by nlinarith

theorem curvature_small_coefficient {J V F S N k : ℝ}
    (hidentity : J+V=21*F+21*S+6*N)
    (hcurvature : -k*(6*N-F) ≤ J) (hk : k ≤ 21)
    (hF : F ≤ 6*N) (hS : S ≤ (16/3 : ℝ)*N) : V ≤ 244*N := by
  have hc := curvature_conversion hidentity hcurvature
  have hp := mul_le_mul_of_nonneg_left hF (show 0 ≤ 21-k by linarith)
  nlinarith

theorem curvature_large_coefficient {J V F S N k : ℝ}
    (hidentity : J+V=21*F+21*S+6*N)
    (hcurvature : -k*(6*N-F) ≤ J) (hk : 21 ≤ k)
    (hF : -2*N ≤ F) (hS : S ≤ (16/3 : ℝ)*N) : V ≤ (8*k+76)*N := by
  have hc := curvature_conversion hidentity hcurvature
  have hp := mul_le_mul_of_nonpos_left hF (show 21-k ≤ 0 by linarith)
  nlinarith

theorem curvature_65over2_gives_cubic336 {J V F S N : ℝ}
    (hidentity : J+V=21*F+21*S+6*N)
    (hcurvature : -(65/2 : ℝ)*(6*N-F) ≤ J)
    (hF : -2*N ≤ F) (hS : S ≤ (16/3 : ℝ)*N) : V ≤ 336*N := by
  have h := curvature_large_coefficient hidentity hcurvature (by norm_num) hF hS
  norm_num at h
  exact h

theorem curvature_34_gives_cubic348 {J V F S N : ℝ}
    (hidentity : J+V=21*F+21*S+6*N)
    (hcurvature : -(34 : ℝ)*(6*N-F) ≤ J)
    (hF : -2*N ≤ F) (hS : S ≤ (16/3 : ℝ)*N) : V ≤ 348*N := by
  have h := curvature_large_coefficient hidentity hcurvature (by norm_num) hF hS
  norm_num at h
  exact h

theorem curvature_65over2_iff_sixth_cumulant {J F S N K6 : ℝ}
    (hJ : J=12*F+12*S-K6) :
    (-(65/2 : ℝ)*(6*N-F) ≤ J) ↔
      K6+(41/2 : ℝ)*F-12*S ≤ 195*N := by
  constructor <;> intro h <;> nlinarith

theorem curvature_three_iff_sixth_cumulant {J F S N K6 : ℝ}
    (hJ : J=12*F+12*S-K6) :
    (-(3 : ℝ)*(6*N-F) ≤ J) ↔ K6 ≤ 9*F+12*S+18*N := by
  constructor <;> intro h <;> nlinarith

theorem curvature_monotone {J D k₁ k₂ : ℝ} (hD : 0 ≤ D)
    (hk : k₁ ≤ k₂) (hcurvature : -k₁*D ≤ J) : -k₂*D ≤ J := by
  have h := mul_le_mul_of_nonneg_right hk hD
  linarith

theorem integrated_kernel_gate_iff {J D K : ℝ} (hK : K=J+4*D) :
    -(65/2 : ℝ)*D ≤ J ↔ 0 ≤ K+(57/2 : ℝ)*D := by
  constructor <;> intro h <;> nlinarith

theorem integrated_six_square_balance_iff {K A R D : ℝ}
    (hK : K=(19/3 : ℝ)*R-(2/3 : ℝ)*A) :
    0 ≤ K+(57/2 : ℝ)*D ↔ A ≤ (19/2 : ℝ)*R+(171/4 : ℝ)*D := by
  constructor <;> intro h <;> nlinarith

end KLSConstantImprovement.DeficitCurvatureScalar
#print axioms KLSConstantImprovement.DeficitCurvatureScalar.deficit_variance_identity
#print axioms KLSConstantImprovement.DeficitCurvatureScalar.curvature_small_coefficient
#print axioms KLSConstantImprovement.DeficitCurvatureScalar.curvature_large_coefficient
#print axioms KLSConstantImprovement.DeficitCurvatureScalar.curvature_65over2_gives_cubic336
#print axioms KLSConstantImprovement.DeficitCurvatureScalar.curvature_34_gives_cubic348
#print axioms KLSConstantImprovement.DeficitCurvatureScalar.curvature_65over2_iff_sixth_cumulant
#print axioms KLSConstantImprovement.DeficitCurvatureScalar.curvature_three_iff_sixth_cumulant
#print axioms KLSConstantImprovement.DeficitCurvatureScalar.curvature_monotone
#print axioms KLSConstantImprovement.DeficitCurvatureScalar.integrated_kernel_gate_iff
#print axioms KLSConstantImprovement.DeficitCurvatureScalar.integrated_six_square_balance_iff
