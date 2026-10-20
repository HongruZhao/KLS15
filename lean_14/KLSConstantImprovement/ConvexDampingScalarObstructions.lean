import Mathlib

/-! Exact scalar calibrations for the convex-damping route.
The moment and potential-variation identifications are explicit inputs.
These calculations obstruct monotonicity, not a paid relative barrier.
-/
noncomputable section
namespace KLSConstantImprovement.ConvexDampingScalarObstructions

theorem gamma_two_hinge_covariance_derivative {E w xw x₂w : ℝ}
    (_hE : 0 < E) (hw : w=3/E) (hxw : xw=11/E) (hx₂w : x₂w=49/E) :
    -(x₂w-4*xw+2*w) = -11/E := by
  rw [hw,hxw,hx₂w]
  ring

theorem gamma_two_whitened_hinge_values {E : ℝ} (hE : 0 < E) :
    ((-5175/E)-3*312*(-11/E)/2)/8 = -27/(8*E) ∧
    ((-16916/E)-3*1020*(-11/E)/2)/8 = -43/(4*E) := by
  constructor <;> field_simp <;> ring

theorem gamma_two_whitened_hinge_decreases {E : ℝ} (hE : 0 < E) :
    ((-5175/E)-3*312*(-11/E)/2)/8 < 0 ∧
    ((-16916/E)-3*1020*(-11/E)/2)/8 < 0 := by
  rw [(gamma_two_whitened_hinge_values hE).1,
    (gamma_two_whitened_hinge_values hE).2]
  constructor
  · exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  · exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

theorem gamma_two_at_exp_one :
    ((-5175/Real.exp 1)-3*312*(-11/Real.exp 1)/2)/8 < 0 ∧
    ((-16916/Real.exp 1)-3*1020*(-11/Real.exp 1)/2)/8 < 0 :=
  gamma_two_whitened_hinge_decreases (Real.exp_pos 1)

end KLSConstantImprovement.ConvexDampingScalarObstructions
#print axioms KLSConstantImprovement.ConvexDampingScalarObstructions.gamma_two_hinge_covariance_derivative
#print axioms KLSConstantImprovement.ConvexDampingScalarObstructions.gamma_two_whitened_hinge_values
#print axioms KLSConstantImprovement.ConvexDampingScalarObstructions.gamma_two_whitened_hinge_decreases
#print axioms KLSConstantImprovement.ConvexDampingScalarObstructions.gamma_two_at_exp_one
