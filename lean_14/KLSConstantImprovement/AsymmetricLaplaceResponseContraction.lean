import Mathlib

/-! Exact scalar consequences of the natural one-dimensional all-rate
asymmetric Laplace response. Actual probability, kernel and response
bindings are paper proofs, not a universal response hypothesis.
No dependent-law/general-tensor or new Poincare endpoint is asserted. -/
noncomputable section
namespace KLSConstantImprovement.AsymmetricLaplaceResponseContraction

def response (r : ℝ) : ℝ := (2-3*r^2+2*r^4)/(1+r^2)^2
def quadratic (r : ℝ) : ℝ := (2+r^2+2*r^4)/(1+r^2)^2

theorem exact_gap (r : ℝ) :
    quadratic r-response r = 4*r^2/(1+r^2)^2 := by
  have hn : (1+r^2:ℝ) ≠ 0 := by nlinarith [sq_nonneg r]
  unfold response quadratic
  field_simp
  <;> ring

theorem scalar_response_contraction (r : ℝ) :
    0 ≤ response r ∧ response r ≤ quadratic r := by
  constructor
  · apply div_nonneg
    · have h := sq_nonneg (r^2-(3/4:ℝ))
      nlinarith
    · exact sq_nonneg _
  · have hg : 0 ≤ quadratic r-response r := by
      rw [exact_gap]
      positivity
    linarith

theorem actual_scalar_calibrations :
    response (1/2)=22/25 ∧ quadratic (1/2)=38/25 ∧
    response (1/5)=1177/676 ∧ quadratic (1/5)=1277/676 ∧
    response 0=2 ∧ quadratic 0=2 := by
  norm_num [response,quadratic]

end KLSConstantImprovement.AsymmetricLaplaceResponseContraction
#print axioms KLSConstantImprovement.AsymmetricLaplaceResponseContraction.exact_gap
#print axioms KLSConstantImprovement.AsymmetricLaplaceResponseContraction.scalar_response_contraction
#print axioms KLSConstantImprovement.AsymmetricLaplaceResponseContraction.actual_scalar_calibrations
