import KLSConstantImprovement.SourceThirdAdjointResponse

/-! Same quadratic rows b, their actual diffusion images c = A b, and
e = 2 b - c. The exact source trace identity is an explicit input.
These declarations isolate the weighted response decision gate; they
do not prove its sign or assert a higher source spectral gap. -/
noncomputable section
namespace KLSConstantImprovement.AdjacentQuadraticResponseDefect

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem adjacent_row_norm (b c e : E)
    (he : e = (2 : ℝ) • b - c) :
    ‖e‖^2 = 4*‖b‖^2 - 4*inner ℝ b c + ‖c‖^2 := by
  rw [he, norm_sub_sq_real, norm_smul, real_inner_smul_left]
  norm_num <;> ring

/-- For the same rows c = A b, this is the A(A-1) quadratic form.
The c norm requires the graph domain, not the strong domain of A squared. -/
theorem matched_gram_operator_identity (b c e : E) {r : ℝ}
    (he : e = (2 : ℝ) • b - c)
    (htrace : ‖e‖^2 = 4*‖b‖^2 - 3*inner ℝ b c + r) :
    r = ‖c‖^2 - inner ℝ b c := by
  have h := adjacent_row_norm b c e he
  linarith

theorem unweighted_trace_cap (b c e : E) {r : ℝ}
    (htrace : ‖e‖^2 = 4*‖b‖^2 - 3*inner ℝ b c + r)
    (hBL : ‖b‖^2 ≤ inner ℝ b c) :
    ‖e‖^2 ≤ r + ‖b‖^2 := by
  linarith

/-- C is the same weighted field cost E e^T H e; its sign gate stays open. -/
theorem wider_weighted_gate_iff (b c e : E) {r C : ℝ}
    (htrace : ‖e‖^2 = 4*‖b‖^2 - 3*inner ℝ b c + r) :
    C ≤ r + ‖b‖^2 ↔
      C - ‖e‖^2 ≤ 3*(inner ℝ b c - ‖b‖^2) := by
  constructor <;> intro h <;> linarith

/-- L is the original linear projection norm squared of the same b.
The tighter gate additionally charges its quadratic residual. -/
theorem linear_projection_weighted_gate_iff (b c e : E) {r C L : ℝ}
    (htrace : ‖e‖^2 = 4*‖b‖^2 - 3*inner ℝ b c + r) :
    C ≤ r + L ↔
      C - ‖e‖^2 ≤ 3*(inner ℝ b c - ‖b‖^2) - (‖b‖^2-L) := by
  constructor <;> intro h <;> linarith

theorem wider_response_double_mean {I C r bnorm : ℝ}
    (hresponse : I ≤ C) (hweighted : C ≤ r+bnorm)
    (hquadratic : bnorm ≤ r) : I ≤ 2*r := by
  linarith

/-- The ordinary-source HS rows are identified with z and u explicitly.
Their weighted inner product equals the same row variance. -/
theorem helffer_row_defect_square (z u : E) {bnorm derivativeEnergy : ℝ}
    (hpair : inner ℝ z u = bnorm)
    (henergy : ‖u‖^2 + derivativeEnergy = bnorm) :
    ‖z‖^2-bnorm = ‖z-u‖^2+derivativeEnergy := by
  rw [norm_sub_sq_real]
  linarith

theorem higher_row_defect_split (b c : E) {r : ℝ}
    (hr : r = ‖c‖^2-inner ℝ b c) :
    r = (inner ℝ b c-‖b‖^2)+‖c-b‖^2 := by
  rw [norm_sub_sq_real, real_inner_comm c b]
  rw [real_inner_comm c b] at hr
  linarith

theorem exponential_adjacent_calibration :
    (2 : ℝ) = 5-3 ∧
    (1 : ℝ) = 4*2-3*3+2 ∧
    (3 : ℝ)-1 = 3*(3-2)-(2-1) := by
  norm_num

end KLSConstantImprovement.AdjacentQuadraticResponseDefect
#print axioms KLSConstantImprovement.AdjacentQuadraticResponseDefect.adjacent_row_norm
#print axioms KLSConstantImprovement.AdjacentQuadraticResponseDefect.matched_gram_operator_identity
#print axioms KLSConstantImprovement.AdjacentQuadraticResponseDefect.unweighted_trace_cap
#print axioms KLSConstantImprovement.AdjacentQuadraticResponseDefect.wider_weighted_gate_iff
#print axioms KLSConstantImprovement.AdjacentQuadraticResponseDefect.linear_projection_weighted_gate_iff
#print axioms KLSConstantImprovement.AdjacentQuadraticResponseDefect.wider_response_double_mean
#print axioms KLSConstantImprovement.AdjacentQuadraticResponseDefect.helffer_row_defect_square
#print axioms KLSConstantImprovement.AdjacentQuadraticResponseDefect.higher_row_defect_split
#print axioms KLSConstantImprovement.AdjacentQuadraticResponseDefect.exponential_adjacent_calibration
