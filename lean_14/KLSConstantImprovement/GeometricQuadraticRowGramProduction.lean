import Mathlib

/-! Finite Hilbert consequences of the actual geometric quadratic-row Gram
production. Actual source, Poisson row construction, product rule and domain
are paper identifications. No universal extra-metric or CP bound is asserted. -/
noncomputable section
namespace KLSConstantImprovement.GeometricQuadraticRowGramProduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem mixed_connection_gram_completion (d k a l : E) :
    inner ℝ k l+inner ℝ d l+inner ℝ k a+2*inner ℝ d a =
      inner ℝ (d+k) (a+l)+inner ℝ d a := by
  simp only [inner_add_left, inner_add_right]
  ring

theorem actual_row_matching_square {lw p : ℝ} (u z r d : E)
    (hsource : lw=‖u‖^2-2*inner ℝ z u+p+‖r‖^2+‖d‖^2) :
    lw+‖z‖^2=‖z-u‖^2+p+‖r‖^2+‖d‖^2 := by
  rw [norm_sub_sq_real]
  linarith

theorem actual_row_positive_production {lw p : ℝ} (u z r d : E)
    (hp : 0 ≤ p)
    (hsource : lw=‖u‖^2-2*inner ℝ z u+p+‖r‖^2+‖d‖^2) :
    0 ≤ lw+‖z‖^2 := by
  rw [actual_row_matching_square u z r d hsource]
  positivity

theorem matched_metric_pair_keeps_signed_charge {M J charge loss : ℝ}
    (hpair : -M+charge=-J+loss) : M+loss=J+charge := by
  linarith

end KLSConstantImprovement.GeometricQuadraticRowGramProduction

#print axioms KLSConstantImprovement.GeometricQuadraticRowGramProduction.mixed_connection_gram_completion
#print axioms KLSConstantImprovement.GeometricQuadraticRowGramProduction.actual_row_matching_square
#print axioms KLSConstantImprovement.GeometricQuadraticRowGramProduction.actual_row_positive_production
#print axioms KLSConstantImprovement.GeometricQuadraticRowGramProduction.matched_metric_pair_keeps_signed_charge
