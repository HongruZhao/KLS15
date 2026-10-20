import Mathlib

/-! Actual geometric-response Gram production: finite Hilbert completion
and scalar consequences only. Source/PDE/natural-row/domain identities
are explicit paper inputs. The extra random-H comparison remains open. -/
noncomputable section
namespace KLSConstantImprovement.GeometricResponseGramProduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem signed_connection_square (r a c : E) :
    ‖r‖^2+‖a‖^2-2*inner ℝ c (r-a) =
      ‖r-c‖^2+‖a+c‖^2-2*‖c‖^2 := by
  rw [norm_sub_sq_real, norm_add_sq_real, inner_sub_right]
  have hrc := real_inner_comm r c
  have hac := real_inner_comm a c
  nlinarith

theorem actual_response_matching_production {lw w p : ℝ} (r a c : E)
    (hsource : lw=w+p+‖r‖^2+‖a‖^2-2*inner ℝ c (r-a)) :
    lw+2*‖c‖^2=w+p+‖r-c‖^2+‖a+c‖^2 := by
  have hs := signed_connection_square r a c
  linarith

theorem actual_response_positive_production {lw w p : ℝ} (r a c : E)
    (hp : 0 ≤ p)
    (hsource : lw=w+p+‖r‖^2+‖a‖^2-2*inner ℝ c (r-a)) :
    w ≤ lw+2*‖c‖^2 := by
  rw [actual_response_matching_production r a c hsource]
  have h1 := sq_nonneg ‖r-c‖
  have h2 := sq_nonneg ‖a+c‖
  linarith

theorem conservative_right_metric_cap {w r p matching d : ℝ}
    (hp : 0 ≤ p) (hm : 0 ≤ matching) (hd : 0 ≤ d)
    (hidentity : 2*r=w+p+matching+4*d) : w ≤ 2*r := by
  linarith

end KLSConstantImprovement.GeometricResponseGramProduction

#print axioms KLSConstantImprovement.GeometricResponseGramProduction.signed_connection_square
#print axioms KLSConstantImprovement.GeometricResponseGramProduction.actual_response_matching_production
#print axioms KLSConstantImprovement.GeometricResponseGramProduction.actual_response_positive_production
#print axioms KLSConstantImprovement.GeometricResponseGramProduction.conservative_right_metric_cap
