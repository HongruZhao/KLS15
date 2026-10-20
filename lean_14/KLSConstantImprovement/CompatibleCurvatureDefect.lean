import Mathlib

/-! The compatible combined field minus the same Poisson Hessian is the
curvature representer. The original-law pairing and Bochner identities
are explicit inputs. These statements do not pay a universal budget. -/
noncomputable section
namespace KLSConstantImprovement.CompatibleCurvatureDefect

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem curvature_defect_pairing (f s : E) {V curvature : ℝ}
    (hpair : V = inner ℝ f s)
    (hbochner : V = ‖s‖ ^ 2 + curvature) :
    inner ℝ (f-s) s = curvature := by
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  linarith

theorem combined_energy_exact_decomposition (f s : E) {V curvature : ℝ}
    (hpair : V = inner ℝ f s)
    (hbochner : V = ‖s‖ ^ 2 + curvature) :
    ‖f‖ ^ 2 = V + curvature + ‖f-s‖ ^ 2 := by
  rw [norm_sub_sq_real]
  linarith

/-- The norm-only sufficient budget asks for an extra nonnegative
curvature-defect payment beyond the original variance target. -/
theorem combined_budget_iff_variance_plus_defect (f s : E)
    {V curvature budget : ℝ}
    (hpair : V = inner ℝ f s)
    (hbochner : V = ‖s‖ ^ 2 + curvature) :
    (‖f‖ ^ 2 ≤ budget + curvature) ↔
      (V + ‖f-s‖ ^ 2 ≤ budget) := by
  have h := combined_energy_exact_decomposition f s hpair hbochner
  constructor <;> intro hb <;> linarith

end KLSConstantImprovement.CompatibleCurvatureDefect
#print axioms KLSConstantImprovement.CompatibleCurvatureDefect.curvature_defect_pairing
#print axioms KLSConstantImprovement.CompatibleCurvatureDefect.combined_energy_exact_decomposition
#print axioms KLSConstantImprovement.CompatibleCurvatureDefect.combined_budget_iff_variance_plus_defect
