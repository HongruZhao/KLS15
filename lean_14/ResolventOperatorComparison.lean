import ResolventQuadraticJensen

/-! The positive resolvent operator comparison implies the scalar curvature
comparison needed in the spectral argument. This is an abstract operator
lemma; realization by the actual compatible tensor maps remains separate. -/
noncomputable section
namespace KLSBelow25
open ContinuousLinearMap InnerProductSpace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def integrationGram (R : H →L[ℂ] H) (L : E →L[ℂ] H) : H →L[ℂ] H :=
  R.comp R.adjoint + L.comp L.adjoint

theorem integrationGram_isPositive (R : H →L[ℂ] H) (L : E →L[ℂ] H) :
    (integrationGram R L).IsPositive :=
  (isPositive_self_comp_adjoint R).add (isPositive_self_comp_adjoint L)

theorem integrationGram_quadratic (R : H →L[ℂ] H) (L : E →L[ℂ] H) (v : H) :
    Complex.re ⟪integrationGram R L v, v⟫_ℂ = ‖R.adjoint v‖ ^ 2 + ‖L.adjoint v‖ ^ 2 := by
  have hR := apply_norm_sq_eq_inner_adjoint_left R.adjoint v
  have hL := apply_norm_sq_eq_inner_adjoint_left L.adjoint v
  simp only [adjoint_adjoint] at hR hL
  simp only [integrationGram, add_apply, comp_apply, inner_add_left, Complex.add_re]
  exact congrArg₂ (· + ·) hR.symm hL.symm

/-- No Jensen premise: it is derived from the actual positive inverse. -/
theorem scalar_curvature_comparison_of_resolvent
    (R : H →L[ℂ] H) (L : E →L[ℂ] H) (U : H →L[ℂ] H)
    {a : ℝ} (ha : 0 < a)
    (hU : (1 + a • integrationGram R L) * U = 1)
    (hcomparison : ∀ v : H, ‖R v‖ ^ 2 ≤
      Complex.re ⟪(a⁻¹ • (1 - U)) v, v⟫_ℂ) :
    ∀ v : H, ‖v‖ = 1 → ‖R v‖ ^ 2 ≤
      (‖R.adjoint v‖ ^ 2 + ‖L.adjoint v‖ ^ 2) /
        (1 + a * (‖R.adjoint v‖ ^ 2 + ‖L.adjoint v‖ ^ 2)) := by
  intro v hv
  have hj := complex_resolvent_quadratic_jensen (integrationGram R L) U
    (integrationGram_isPositive R L) ha hU v hv
  rw [integrationGram_quadratic] at hj
  exact (hcomparison v).trans hj

/-- The linear comparison used in the adjoint-orbit recurrence follows
from the same actual positive inverse comparison. -/
theorem linear_curvature_comparison_of_resolvent
    (R : H →L[ℂ] H) (L : E →L[ℂ] H) (U : H →L[ℂ] H)
    {a : ℝ} (ha : 0 < a)
    (hU : (1 + a • integrationGram R L) * U = 1)
    (hcomparison : ∀ v : H, ‖R v‖ ^ 2 ≤
      Complex.re ⟪(a⁻¹ • (1 - U)) v, v⟫_ℂ) :
    ∀ v : H, ‖R v‖ ^ 2 ≤ ‖R.adjoint v‖ ^ 2 + ‖L.adjoint v‖ ^ 2 := by
  intro v
  have hj := complex_resolvent_quadratic_le_argument (integrationGram R L) U
    (integrationGram_isPositive R L) ha hU v
  rw [integrationGram_quadratic] at hj
  exact (hcomparison v).trans hj

#print axioms linear_curvature_comparison_of_resolvent

#print axioms integrationGram_isPositive
#print axioms integrationGram_quadratic
#print axioms scalar_curvature_comparison_of_resolvent
end KLSBelow25
