import KLSConstantImprovement.SourceGradientCubicCombinedEnergy

/-! No-optimizer transfer of a source compact-test residual budget.
The actual centered target must lie in the displayed diffusion-range
closure. This is a substantive analytic input, not true for every
boundary-supported original canonical source. The bounded-kernel,
smooth global full-support regular class supplies a separate paper
range-density bridge; its approximation class remains an obligation.
Source pairing, vector Bochner, and the numerical residual90 are explicit.
No universal estimate or new unconditional Poincare endpoint is proved. -/
noncomputable section
open Set
namespace KLSConstantImprovement.SourceCompactCombinedBudgetTransfer
open SourceGradientCubicCombinedEnergy

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {α : Type*}

theorem norm_sq_le_of_mem_closure_range (f : E) (A : α → E) {K : ℝ}
    (hclosure : f ∈ closure (range A))
    (hbudget : ∀ a, 2 * inner ℝ f (A a) - ‖A a‖^2 ≤ K) :
    ‖f‖^2 ≤ K := by
  have hclosed : IsClosed {v : E | 2 * inner ℝ f v - ‖v‖^2 ≤ K} :=
    isClosed_le (by fun_prop) continuous_const
  have hrange : range A ⊆ {v : E | 2 * inner ℝ f v - ‖v‖^2 ≤ K} := by
    rintro v ⟨a, rfl⟩
    exact hbudget a
  have h := (closure_minimal hrange hclosed) hclosure
  change 2 * inner ℝ f f - ‖f‖^2 ≤ K at h
  rw [real_inner_self_eq_norm_sq] at h
  linarith

theorem compact_residual_ninety_gives_norm_budget
    (f : E) (A : α → E) (b : F) (R : α → F)
    (response curvature : α → ℝ) {N : ℝ}
    (hclosure : f ∈ closure (range A))
    (hpair : ∀ a, inner ℝ f (A a) = 3 * inner ℝ (R a) b + 3 * response a)
    (hbochner : ∀ a, ‖A a‖^2 = ‖R a‖^2 + curvature a)
    (hresidual : ∀ a,
      6 * response a - ‖R a - (3:ℝ) • b‖^2 - curvature a ≤ 90 * N) :
    ‖f‖^2 ≤ 9 * ‖b‖^2 + 90 * N := by
  apply norm_sq_le_of_mem_closure_range f A hclosure
  intro a
  have h := source_gradient_objective b (R a) (curvature := curvature a) (hpair a)
  rw [hbochner a]
  nlinarith [hresidual a]

theorem compact_residual_ninety_gives_cubic336
    (f : E) (A : α → E) (b : F) (R : α → F)
    (response curvature : α → ℝ) {N : ℝ}
    (hN : 0 ≤ N)
    (hclosure : f ∈ closure (range A))
    (hpair : ∀ a, inner ℝ f (A a) = 3 * inner ℝ (R a) b + 3 * response a)
    (hbochner : ∀ a, ‖A a‖^2 = ‖R a‖^2 + curvature a)
    (hmain : ‖b‖^2 ≤ (16 + 8 * Real.sqrt 2) * N)
    (hresidual : ∀ a,
      6 * response a - ‖R a - (3:ℝ) • b‖^2 - curvature a ≤ 90 * N) :
    ‖f‖^2 ≤ 336 * N := by
  have h := compact_residual_ninety_gives_norm_budget
    f A b R response curvature hclosure hpair hbochner hresidual
  exact KLSConstantImprovement.HessianMomentScalar.residual_ninety_gives_cubic336
    hN hmain (by linarith)

end KLSConstantImprovement.SourceCompactCombinedBudgetTransfer
#print axioms KLSConstantImprovement.SourceCompactCombinedBudgetTransfer.norm_sq_le_of_mem_closure_range
#print axioms KLSConstantImprovement.SourceCompactCombinedBudgetTransfer.compact_residual_ninety_gives_norm_budget
#print axioms KLSConstantImprovement.SourceCompactCombinedBudgetTransfer.compact_residual_ninety_gives_cubic336
