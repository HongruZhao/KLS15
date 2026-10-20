import KLSConstantImprovement.SourceThirdAdjointResponse

/-! Scalar conservative-cutoff and finite quartic consequences.
The actual response Gram PDE, Kato inequality, source integration
and cutoff convergence remain explicit analytic identifications.
M is a per-law source bound; no uniform endpoint is claimed. -/
noncomputable section
open Filter Topology
namespace KLSConstantImprovement.ResponseGramCutoffBound

theorem cutoff_positive_mass_zero {v : ℝ} (hv : 0 ≤ v)
    (mass boundary : ℕ → ℝ)
    (hMass : Tendsto mass atTop (𝓝 v))
    (hBoundary : Tendsto boundary atTop (𝓝 0))
    (hCutoff : ∀ n, mass n ≤ boundary n) : v = 0 := by
  have hUpper : v ≤ 0 := le_of_tendsto_of_tendsto hMass hBoundary
    (Filter.Eventually.of_forall hCutoff)
  exact le_antisymm hUpper hv

theorem scalar_bound_from_cutoff_excess {f c : ℝ}
    (mass boundary : ℕ → ℝ)
    (hMass : Tendsto mass atTop (𝓝 (max (f-c) 0)))
    (hBoundary : Tendsto boundary atTop (𝓝 0))
    (hCutoff : ∀ n, mass n ≤ boundary n) : f ≤ c := by
  have hZero := cutoff_positive_mass_zero (le_max_right (f-c) 0)
    mass boundary hMass hBoundary hCutoff
  have h := le_max_left (f-c) 0
  rw [hZero] at h
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem response_gram_quartic_compensation (W G : E)
    {generator production energy kappa : ℝ}
    (hProduction : 0 ≤ production)
    (hForcing : ‖G‖^2 ≤ kappa)
    (hPDE : generator = ‖W‖^2-2*inner ℝ W G+production+energy) :
    energy ≤ generator+kappa := by
  have hs := sq_nonneg (‖W-G‖)
  rw [norm_sub_sq_real] at hs
  linarith

theorem response_gram_positive_generator (W G : E)
    {generator production energy kappa : ℝ}
    (hProduction : 0 ≤ production)
    (hEnergy : 0 ≤ energy)
    (hForcing : ‖G‖^2 ≤ kappa)
    (hPDE : generator = ‖W‖^2-2*inner ℝ W G+production+energy) :
    0 ≤ generator+‖W‖^2/2+kappa := by
  have h := response_gram_quartic_compensation W G hProduction hForcing hPDE
  have hs := sq_nonneg (‖W‖)
  linarith

end KLSConstantImprovement.ResponseGramCutoffBound
#print axioms KLSConstantImprovement.ResponseGramCutoffBound.cutoff_positive_mass_zero
#print axioms KLSConstantImprovement.ResponseGramCutoffBound.scalar_bound_from_cutoff_excess
#print axioms KLSConstantImprovement.ResponseGramCutoffBound.response_gram_quartic_compensation
#print axioms KLSConstantImprovement.ResponseGramCutoffBound.response_gram_positive_generator
