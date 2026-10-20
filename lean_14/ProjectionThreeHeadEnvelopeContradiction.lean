import ProjectionSlackEnvelopeContradiction

/-! Four-shift anchor growth contradicts the genuine all-rate envelope. -/
noncomputable section
namespace KLSBelow25.ProjectionSlackRatio

theorem four_shift_growth_contradicts_all_rate_envelope
    (z : ℕ → ℝ) {A gamma : ℝ} (hA : 0 < A) (hgamma : 1 < gamma)
    (hgrowth : ∀ n, A*gamma^n ≤ z (n+4))
    (henvelope : ∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ n, z n ≤ M*rho^n) : False := by
  apply shifted_growth_contradicts_all_rate_envelope (fun n => z (n+1)) hA hgamma
  · intro n
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hgrowth n
  · intro rho hrho
    obtain ⟨M,hM⟩ := henvelope rho hrho
    refine ⟨M*rho, fun n => ?_⟩
    calc
      z (n+1) ≤ M*rho^(n+1) := hM (n+1)
      _ = (M*rho)*rho^n := by rw [pow_succ]; ring

end KLSBelow25.ProjectionSlackRatio
#print axioms KLSBelow25.ProjectionSlackRatio.four_shift_growth_contradicts_all_rate_envelope
