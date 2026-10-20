import ProjectionSlackFiniteAnchor
import JointObservationScalarEndgame

/-! Finite projection-slack anchor growth contradicts the existing all-rate
spectral envelope. This helper has no new universal numeric conclusion. -/
noncomputable section
namespace KLSBelow25.ProjectionSlackRatio
open KLSBelow25.CoupledEnergy

theorem shifted_growth_contradicts_all_rate_envelope
    (z : ℕ → ℝ) {A gamma : ℝ} (hA : 0 < A) (hgamma : 1 < gamma)
    (hgrowth : ∀ n, A*gamma^n ≤ z (n+3))
    (henvelope : ∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ n, z n ≤ M*rho^n) : False := by
  let rho : ℝ := (1+gamma)/2
  have hrho : 1 < rho := by dsimp [rho]; linarith
  obtain ⟨M,hM⟩ := henvelope rho hrho
  have hlower (n : ℕ) : gamma^n ≤ z (n+3)/A := by
    apply (le_div_iff₀ hA).mpr
    simpa only [mul_comm] using hgrowth n
  have hupper (n : ℕ) : z (n+3)/A ≤ ((M*rho^3)/A)*rho^n := by
    calc
      _ ≤ (M*rho^(n+3))/A := div_le_div_of_nonneg_right (hM (n+3)) hA.le
      _ = _ := by rw [pow_add]; ring
  exact no_growth_above_exponential_envelope
    (by linarith : 0 < rho) (by dsimp [rho]; linarith : rho < gamma) hlower hupper

end KLSBelow25.ProjectionSlackRatio
#print axioms KLSBelow25.ProjectionSlackRatio.shifted_growth_contradicts_all_rate_envelope
