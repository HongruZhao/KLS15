import ScalarGrowth

/-! Closes the scalar growth-versus-spectrum contradiction. Operator orbit
recurrences and their spectral growth bounds must still be proved for the
actual compatible inverse gradient. -/
noncomputable section
namespace KLSBelow25

theorem no_growth_above_exponential_envelope {b rho M : ℝ} {z : ℕ → ℝ}
    (hrho : 0 < rho) (hb : rho < b)
    (hlower : ∀ j, b ^ j ≤ z j) (hupper : ∀ j, z j ≤ M * rho ^ j) : False := by
  have hratio : 1 < b / rho := (one_lt_div hrho).mpr hb
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt M hratio
  have hbound : (b / rho) ^ j ≤ M := by
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos hrho j)).mpr
    exact (hlower j).trans (hupper j)
  exact (not_lt_of_ge hbound) hj

/-- A positive initial gap is impossible if spectral estimates give an
exponential envelope of every rate rho>1. The envelope is explicit here,
not smuggled in as equality of spectral radius and operator norm. -/
theorem scalar_initial_gap_impossible {epsilon q : ℝ}
    (he : 0 < epsilon) (hq : 0 < q) (hgap : 2 * epsilon < q ^ 2)
    (z : ℕ → ℝ) (hz0 : z 0 = 1)
    (hrec : ∀ j : ℕ, 0 < z j → 0 < z (j + 1) →
      z (j + 1) ^ 2 / z j - epsilon ≤ z (j + 2))
    (henvelope : ∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ j : ℕ, z j ≤ M * rho ^ j) :
    z 1 ≤ 1 + q := by
  by_contra hn
  have hz1 : 1 + q < z 1 := not_le.mp hn
  have hg := scalar_growth_of_initial_gap he hq hgap z hz0 hz1 hrec
  have hk : 0 < Real.sqrt (q ^ 2 - 2 * epsilon) := Real.sqrt_pos.mpr (by linarith)
  let rho : ℝ := 1 + Real.sqrt (q ^ 2 - 2 * epsilon) / 2
  obtain ⟨M, hM⟩ := henvelope rho (by dsimp [rho]; linarith)
  exact no_growth_above_exponential_envelope
    (by dsimp [rho]; linarith : 0 < rho)
    (by dsimp [rho]; linarith : rho < 1 + Real.sqrt (q ^ 2 - 2 * epsilon))
    (fun j => (hg j).2) hM

#print axioms no_growth_above_exponential_envelope
#print axioms scalar_initial_gap_impossible
end KLSBelow25
