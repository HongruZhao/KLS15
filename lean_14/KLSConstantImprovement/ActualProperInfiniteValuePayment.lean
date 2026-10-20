import KLSConstantImprovement.ClippedRunningRatioMinimum

/-! The proper positive-terminal value is paid by arbitrary actual
normalized orbits, including rising ratios and zeros.  Conversely a
compatible minimizing path realizes an exact positive scalar orbit.
This proves sharpness for the displayed normalized scalar constraints;
it does not construct an admissible probability law realizing the orbit.
The outer generator-profile minimum is a separate problem.

This isolated source draft has not been compiled by its author. -/

noncomputable section
namespace KLSConstantImprovement.ActualProperInfiniteValuePayment

open KLSConstantImprovement.CompatibleRatioPathCompact
open KLSConstantImprovement.ProperInfiniteRatioPathSelection
open KLSConstantImprovement.ProperInfiniteRatioPathMinimum
open KLSConstantImprovement.SubexponentialTerminalSupremum
open KLSConstantImprovement.WeightedOrbitBellmanTail
open KLSConstantImprovement.RatioPathOrbitRealization

/-- Infinite value payment for every original scalar orbit, with no
decreasing-ratio hypothesis and no global positive weight floor. -/
theorem actual_infinite_value_payment {A C : ℝ} (Z c w : ℕ → ℝ)
    (hA : 0 ≤ A) (hF : Nonempty (Floor w))
    (hZ : ∀ n : ℕ, 0 ≤ Z n) (hc : ∀ n : ℕ, 0 ≤ c n)
    (hZ0 : Z 0 = 1) (hp : 1 ≤ Z 1)
    (hrec : ∀ i : ℕ, 0 < Z i → 0 < Z (i + 1) →
      Z (i + 1) ^ 2 / Z i - c i ≤ Z (i + 2))
    (hcap : ∀ i : ℕ, c i ≤ A * Z i)
    (hbudget : ∀ N : ℕ, spend w c N ≤ C)
    (henv : ∀ q : ℝ, 1 < q → ∃ M : ℝ, ∀ i : ℕ, Z i ≤ M * q ^ i) :
    Z 1 * infiniteValue A (Z 1) w ≤ C := by
  let r := ClippedRunningRatioMinimum.running Z
  have hr : r ∈ ratioPathSet A (Z 1) :=
    ClippedRunningRatioMinimum.running_mem hA hZ hc hZ0 hp hrec hcap
  have hproper : Proper r :=
    ClippedRunningRatioMinimum.running_proper hA hZ hc hZ0 hp hrec hcap henv
  have hp0 : 0 < Z 1 := by linarith
  have hnormbudget (N : ℕ) : prefixSpend w r N ≤ C / Z 1 := by
    apply (le_div_iff₀ hp0).mpr
    have hh := (ClippedRunningRatioMinimum.prefix_payment hZ hc
      (weight_nonnegative hF) hZ0 hp hrec N).trans (hbudget N)
    simpa only [mul_comm] using hh
  have hh := infiniteValue_le_of_proper_budget hr hF hproper hnormbudget
  simpa only [mul_comm] using (le_div_iff₀ hp0).mp hh

/-- A proper selected path realizes a positive normalized scalar optimizer.
The factor `p` is retained in every actual weighted prefix budget. -/
theorem exists_exact_scalar_optimizer {A p : ℝ} {w : ℕ → ℝ}
    (hA : 0 < A) (hp : 1 ≤ p) (hw : FullFloors w) :
    ∃ Z c : ℕ → ℝ, Z 0 = 1 ∧ Z 1 = p ∧
      (∀ i : ℕ, 0 < Z i) ∧ (∀ i : ℕ, 0 ≤ c i) ∧
      (∀ i : ℕ, Z (i + 1) ^ 2 / Z i - c i = Z (i + 2)) ∧
      (∀ i : ℕ, c i ≤ A * Z i) ∧
      (∀ N : ℕ, spend w c N ≤ p * infiniteValue A p w) ∧
      (∀ q : ℝ, 1 < q → ∃ M : ℝ, ∀ i : ℕ, Z i ≤ M * q ^ i) := by
  obtain ⟨r, hr, hproper, hbudget, hcost, hminimal⟩ := attained_scalar_minimum hA hp hw
  refine ⟨orbitZ r p, orbitC r p, rfl, orbitZ_one r p,
    orbitZ_pos hr, orbitC_nonneg hr, orbit_recurrence hr, orbit_cap hr, ?_, ?_⟩
  · intro N
    rw [spend_eq]
    exact mul_le_mul_of_nonneg_left (hbudget N) (by linarith : 0 ≤ p)
  · exact orbitZ_envelope r hp hproper

/-- The literal infinite formula is the attained least feasible budget for
all normalized scalar orbits with the displayed recurrence, cap, and
all-rate growth constraints. This is not a lower bound for the KLS constant. -/
theorem attained_least_normalized_scalar_budget {A p : ℝ} {w : ℕ → ℝ}
    (hA : 0 < A) (hp : 1 ≤ p) (hw : FullFloors w) :
    (∃ Z c : ℕ → ℝ, Z 0 = 1 ∧ Z 1 = p ∧
      (∀ i : ℕ, 0 < Z i) ∧ (∀ i : ℕ, 0 ≤ c i) ∧
      (∀ i : ℕ, Z (i + 1) ^ 2 / Z i - c i = Z (i + 2)) ∧
      (∀ i : ℕ, c i ≤ A * Z i) ∧
      (∀ N : ℕ, spend w c N ≤ p * infiniteValue A p w) ∧
      (∀ q : ℝ, 1 < q → ∃ M : ℝ, ∀ i : ℕ, Z i ≤ M * q ^ i)) ∧
    (∀ Z c : ℕ → ℝ, ∀ C : ℝ,
      (∀ i : ℕ, 0 ≤ Z i) → (∀ i : ℕ, 0 ≤ c i) → Z 0 = 1 → Z 1 = p →
      (∀ i : ℕ, 0 < Z i → 0 < Z (i + 1) →
        Z (i + 1) ^ 2 / Z i - c i ≤ Z (i + 2)) →
      (∀ i : ℕ, c i ≤ A * Z i) →
      (∀ N : ℕ, spend w c N ≤ C) →
      (∀ q : ℝ, 1 < q → ∃ M : ℝ, ∀ i : ℕ, Z i ≤ M * q ^ i) →
      p * infiniteValue A p w ≤ C) := by
  refine ⟨exists_exact_scalar_optimizer hA hp hw, ?_⟩
  intro Z c C hZ hc hZ0 hZ1 hrec hcap hbudget henv
  have hh := actual_infinite_value_payment Z c w hA.le (floors_nonempty hw)
    hZ hc hZ0 (hZ1.symm ▸ hp) hrec hcap hbudget henv
  simpa only [hZ1] using hh

end KLSConstantImprovement.ActualProperInfiniteValuePayment

#print axioms KLSConstantImprovement.ActualProperInfiniteValuePayment.actual_infinite_value_payment
#print axioms KLSConstantImprovement.ActualProperInfiniteValuePayment.exists_exact_scalar_optimizer
#print axioms KLSConstantImprovement.ActualProperInfiniteValuePayment.attained_least_normalized_scalar_budget
