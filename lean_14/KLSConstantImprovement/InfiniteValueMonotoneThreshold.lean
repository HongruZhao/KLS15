import KLSConstantImprovement.NormalizedScalarInitialContraction

/-! Monotonicity and actual endpoint tests for the selected infinite value.
The underlying exact scalar minimum is not the outer generator optimum.
This isolated source draft has not been compiled by its author. -/

noncomputable section
namespace KLSConstantImprovement.InfiniteValueMonotoneThreshold
open KLSConstantImprovement.ProperInfiniteRatioPathSelection
open KLSConstantImprovement.ProperInfiniteRatioPathMinimum
open KLSConstantImprovement.SubexponentialTerminalSupremum
open KLSConstantImprovement.ActualProperInfiniteValuePayment
open KLSConstantImprovement.NormalizedScalarInitialContraction
open KLSConstantImprovement.WeightedOrbitBellmanTail

/-- Every actual orbit starting at `Z₁ ≥ p` pays the fixed-state value
with its own initial multiplier: `Z₁ * V(p) ≤ C`. -/
theorem actual_payment_at_lower_initial {A C p : ℝ} (Z c w : ℕ → ℝ)
    (hA : 0 ≤ A) (hF : Nonempty (Floor w)) (hp : 1 ≤ p) (hpZ : p ≤ Z 1)
    (hZ : ∀ n : ℕ, 0 ≤ Z n) (hc : ∀ n : ℕ, 0 ≤ c n) (hZ0 : Z 0 = 1)
    (hrec : ∀ i : ℕ, 0 < Z i → 0 < Z (i + 1) →
      Z (i + 1) ^ 2 / Z i - c i ≤ Z (i + 2))
    (hcap : ∀ i : ℕ, c i ≤ A * Z i)
    (hbudget : ∀ N : ℕ, spend w c N ≤ C)
    (henv : ∀ q : ℝ, 1 < q → ∃ M : ℝ, ∀ i : ℕ, Z i ≤ M * q ^ i) :
    Z 1 * infiniteValue A p w ≤ C := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < Z 1 := hp0.trans_le hpZ
  let k : ℝ := p / Z 1
  have hk : 0 < k := div_pos hp0 hq0
  have hk1 : k ≤ 1 := (div_le_one hq0).mpr hpZ
  have hinit : contractedZ k Z 1 = p := by
    change (p / Z 1) * Z 1 = p
    field_simp [ne_of_gt hq0]
  have hnewbudget (N : ℕ) : spend w (contractedC k c) N ≤ k * C := by
    rw [contracted_spend]
    exact mul_le_mul_of_nonneg_left (hbudget N) hk.le
  have hh := actual_infinite_value_payment (contractedZ k Z) (contractedC k c) w hA hF
    (contractedZ_nonneg hk.le hZ) (contractedC_nonneg hk.le hc) rfl
    (by simpa only [hinit] using hp)
    (contracted_recurrence hk hk1 hZ0 hrec)
    (contracted_cap hk.le hk1 hA hZ0 hcap) hnewbudget
    (contracted_envelope hk.le hk1 hZ hZ0 henv)
  rw [hinit] at hh
  have hm := mul_le_mul_of_nonneg_right hh hq0.le
  have he : (k * C) * Z 1 = p * C := by
    dsimp only [k]
    field_simp [ne_of_gt hq0] <;> ring
  rw [he] at hm
  apply le_of_mul_le_mul_left (a := p) ?_ hp0
  nlinarith only [hm]

theorem infiniteValue_monotone {A p q : ℝ} {w : ℕ → ℝ}
    (hA : 0 < A) (hp : 1 ≤ p) (hpq : p ≤ q) (hw : FullFloors w) :
    infiniteValue A p w ≤ infiniteValue A q w := by
  have hq : 1 ≤ q := hp.trans hpq
  obtain ⟨Z, c, hZ0, hZ1, hZ, hc, hrec, hcap, hbudget, henv⟩ :=
    exists_exact_scalar_optimizer hA hq hw
  have hh := actual_payment_at_lower_initial Z c w hA.le (floors_nonempty hw) hp
    (by simpa only [hZ1] using hpq) (fun i => (hZ i).le) hc hZ0
    (fun i _ _ => (hrec i).le) hcap hbudget henv
  rw [hZ1] at hh
  exact le_of_mul_le_mul_left hh (by linarith : 0 < q)

/-- A strict budget violation at a nominated state excludes every larger
actual initial state, using the correct leading initial factor. -/
theorem actual_initial_lt_of_strict_budget {A C p : ℝ} (Z c w : ℕ → ℝ)
    (hA : 0 ≤ A) (hF : Nonempty (Floor w)) (hp : 1 ≤ p)
    (hZ : ∀ n : ℕ, 0 ≤ Z n) (hc : ∀ n : ℕ, 0 ≤ c n) (hZ0 : Z 0 = 1)
    (hrec : ∀ i : ℕ, 0 < Z i → 0 < Z (i + 1) →
      Z (i + 1) ^ 2 / Z i - c i ≤ Z (i + 2))
    (hcap : ∀ i : ℕ, c i ≤ A * Z i)
    (hbudget : ∀ N : ℕ, spend w c N ≤ C)
    (henv : ∀ q : ℝ, 1 < q → ∃ M : ℝ, ∀ i : ℕ, Z i ≤ M * q ^ i)
    (hstrict : C < p * infiniteValue A p w) : Z 1 < p := by
  by_contra hn
  have hpZ : p ≤ Z 1 := le_of_not_gt hn
  have hpaid := actual_payment_at_lower_initial Z c w hA hF hp hpZ
    hZ hc hZ0 hrec hcap hbudget henv
  have hC : 0 ≤ C := by simpa only [spend, Finset.range_zero, Finset.sum_empty] using hbudget 0
  have hV : 0 ≤ infiniteValue A p w := by
    by_contra hneg
    have hh := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ p) (le_of_not_ge hneg)
    linarith
  have hh := mul_le_mul_of_nonneg_right hpZ hV
  linarith

end KLSConstantImprovement.InfiniteValueMonotoneThreshold

#print axioms KLSConstantImprovement.InfiniteValueMonotoneThreshold.actual_payment_at_lower_initial
#print axioms KLSConstantImprovement.InfiniteValueMonotoneThreshold.infiniteValue_monotone
#print axioms KLSConstantImprovement.InfiniteValueMonotoneThreshold.actual_initial_lt_of_strict_budget
