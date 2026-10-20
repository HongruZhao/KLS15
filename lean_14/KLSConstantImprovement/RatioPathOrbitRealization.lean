import KLSConstantImprovement.CompatibleRatioPathCompact
import KLSConstantImprovement.GeometricTerminalGrowthExclusion
import KLSConstantImprovement.SubexponentialTerminalSupremum

/-!
# Exact scalar orbit realization of a compatible ratio path

The normalization is `Z 0 = 1`, `Z 1 = p`.  Consequently actual weighted
spend is `p` times the literal normalized prefix sum.  All recurrence and
cap statements below are exact.  This source draft has not been compiled
by its author.
-/

noncomputable section
open scoped BigOperators

namespace KLSConstantImprovement.RatioPathOrbitRealization

open KLSConstantImprovement.CompatibleRatioPathCompact
open KLSConstantImprovement.GeometricTerminalGrowthExclusion
open KLSConstantImprovement.WeightedOrbitBellmanTail
open KLSConstantImprovement.SubexponentialTerminalSupremum

def orbitZ (r : ℕ → ℝ) (p : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => p * P r n

def orbitC (r : ℕ → ℝ) (p : ℝ) (n : ℕ) : ℝ :=
  orbitZ r p (n + 1) * (r n - r (n + 1))

@[simp] theorem orbitZ_zero (r : ℕ → ℝ) (p : ℝ) : orbitZ r p 0 = 1 := rfl

@[simp] theorem orbitZ_one (r : ℕ → ℝ) (p : ℝ) : orbitZ r p 1 = p := by
  simp only [orbitZ, P_zero, mul_one]

theorem p_ge_one {A p : ℝ} {r : ℕ → ℝ} (hr : r ∈ ratioPathSet A p) :
    1 ≤ p := by
  calc
    1 ≤ r 0 := lower hr 0
    _ = p := initial hr

theorem p_pos {A p : ℝ} {r : ℕ → ℝ} (hr : r ∈ ratioPathSet A p) :
    0 < p := lt_of_lt_of_le zero_lt_one (p_ge_one hr)

theorem orbitZ_pos {A p : ℝ} {r : ℕ → ℝ} (hr : r ∈ ratioPathSet A p)
    (n : ℕ) : 0 < orbitZ r p n := by
  cases n with
  | zero => exact zero_lt_one
  | succ n =>
      exact mul_pos (p_pos hr)
        (lt_of_lt_of_le zero_lt_one (P_one_le r (lower hr) n))

theorem orbitZ_succ_mul {A p : ℝ} {r : ℕ → ℝ} (hr : r ∈ ratioPathSet A p)
    (n : ℕ) : orbitZ r p (n + 1) = orbitZ r p n * r n := by
  cases n with
  | zero => simp only [orbitZ, P_zero, mul_one, one_mul, initial hr]
  | succ n =>
      simp only [orbitZ, P_succ]
      ring

theorem orbitC_nonneg {A p : ℝ} {r : ℕ → ℝ} (hr : r ∈ ratioPathSet A p)
    (n : ℕ) : 0 ≤ orbitC r p n :=
  mul_nonneg (orbitZ_pos hr (n + 1)).le (sub_nonneg.mpr (successor_le hr n))

theorem orbit_ratio {A p : ℝ} {r : ℕ → ℝ} (hr : r ∈ ratioPathSet A p)
    (n : ℕ) : orbitZ r p (n + 1) / orbitZ r p n = r n := by
  apply (div_eq_iff (ne_of_gt (orbitZ_pos hr n))).mpr
  rw [orbitZ_succ_mul hr n]
  ring

theorem orbit_recurrence {A p : ℝ} {r : ℕ → ℝ} (hr : r ∈ ratioPathSet A p)
    (n : ℕ) : orbitZ r p (n + 1) ^ 2 / orbitZ r p n - orbitC r p n =
      orbitZ r p (n + 2) := by
  have hfirst : orbitZ r p (n + 1) ^ 2 / orbitZ r p n =
      orbitZ r p (n + 1) * r n := by
    calc
      _ = orbitZ r p (n + 1) *
          (orbitZ r p (n + 1) / orbitZ r p n) := by ring
      _ = _ := by rw [orbit_ratio hr n]
  rw [hfirst, orbitC, orbitZ_succ_mul hr (n + 1)]
  ring

theorem orbit_cap {A p : ℝ} {r : ℕ → ℝ} (hr : r ∈ ratioPathSet A p)
    (n : ℕ) : orbitC r p n ≤ A * orbitZ r p n := by
  unfold orbitC
  rw [orbitZ_succ_mul hr n]
  calc
    orbitZ r p n * r n * (r n - r (n + 1)) =
        orbitZ r p n * (r n * (r n - r (n + 1))) := by ring
    _ ≤ orbitZ r p n * A :=
      mul_le_mul_of_nonneg_left (cap hr n) (orbitZ_pos hr n).le
    _ = A * orbitZ r p n := mul_comm _ _

/-- The normalization factor is exactly `p`, with no endpoint correction. -/
theorem spend_eq (r w : ℕ → ℝ) (p : ℝ) (N : ℕ) :
    spend w (orbitC r p) N =
      p * (∑ i ∈ Finset.range N, w i * P r i * (r i - r (i + 1))) := by
  unfold spend
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [orbitC, orbitZ]
  ring

/-- The positive product envelope transfers to the normalized orbit. -/
theorem orbitZ_envelope (r : ℕ → ℝ) {p : ℝ} (hp : 1 ≤ p)
    (henv : ∀ q : ℝ, 1 < q → ∃ M : ℝ, ∀ n : ℕ, P r n ≤ M * q ^ n) :
    ∀ q : ℝ, 1 < q → ∃ M : ℝ, ∀ n : ℕ, orbitZ r p n ≤ M * q ^ n := by
  intro q hq
  obtain ⟨M, hM⟩ := henv q hq
  have hM1 : 1 ≤ M := by simpa only [P_zero, pow_zero, mul_one] using hM 0
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hPM1 : 1 ≤ p * M := by
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ p * M := mul_le_mul hp hM1 zero_le_one hp0
  have hPM0 : 0 ≤ p * M := mul_nonneg hp0 hM0
  refine ⟨p * M, ?_⟩
  intro n
  cases n with
  | zero => simpa only [orbitZ, pow_zero, mul_one] using hPM1
  | succ n =>
      have hpow : q ^ n ≤ q ^ (n + 1) := pow_le_pow_right₀ hq.le (Nat.le_succ n)
      calc
        orbitZ r p (n + 1) = p * P r n := rfl
        _ ≤ p * (M * q ^ n) := mul_le_mul_of_nonneg_left (hM n) hp0
        _ = (p * M) * q ^ n := by ring
        _ ≤ (p * M) * q ^ (n + 1) := mul_le_mul_of_nonneg_left hpow hPM0

/-- A finite hit at one makes the whole prefix product bounded. -/
theorem product_bounded_of_eventually_one {A p : ℝ} {r : ℕ → ℝ}
    (hr : r ∈ ratioPathSet A p) {M : ℕ}
    (htail : ∀ n : ℕ, M ≤ n → r n = 1) (n : ℕ) : P r n ≤ P r M := by
  have hlater : ∀ k : ℕ, M ≤ k → P r k = P r M := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih => rw [P_succ, htail (k + 1) (by omega), mul_one, ih]
  by_cases hn : n ≤ M
  · exact P_monotone r (lower hr) hn
  · exact (hlater n (by omega)).le

theorem product_envelope_of_eventually_one {A p : ℝ} {r : ℕ → ℝ}
    (hr : r ∈ ratioPathSet A p)
    (htail : ∃ M : ℕ, ∀ n : ℕ, M ≤ n → r n = 1) :
    ∀ q : ℝ, 1 < q → ∃ H : ℝ, ∀ n : ℕ, P r n ≤ H * q ^ n := by
  obtain ⟨M, hM⟩ := htail
  intro q hq
  refine ⟨P r M, fun n => ?_⟩
  calc
    P r n ≤ P r M := product_bounded_of_eventually_one hr hM n
    _ ≤ P r M * q ^ n :=
      le_mul_of_one_le_right (P_nonnegative r (lower hr) M) (one_le_pow₀ hq.le)

/-- The accepted terminal payment applies to every compatible path with an
all-rate product envelope.  The conclusion is fully normalized by `p`. -/
theorem literal_terminal_bound {A p J : ℝ} (r w : ℕ → ℝ)
    (hr : r ∈ ratioPathSet A p) (hF : Nonempty (Floor w))
    (henv : ∀ q : ℝ, 1 < q → ∃ M : ℝ, ∀ n : ℕ, P r n ≤ M * q ^ n)
    (hbudget : ∀ N : ℕ,
      (∑ i ∈ Finset.range N, w i * P r i * (r i - r (i + 1))) ≤ J)
    (N : ℕ) :
    (∑ i ∈ Finset.range N, w i * P r i * (r i - r (i + 1))) +
      P r N * terminalSup w N (r N) ≤ J := by
  have hz : ∀ i : ℕ, 0 ≤ orbitZ r p i := fun i => (orbitZ_pos hr i).le
  have hc : ∀ i : ℕ, 0 ≤ orbitC r p i := orbitC_nonneg hr
  have hzero : ∀ i : ℕ, orbitZ r p i = 0 → orbitZ r p (i + 1) = 0 := by
    intro i hi
    exact False.elim ((ne_of_gt (orbitZ_pos hr i)) hi)
  have hrec : ∀ i : ℕ, 0 < orbitZ r p i → 0 < orbitZ r p (i + 1) →
      orbitZ r p (i + 1) ^ 2 / orbitZ r p i - orbitC r p i ≤
        orbitZ r p (i + 2) := fun i _ _ => (orbit_recurrence hr i).le
  have hb : ∀ j : ℕ, spend w (orbitC r p) j ≤ p * J := by
    intro j
    rw [spend_eq]
    exact mul_le_mul_of_nonneg_left (hbudget j) (p_pos hr).le
  have hh := terminalSup_payment (orbitZ r p) (orbitC r p) w hF hz hc hzero hrec hb
    (orbitZ_envelope r (p_ge_one hr) henv) N
  rw [orbit_ratio hr N, spend_eq] at hh
  change (p * P r N) * terminalSup w N (r N) ≤
    p * J - p * (∑ i ∈ Finset.range N, w i * P r i * (r i - r (i + 1))) at hh
  apply le_of_mul_le_mul_left (a := p) ?_ (p_pos hr)
  nlinarith only [hh]

/-- Explicit finite compatible paths realize genuine positive normalized scalar
orbits with the exact cap, budget, and all-rate envelope. -/
theorem exists_orbit_of_eventually_one {A p J : ℝ} (r w : ℕ → ℝ)
    (hr : r ∈ ratioPathSet A p)
    (htail : ∃ M : ℕ, ∀ n : ℕ, M ≤ n → r n = 1)
    (hbudget : ∀ N : ℕ,
      (∑ i ∈ Finset.range N, w i * P r i * (r i - r (i + 1))) ≤ J) :
    ∃ Z c : ℕ → ℝ, Z 0 = 1 ∧ Z 1 = p ∧ (∀ i : ℕ, 0 < Z i) ∧
      (∀ i : ℕ, 0 ≤ c i) ∧ (∀ i : ℕ, Z (i + 1) / Z i = r i) ∧
      (∀ i : ℕ, Z (i + 1) ^ 2 / Z i - c i = Z (i + 2)) ∧
      (∀ i : ℕ, c i ≤ A * Z i) ∧ (∀ N : ℕ, spend w c N ≤ p * J) ∧
      (∀ q : ℝ, 1 < q → ∃ H : ℝ, ∀ i : ℕ, Z i ≤ H * q ^ i) := by
  refine ⟨orbitZ r p, orbitC r p, rfl, orbitZ_one r p,
    orbitZ_pos hr, orbitC_nonneg hr, orbit_ratio hr, orbit_recurrence hr,
    orbit_cap hr, ?_, ?_⟩
  · intro N
    rw [spend_eq]
    exact mul_le_mul_of_nonneg_left (hbudget N) (p_pos hr).le
  · exact orbitZ_envelope r (p_ge_one hr) (product_envelope_of_eventually_one hr htail)

end KLSConstantImprovement.RatioPathOrbitRealization

#print axioms KLSConstantImprovement.RatioPathOrbitRealization.orbit_recurrence
#print axioms KLSConstantImprovement.RatioPathOrbitRealization.orbit_cap
#print axioms KLSConstantImprovement.RatioPathOrbitRealization.literal_terminal_bound
