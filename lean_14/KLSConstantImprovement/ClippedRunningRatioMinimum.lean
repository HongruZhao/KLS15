import KLSConstantImprovement.ProperInfiniteRatioPathMinimum

/-! A clipped running minimum turns arbitrary nonnegative normalized
orbits into compatible decreasing paths, at no greater weighted cost.
The minimum stops permanently at one when an original ratio is below one
or a denominator is zero.  No monotonicity of the original ratios is
assumed.  This isolated source draft has not been compiled by its author. -/

noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.ClippedRunningRatioMinimum

open KLSConstantImprovement.CompatibleRatioPathCompact
open KLSConstantImprovement.GeometricTerminalGrowthExclusion
open KLSConstantImprovement.ProperInfiniteRatioPathSelection
open KLSConstantImprovement.ProperInfiniteRatioPathMinimum
open KLSConstantImprovement.WeightedOrbitBellmanTail

def ratio (Z : ℕ → ℝ) (n : ℕ) : ℝ := Z (n + 1) / Z n

def running (Z : ℕ → ℝ) : ℕ → ℝ
  | 0 => Z 1
  | n + 1 => min (running Z n) (max 1 (ratio Z (n + 1)))

@[simp] theorem running_zero (Z : ℕ → ℝ) : running Z 0 = Z 1 := rfl

theorem running_succ (Z : ℕ → ℝ) (n : ℕ) :
    running Z (n + 1) = min (running Z n) (max 1 (ratio Z (n + 1))) := rfl

theorem running_lower (Z : ℕ → ℝ) (hp : 1 ≤ Z 1) (n : ℕ) :
    1 ≤ running Z n := by
  induction n with
  | zero => exact hp
  | succ n ih => exact le_min ih (le_max_left _ _)

theorem running_successor_le (Z : ℕ → ℝ) (n : ℕ) :
    running Z (n + 1) ≤ running Z n := min_le_left _ _

theorem running_antitone (Z : ℕ → ℝ) : Antitone (running Z) :=
  antitone_nat_of_succ_le (running_successor_le Z)

theorem running_eq_one_after {Z : ℕ → ℝ} (hp : 1 ≤ Z 1) {M : ℕ}
    (hhit : running Z M = 1) {n : ℕ} (hn : M ≤ n) : running Z n = 1 := by
  exact le_antisymm ((running_antitone Z hn).trans_eq hhit) (running_lower Z hp n)

theorem active_le_ratio {Z : ℕ → ℝ} (hZ0 : Z 0 = 1) {n : ℕ}
    (hactive : 1 < running Z n) : running Z n ≤ ratio Z n := by
  cases n with
  | zero =>
    simpa only [running_zero, ratio, hZ0, div_one, Nat.zero_add] using
      (le_rfl : Z 1 ≤ Z 1)
  | succ n =>
    have hm : running Z (n + 1) ≤ max 1 (ratio Z (n + 1)) := min_le_right _ _
    have hratio : 1 < ratio Z (n + 1) := by
      by_contra hn
      rw [max_eq_left (le_of_not_gt hn)] at hm
      linarith
    rwa [max_eq_right hratio.le] at hm

theorem active_positive {Z : ℕ → ℝ} (hZ : ∀ n : ℕ, 0 ≤ Z n) (hZ0 : Z 0 = 1)
    {n : ℕ} (hactive : 1 < running Z n) : 0 < Z n ∧ 0 < Z (n + 1) := by
  have hr : 0 < ratio Z n := by linarith [active_le_ratio hZ0 hactive]
  have hne : Z n ≠ 0 := by
    intro hz
    simp only [ratio, hz, div_zero] at hr
    linarith
  have hz : 0 < Z n := lt_of_le_of_ne (hZ n) (Ne.symm hne)
  exact ⟨hz, (div_pos_iff_of_pos_right hz).mp hr⟩

/-- Product comparison is required only while the running minimum is active.
After a hit at one it is constant and no later costs occur. -/
theorem active_product_comparison {Z : ℕ → ℝ}
    (hZ : ∀ n : ℕ, 0 ≤ Z n) (hZ0 : Z 0 = 1) (hp : 1 ≤ Z 1) (n : ℕ)
    (hactive : 1 < running Z n) :
    Z 1 * P (running Z) n ≤ Z (n + 1) := by
  induction n with
  | zero =>
    simpa only [P_zero, mul_one, Nat.zero_add] using (le_rfl : Z 1 ≤ Z 1)
  | succ n ih =>
    have ha : 1 < running Z n := hactive.trans_le (running_successor_le Z n)
    have hcomp := ih ha
    have hz := (active_positive hZ hZ0 ha).2
    have hratio := active_le_ratio hZ0 hactive
    calc
      Z 1 * P (running Z) (n + 1) =
          (Z 1 * P (running Z) n) * running Z (n + 1) := by rw [P_succ]; ring
      _ ≤ Z (n + 1) * ratio Z (n + 1) :=
        mul_le_mul hcomp hratio (by linarith [running_lower Z hp (n + 1)]) (hZ _)
      _ = Z (n + 2) := by
        dsimp only [ratio]
        rw [show n + 1 + 1 = n + 2 by omega]
        field_simp [ne_of_gt hz]

theorem active_drop_bound {Z c : ℕ → ℝ}
    (hZ : ∀ n : ℕ, 0 ≤ Z n) (hc : ∀ n : ℕ, 0 ≤ c n) (hZ0 : Z 0 = 1)
    (hrec : ∀ i : ℕ, 0 < Z i → 0 < Z (i + 1) →
      Z (i + 1) ^ 2 / Z i - c i ≤ Z (i + 2))
    {n : ℕ} (hactive : 1 < running Z n) :
    running Z n - running Z (n + 1) ≤ c n / Z (n + 1) := by
  obtain ⟨hzn, hzn1⟩ := active_positive hZ hZ0 hactive
  have hd : 0 ≤ c n / Z (n + 1) := div_nonneg (hc n) hzn1.le
  have hratio := active_le_ratio hZ0 hactive
  have hrrec : ratio Z n - ratio Z (n + 1) ≤ c n / Z (n + 1) := by
    have hh := div_le_div_of_nonneg_right (hrec n hzn hzn1) hzn1.le
    have he : (Z (n + 1) ^ 2 / Z n - c n) / Z (n + 1) =
        ratio Z n - c n / Z (n + 1) := by
      dsimp only [ratio]
      field_simp [ne_of_gt hzn, ne_of_gt hzn1] <;> ring
    rw [he] at hh
    change ratio Z n - c n / Z (n + 1) ≤ ratio Z (n + 1) at hh
    linarith
  have hnext : running Z n - c n / Z (n + 1) ≤ running Z (n + 1) := by
    apply le_min
    · linarith
    · have hlow : running Z n - c n / Z (n + 1) ≤ ratio Z (n + 1) := by linarith
      exact hlow.trans (le_max_right _ _)
  linarith

theorem running_cap {Z c : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hZ : ∀ n : ℕ, 0 ≤ Z n) (hc : ∀ n : ℕ, 0 ≤ c n)
    (hZ0 : Z 0 = 1) (hp : 1 ≤ Z 1)
    (hrec : ∀ i : ℕ, 0 < Z i → 0 < Z (i + 1) →
      Z (i + 1) ^ 2 / Z i - c i ≤ Z (i + 2))
    (hcap : ∀ i : ℕ, c i ≤ A * Z i) (n : ℕ) :
    running Z n * (running Z n - running Z (n + 1)) ≤ A := by
  by_cases ha : 1 < running Z n
  · obtain ⟨hzn, hzn1⟩ := active_positive hZ hZ0 ha
    have hdrop := active_drop_bound hZ hc hZ0 hrec ha
    have hdrop0 : 0 ≤ running Z n - running Z (n + 1) :=
      sub_nonneg.mpr (running_successor_le Z n)
    have hrr : 0 ≤ ratio Z n := div_nonneg (hZ _) (hZ _)
    have hm := mul_le_mul (active_le_ratio hZ0 ha) hdrop hdrop0 hrr
    have hid : ratio Z n * (c n / Z (n + 1)) = c n / Z n := by
      dsimp only [ratio]
      field_simp [ne_of_gt hzn, ne_of_gt hzn1] <;> ring
    rw [hid] at hm
    exact hm.trans ((div_le_iff₀ hzn).mpr (by simpa only [mul_comm] using hcap n))
  · have hone : running Z n = 1 :=
      le_antisymm (le_of_not_gt ha) (running_lower Z hp n)
    have hnext := running_eq_one_after hp hone (Nat.le_succ n)
    simpa only [hone, hnext, sub_self, mul_zero] using hA

theorem running_mem {Z c : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hZ : ∀ n : ℕ, 0 ≤ Z n) (hc : ∀ n : ℕ, 0 ≤ c n)
    (hZ0 : Z 0 = 1) (hp : 1 ≤ Z 1)
    (hrec : ∀ i : ℕ, 0 < Z i → 0 < Z (i + 1) →
      Z (i + 1) ^ 2 / Z i - c i ≤ Z (i + 2))
    (hcap : ∀ i : ℕ, c i ≤ A * Z i) :
    running Z ∈ ratioPathSet A (Z 1) := by
  refine ⟨rfl, fun n => ⟨running_lower Z hp n, running_successor_le Z n, ?_⟩⟩
  exact running_cap hA hZ hc hZ0 hp hrec hcap n

/-- Every local running-minimum cost is dominated by the original cost. -/
theorem local_payment {Z c : ℕ → ℝ}
    (hZ : ∀ n : ℕ, 0 ≤ Z n) (hc : ∀ n : ℕ, 0 ≤ c n)
    (hZ0 : Z 0 = 1) (hp : 1 ≤ Z 1)
    (hrec : ∀ i : ℕ, 0 < Z i → 0 < Z (i + 1) →
      Z (i + 1) ^ 2 / Z i - c i ≤ Z (i + 2)) (n : ℕ) :
    Z 1 * P (running Z) n * (running Z n - running Z (n + 1)) ≤ c n := by
  by_cases ha : 1 < running Z n
  · have hz := (active_positive hZ hZ0 ha).2
    have hdrop := active_drop_bound hZ hc hZ0 hrec ha
    have hdrop0 : 0 ≤ running Z n - running Z (n + 1) :=
      sub_nonneg.mpr (running_successor_le Z n)
    have hh := mul_le_mul (active_product_comparison hZ hZ0 hp n ha) hdrop
      hdrop0 (hZ (n + 1))
    have he : Z (n + 1) * (c n / Z (n + 1)) = c n := by
      field_simp [ne_of_gt hz]
    exact hh.trans_eq he
  · have hone : running Z n = 1 :=
      le_antisymm (le_of_not_gt ha) (running_lower Z hp n)
    have hnext := running_eq_one_after hp hone (Nat.le_succ n)
    simpa only [hone, hnext, sub_self, mul_zero] using hc n

theorem prefix_payment {Z c w : ℕ → ℝ}
    (hZ : ∀ n : ℕ, 0 ≤ Z n) (hc : ∀ n : ℕ, 0 ≤ c n)
    (hw : ∀ n : ℕ, 0 ≤ w n) (hZ0 : Z 0 = 1) (hp : 1 ≤ Z 1)
    (hrec : ∀ i : ℕ, 0 < Z i → 0 < Z (i + 1) →
      Z (i + 1) ^ 2 / Z i - c i ≤ Z (i + 2)) (N : ℕ) :
    Z 1 * prefixSpend w (running Z) N ≤ spend w c N := by
  unfold prefixSpend spend
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hh := mul_le_mul_of_nonneg_left (local_payment hZ hc hZ0 hp hrec i) (hw i)
  nlinarith only [hh]

theorem running_proper {Z c : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hZ : ∀ n : ℕ, 0 ≤ Z n) (hc : ∀ n : ℕ, 0 ≤ c n)
    (hZ0 : Z 0 = 1) (hp : 1 ≤ Z 1)
    (hrec : ∀ i : ℕ, 0 < Z i → 0 < Z (i + 1) →
      Z (i + 1) ^ 2 / Z i - c i ≤ Z (i + 2))
    (hcap : ∀ i : ℕ, c i ≤ A * Z i)
    (henv : ∀ q : ℝ, 1 < q → ∃ M : ℝ, ∀ i : ℕ, Z i ≤ M * q ^ i) :
    Proper (running Z) := by
  have hr := running_mem hA hZ hc hZ0 hp hrec hcap
  by_cases hhit : ∃ M : ℕ, running Z M = 1
  · obtain ⟨M, hM⟩ := hhit
    exact RatioPathOrbitRealization.product_envelope_of_eventually_one hr
      ⟨M, fun n hn => running_eq_one_after hp hM hn⟩
  · intro q hq
    obtain ⟨M, hM⟩ := henv q hq
    have hp0 : 0 < Z 1 := by linarith
    refine ⟨M * q / Z 1, ?_⟩
    intro n
    have ha : 1 < running Z n := by
      have hne : running Z n ≠ 1 := fun hn => hhit ⟨n, hn⟩
      exact lt_of_le_of_ne (running_lower Z hp n) (Ne.symm hne)
    have hh := (active_product_comparison hZ hZ0 hp n ha).trans (hM (n + 1))
    apply le_of_mul_le_mul_right (a := Z 1) ?_ hp0
    have he : (M * q / Z 1 * q ^ n) * Z 1 = M * q ^ (n + 1) := by
      rw [pow_succ]
      field_simp [ne_of_gt hp0] <;> ring
    rw [he]
    simpa only [mul_comm] using hh

end KLSConstantImprovement.ClippedRunningRatioMinimum

#print axioms KLSConstantImprovement.ClippedRunningRatioMinimum.running_mem
#print axioms KLSConstantImprovement.ClippedRunningRatioMinimum.prefix_payment
#print axioms KLSConstantImprovement.ClippedRunningRatioMinimum.running_proper
