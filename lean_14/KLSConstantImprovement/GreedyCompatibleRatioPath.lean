import KLSConstantImprovement.CompatibleRatioPathCompact
import KLSConstantImprovement.NonlinearBellmanTailPayment

/-!
# An eventually constant compatible greedy path

The exact scalar transition supplies a compatible path, and positive cap
forces a finite hit at ratio one.  This isolated draft has not been compiled
by its author.
-/

noncomputable section

namespace KLSConstantImprovement.GreedyCompatibleRatioPath

open KLSConstantImprovement.ProperConstantTailRecursion
open KLSConstantImprovement.ConstantTailFiniteHitting
open KLSConstantImprovement.NonlinearBellmanTailPayment
open KLSConstantImprovement.CompatibleRatioPathCompact

/-- The exact-cap greedy ratio path starting from `p`. -/
def greedy (A p : ℝ) (n : ℕ) : ℝ :=
  1 + path (exactStep A) n (p - 1)

theorem greedy_zero (A p : ℝ) : greedy A p 0 = p := by
  simp only [greedy, path]
  ring

theorem greedy_succ (A p : ℝ) (n : ℕ) :
    greedy A p (n + 1) = 1 + exactStep A (greedy A p n - 1) := by
  simp only [greedy, path_succ]
  congr 2
  ring

theorem greedy_lower {A p : ℝ} (hp : 1 ≤ p) (n : ℕ) :
    1 ≤ greedy A p n := by
  have hh := path_nonneg (exactStep A) (exactStep_nonneg A)
    (show 0 ≤ p - 1 by linarith) n
  dsimp only [greedy]
  linarith

theorem exactStep_le_self {A x : ℝ} (hA : 0 ≤ A) (hx : 0 ≤ x) :
    exactStep A x ≤ x := by
  unfold exactStep
  rw [max_eq_right hx]
  exact max_le hx (sub_le_self _ (div_nonneg hA (by linarith)))

/-- The exact transition saturates the quadratic cap unless it lands at one. -/
theorem exactStep_cap {A x : ℝ} (hx : 0 ≤ x) :
    (1 + x) * (x - exactStep A x) ≤ A := by
  have hden : 0 < 1 + x := by linarith
  have hnext : x - A / (1 + x) ≤ exactStep A x := by
    unfold exactStep
    rw [max_eq_right hx]
    exact le_max_right _ _
  have hdrop : x - exactStep A x ≤ A / (1 + x) := by linarith
  exact (le_div_iff₀' hden).mp hdrop

theorem greedy_successor_le {A p : ℝ} (hA : 0 ≤ A) (hp : 1 ≤ p)
    (n : ℕ) : greedy A p (n + 1) ≤ greedy A p n := by
  have hh := exactStep_le_self hA
    (show 0 ≤ greedy A p n - 1 by linarith [greedy_lower (A := A) hp n])
  rw [greedy_succ]
  linarith

theorem greedy_cap {A p : ℝ} (hp : 1 ≤ p) (n : ℕ) :
    greedy A p n * (greedy A p n - greedy A p (n + 1)) ≤ A := by
  rw [greedy_succ]
  have hh := exactStep_cap
    (A := A) (show 0 ≤ greedy A p n - 1 by linarith [greedy_lower (A := A) hp n])
  convert hh using 1 <;> ring

theorem greedy_mem {A p : ℝ} (hA : 0 ≤ A) (hp : 1 ≤ p) :
    greedy A p ∈ ratioPathSet A p := by
  refine ⟨greedy_zero A p, fun n => ?_⟩
  exact ⟨greedy_lower (A := A) hp n, greedy_successor_le hA hp n, greedy_cap hp n⟩

theorem greedy_antitone {A p : ℝ} (hA : 0 ≤ A) (hp : 1 ≤ p) :
    Antitone (greedy A p) :=
  CompatibleRatioPathCompact.antitone (greedy_mem hA hp)

theorem greedy_bounds {A p : ℝ} (hA : 0 ≤ A) (hp : 1 ≤ p) (n : ℕ) :
    greedy A p n ∈ Set.Icc (1 : ℝ) p :=
  CompatibleRatioPathCompact.bounds (greedy_mem hA hp) n

theorem greedy_has_hit {A p : ℝ} (hA : 0 < A) :
    ∃ M : ℕ, greedy A p M = 1 := by
  obtain ⟨M, hM⟩ := exactStep_has_hit hA (p - 1)
  refine ⟨M, ?_⟩
  simp only [greedy, hM, add_zero]

theorem greedy_eq_one_of_hit {A p : ℝ} (hA : 0 ≤ A) {M : ℕ}
    (hhit : greedy A p M = 1) {n : ℕ} (hn : M ≤ n) :
    greedy A p n = 1 := by
  induction n, hn using Nat.le_induction with
  | base => exact hhit
  | succ n hn ih =>
      rw [greedy_succ, ih, sub_self, exactStep_zero hA, add_zero]

theorem greedy_eventually_one {A p : ℝ} (hA : 0 < A) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → greedy A p n = 1 := by
  obtain ⟨M, hM⟩ := greedy_has_hit (p := p) hA
  exact ⟨M, fun n hn => greedy_eq_one_of_hit hA.le hM hn⟩

/-- A concrete compatible path with a finite constant tail, for bounding minima. -/
theorem exists_compatible_eventually_one {A p : ℝ} (hA : 0 < A) (hp : 1 ≤ p) :
    ∃ r : ℕ → ℝ, r ∈ ratioPathSet A p ∧
      ∃ M : ℕ, ∀ n : ℕ, M ≤ n → r n = 1 :=
  ⟨greedy A p, greedy_mem hA.le hp, greedy_eventually_one hA⟩

end KLSConstantImprovement.GreedyCompatibleRatioPath

#print axioms KLSConstantImprovement.GreedyCompatibleRatioPath.greedy_mem
#print axioms KLSConstantImprovement.GreedyCompatibleRatioPath.greedy_eventually_one
