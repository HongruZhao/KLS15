import Mathlib

/-!
# Compact compatible ratio paths

The topology is the product topology on `ℕ → ℝ`.  The cap is written as a
polynomial inequality, so closedness does not require dividing by a coordinate.

This is an isolated source draft.  It has not been compiled by its author.
-/

namespace KLSConstantImprovement.CompatibleRatioPathCompact

/-- Nonincreasing ratio paths with fixed initial ratio and the exact scalar cap. -/
def ratioPathSet (A p : ℝ) : Set (ℕ → ℝ) :=
  {r | r 0 = p ∧ ∀ n : ℕ,
    1 ≤ r n ∧ r (n + 1) ≤ r n ∧ r n * (r n - r (n + 1)) ≤ A}

theorem mem_iff (A p : ℝ) (r : ℕ → ℝ) :
    r ∈ ratioPathSet A p ↔
      r 0 = p ∧ ∀ n : ℕ,
        1 ≤ r n ∧ r (n + 1) ≤ r n ∧ r n * (r n - r (n + 1)) ≤ A :=
  Iff.rfl

theorem initial {A p : ℝ} {r : ℕ → ℝ} (hr : r ∈ ratioPathSet A p) :
    r 0 = p :=
  hr.1

theorem lower {A p : ℝ} {r : ℕ → ℝ} (hr : r ∈ ratioPathSet A p) (n : ℕ) :
    1 ≤ r n :=
  (hr.2 n).1

theorem successor_le {A p : ℝ} {r : ℕ → ℝ} (hr : r ∈ ratioPathSet A p)
    (n : ℕ) : r (n + 1) ≤ r n :=
  (hr.2 n).2.1

theorem cap {A p : ℝ} {r : ℕ → ℝ} (hr : r ∈ ratioPathSet A p) (n : ℕ) :
    r n * (r n - r (n + 1)) ≤ A :=
  (hr.2 n).2.2

theorem antitone {A p : ℝ} {r : ℕ → ℝ} (hr : r ∈ ratioPathSet A p) :
    Antitone r :=
  antitone_nat_of_succ_le (successor_le hr)

theorem upper {A p : ℝ} {r : ℕ → ℝ} (hr : r ∈ ratioPathSet A p) (n : ℕ) :
    r n ≤ p := by
  calc
    r n ≤ r 0 := antitone hr (Nat.zero_le n)
    _ = p := initial hr

theorem bounds {A p : ℝ} {r : ℕ → ℝ} (hr : r ∈ ratioPathSet A p) (n : ℕ) :
    r n ∈ Set.Icc (1 : ℝ) p :=
  ⟨lower hr n, upper hr n⟩

theorem isClosed_ratioPathSet (A p : ℝ) : IsClosed (ratioPathSet A p) := by
  have hinit : IsClosed {r : ℕ → ℝ | r 0 = p} :=
    isClosed_eq (continuous_apply 0) continuous_const
  have hstep (n : ℕ) : IsClosed {r : ℕ → ℝ |
      1 ≤ r n ∧ r (n + 1) ≤ r n ∧ r n * (r n - r (n + 1)) ≤ A} := by
    exact (isClosed_le continuous_const (continuous_apply n)).inter
      ((isClosed_le (continuous_apply (n + 1)) (continuous_apply n)).inter
        (isClosed_le
          ((continuous_apply n).mul
            ((continuous_apply n).sub (continuous_apply (n + 1))))
          continuous_const))
  have hall : IsClosed {r : ℕ → ℝ | ∀ n : ℕ,
      1 ≤ r n ∧ r (n + 1) ≤ r n ∧ r n * (r n - r (n + 1)) ≤ A} := by
    have heq : {r : ℕ → ℝ | ∀ n : ℕ,
        1 ≤ r n ∧ r (n + 1) ≤ r n ∧ r n * (r n - r (n + 1)) ≤ A} =
        ⋂ n : ℕ, {r : ℕ → ℝ |
          1 ≤ r n ∧ r (n + 1) ≤ r n ∧ r n * (r n - r (n + 1)) ≤ A} := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [heq]
    exact isClosed_iInter hstep
  exact hinit.inter hall

/-- Every compatible path lies in the same coordinatewise compact box. -/
theorem subset_box (A p : ℝ) :
    ratioPathSet A p ⊆ {r : ℕ → ℝ | ∀ n : ℕ, r n ∈ Set.Icc (1 : ℝ) p} := by
  intro r hr n
  exact bounds hr n

/-- Compactness actually holds even when `p < 1`, since then the path set is empty. -/
theorem isCompact_ratioPathSet_unrestricted (A p : ℝ) :
    IsCompact (ratioPathSet A p) := by
  have hbox : IsCompact {r : ℕ → ℝ | ∀ n : ℕ, r n ∈ Set.Icc (1 : ℝ) p} :=
    isCompact_pi_infinite (fun _ : ℕ => isCompact_Icc)
  exact hbox.of_isClosed_subset (isClosed_ratioPathSet A p) (subset_box A p)

theorem isCompact_ratioPathSet (A p : ℝ) (_hp : 1 ≤ p) :
    IsCompact (ratioPathSet A p) :=
  isCompact_ratioPathSet_unrestricted A p

theorem constant_mem (A p : ℝ) (hA : 0 ≤ A) (hp : 1 ≤ p) :
    (fun _ : ℕ => p) ∈ ratioPathSet A p := by
  refine ⟨rfl, fun _ => ⟨hp, le_rfl, ?_⟩⟩
  simpa only [sub_self, mul_zero] using hA

theorem nonempty_ratioPathSet (A p : ℝ) (hA : 0 ≤ A) (hp : 1 ≤ p) :
    (ratioPathSet A p).Nonempty :=
  ⟨fun _ : ℕ => p, constant_mem A p hA hp⟩

end KLSConstantImprovement.CompatibleRatioPathCompact

#print axioms KLSConstantImprovement.CompatibleRatioPathCompact.isCompact_ratioPathSet
#print axioms KLSConstantImprovement.CompatibleRatioPathCompact.nonempty_ratioPathSet
