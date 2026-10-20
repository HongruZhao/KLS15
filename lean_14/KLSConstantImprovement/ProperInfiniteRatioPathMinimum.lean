import KLSConstantImprovement.ProperInfiniteRatioPathSelection
import KLSConstantImprovement.RatioPathOrbitRealization

/-! Exact scalar minimum selected by positive geometric terminals.

The endpoint is an attained minimum among compatible nonincreasing ratio
paths with all-rate product growth.  Its normalization is per `Z₁ = p`;
the actual normalized-orbit budget is `p` times this value.  No admissible
law attaining this scalar minimum is claimed, and no optimization over
generator/weight profiles is asserted.

This isolated source draft has not been compiled by its author. -/

noncomputable section
namespace KLSConstantImprovement.ProperInfiniteRatioPathMinimum

open KLSConstantImprovement.CompatibleRatioPathCompact
open KLSConstantImprovement.GeometricTerminalGrowthExclusion
open KLSConstantImprovement.SubexponentialTerminalSupremum
open KLSConstantImprovement.ProperInfiniteRatioPathSelection

def Proper (r : ℕ → ℝ) : Prop :=
  ∀ q : ℝ, 1 < q → ∃ M : ℝ, ∀ n : ℕ, P r n ≤ M * q ^ n

/-- This `sSup` is used only after its finite-prefix range is bounded. -/
def pathCost (w r : ℕ → ℝ) : ℝ :=
  sSup (Set.range (fun N : ℕ => prefixSpend w r N))

theorem potential_le_of_proper_budget {A p J : ℝ} {r w : ℕ → ℝ}
    (hr : r ∈ ratioPathSet A p) (hF : Nonempty (Floor w)) (henv : Proper r)
    (hbudget : ∀ N : ℕ, prefixSpend w r N ≤ J) (N : ℕ) :
    prefixPotential w r N ≤ J := by
  exact RatioPathOrbitRealization.literal_terminal_bound r w hr hF henv hbudget N

theorem infiniteValue_le_of_proper_budget {A p J : ℝ} {r w : ℕ → ℝ}
    (hr : r ∈ ratioPathSet A p) (hF : Nonempty (Floor w)) (henv : Proper r)
    (hbudget : ∀ N : ℕ, prefixSpend w r N ≤ J) :
    infiniteValue A p w ≤ J := by
  apply csSup_le (show (Set.range (fun N : ℕ => finiteValue A p w N)).Nonempty from
    ⟨finiteValue A p w 0, ⟨0, rfl⟩⟩)
  rintro y ⟨N, rfl⟩
  exact (finiteValue_le hF hr N).trans
    (potential_le_of_proper_budget hr hF henv hbudget N)

/-- The positive-terminal infinite-horizon formula is an attained scalar
minimum.  The comparison uses bounded prefix costs, so paths of infinite
cost are never assigned a spurious finite real supremum. -/
theorem attained_scalar_minimum {A p : ℝ} {w : ℕ → ℝ}
    (hA : 0 < A) (hp : 1 ≤ p) (hw : FullFloors w) :
    ∃ r : ℕ → ℝ, r ∈ ratioPathSet A p ∧ Proper r ∧
      (∀ N : ℕ, prefixSpend w r N ≤ infiniteValue A p w) ∧
      pathCost w r = infiniteValue A p w ∧
      (∀ s : ℕ → ℝ, s ∈ ratioPathSet A p → Proper s →
        ∀ J : ℝ, (∀ N : ℕ, prefixSpend w s N ≤ J) → infiniteValue A p w ≤ J) := by
  obtain ⟨r, hr, hpot, hcost, hratio, henv⟩ :=
    exists_proper_selected_path hA hp hw
  have hproper : Proper r := by
    intro q hq
    obtain ⟨M, hM, hbound⟩ := henv q hq
    exact ⟨M, hbound⟩
  have hbounded : BddAbove (Set.range (fun N : ℕ => prefixSpend w r N)) := by
    refine ⟨infiniteValue A p w, ?_⟩
    rintro y ⟨N, rfl⟩
    exact hcost N
  have hprefix_le (N : ℕ) : prefixSpend w r N ≤ pathCost w r :=
    le_csSup hbounded ⟨N, rfl⟩
  have hupper : pathCost w r ≤ infiniteValue A p w := by
    apply csSup_le (show (Set.range (fun N : ℕ => prefixSpend w r N)).Nonempty from
      ⟨prefixSpend w r 0, ⟨0, rfl⟩⟩)
    rintro y ⟨N, rfl⟩
    exact hcost N
  have hlower : infiniteValue A p w ≤ pathCost w r :=
    infiniteValue_le_of_proper_budget hr (floors_nonempty hw) hproper hprefix_le
  refine ⟨r, hr, hproper, hcost, le_antisymm hupper hlower, ?_⟩
  intro s hs hsproper J hsbudget
  exact infiniteValue_le_of_proper_budget hs (floors_nonempty hw) hsproper hsbudget

end KLSConstantImprovement.ProperInfiniteRatioPathMinimum

#print axioms KLSConstantImprovement.ProperInfiniteRatioPathMinimum.potential_le_of_proper_budget
#print axioms KLSConstantImprovement.ProperInfiniteRatioPathMinimum.infiniteValue_le_of_proper_budget
#print axioms KLSConstantImprovement.ProperInfiniteRatioPathMinimum.attained_scalar_minimum
