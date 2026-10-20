import KLSConstantImprovement.MonotoneCompactBellmanLimit
import KLSConstantImprovement.SubexponentialTerminalContinuity
import KLSConstantImprovement.GeometricTerminalGrowthExclusion
import KLSConstantImprovement.GreedyCompatibleRatioPath

/-! Proper infinite scalar-path selection for subexponential inverse weights.

The compact space contains improper paths whose costs can diverge.  We
therefore intersect finite-prefix sublevel sets directly, and do not assume
that the selected value is finite at every path.  The selected minimizing
path has all-rate product growth, forced by the positive geometric terminal
family.  This is a scalar relaxation theorem, not sharpness for admissible
laws or an optimization over all generator profiles.

This isolated source draft has not been compiled by its author. -/

noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.ProperInfiniteRatioPathSelection

open KLSConstantImprovement.CompatibleRatioPathCompact
open KLSConstantImprovement.GeometricTerminalGrowthExclusion
open KLSConstantImprovement.SubexponentialTerminalSupremum
open KLSConstantImprovement.SubexponentialTerminalContinuity
open KLSConstantImprovement.MonotoneCompactBellmanLimit

/-- Weight lower envelopes at every exponential rate, in orbit indices. -/
def FullFloors (w : ℕ → ℝ) : Prop :=
  ∀ ρ : ℝ, 1 < ρ → ∃ τ : ℝ, 0 < τ ∧ ∀ i : ℕ, τ ≤ w i * ρ ^ (i + 2)

/-- Cost divided by the initial factor `Z₁ = p`. -/
def prefixSpend (w r : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, w i * P r i * (r i - r (i + 1))

def prefixPotential (w r : ℕ → ℝ) (N : ℕ) : ℝ :=
  prefixSpend w r N + P r N * terminalSup w N (r N)

def finiteValue (A p : ℝ) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  minimumOn (ratioPathSet A p) (fun r => prefixPotential w r N)

/-- Literal supremum of compact finite-prefix minima, with positive terminal. -/
def infiniteValue (A p : ℝ) (w : ℕ → ℝ) : ℝ :=
  sSup (Set.range (fun N : ℕ => finiteValue A p w N))

theorem floors_nonempty {w : ℕ → ℝ} (hw : FullFloors w) : Nonempty (Floor w) := by
  obtain ⟨τ, hτ, hlow⟩ := hw 2 (by norm_num)
  exact ⟨⟨2, τ, by norm_num, hτ, hlow⟩⟩

theorem weight_nonnegative {w : ℕ → ℝ} (hF : Nonempty (Floor w)) (i : ℕ) :
    0 ≤ w i := by
  obtain ⟨f⟩ := hF
  exact (f.coeff_nonneg i).trans (f.coeff_le i)

theorem P_continuous (N : ℕ) : Continuous (fun r : ℕ → ℝ => P r N) := by
  induction N with
  | zero => simpa only [P_zero] using (continuous_const : Continuous (fun _ : ℕ → ℝ => (1 : ℝ)))
  | succ N ih =>
    refine ((continuous_mul : Continuous (fun z : ℝ × ℝ => z.1 * z.2)).comp
      (ih.prodMk (continuous_apply (N + 1)))).congr ?_
    intro r
    exact (P_succ r N).symm

theorem prefixSpend_continuous (w : ℕ → ℝ) (N : ℕ) :
    Continuous (fun r : ℕ → ℝ => prefixSpend w r N) := by
  unfold prefixSpend
  exact continuous_finsetSum (Finset.range N) (fun i _ =>
    (continuous_const.mul (P_continuous i)).mul
      ((continuous_apply i).sub (continuous_apply (i + 1))))

theorem prefixPotential_continuous {w : ℕ → ℝ} (hF : Nonempty (Floor w)) (N : ℕ) :
    Continuous (fun r : ℕ → ℝ => prefixPotential w r N) := by
  exact (prefixSpend_continuous w N).add
    ((P_continuous N).mul ((terminalSup_continuous hF N).comp (continuous_apply N)))

@[simp] theorem prefixSpend_zero (w r : ℕ → ℝ) : prefixSpend w r 0 = 0 := by
  simp only [prefixSpend, Finset.range_zero, Finset.sum_empty]

theorem prefixSpend_succ (w r : ℕ → ℝ) (N : ℕ) :
    prefixSpend w r (N + 1) =
      prefixSpend w r N + w N * P r N * (r N - r (N + 1)) := by
  simp only [prefixSpend, Finset.sum_range_succ]

theorem prefixSpend_nonnegative {A p : ℝ} {w r : ℕ → ℝ}
    (hF : Nonempty (Floor w)) (hr : r ∈ ratioPathSet A p) (N : ℕ) :
    0 ≤ prefixSpend w r N := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg
    (mul_nonneg (weight_nonnegative hF i) (P_nonnegative r (lower hr) i))
    (sub_nonneg.mpr (successor_le hr i))

theorem prefixSpend_le_potential {A p : ℝ} {w r : ℕ → ℝ}
    (hF : Nonempty (Floor w)) (hr : r ∈ ratioPathSet A p) (N : ℕ) :
    prefixSpend w r N ≤ prefixPotential w r N := by
  exact le_add_of_nonneg_right
    (mul_nonneg (P_nonnegative r (lower hr) N) (terminalSup_nonneg hF N (r N)))

theorem prefixPotential_nonnegative {A p : ℝ} {w r : ℕ → ℝ}
    (hF : Nonempty (Floor w)) (hr : r ∈ ratioPathSet A p) (N : ℕ) :
    0 ≤ prefixPotential w r N :=
  (prefixSpend_nonnegative hF hr N).trans (prefixSpend_le_potential hF hr N)

theorem prefixPotential_monotone {A p : ℝ} {w r : ℕ → ℝ}
    (hF : Nonempty (Floor w)) (hr : r ∈ ratioPathSet A p) :
    Monotone (prefixPotential w r) := by
  apply monotone_nat_of_le_succ
  intro N
  have hh := terminalSup_step hF N
    (show 0 ≤ r (N + 1) by linarith [lower hr (N + 1)])
    (sub_nonneg.mpr (successor_le hr N)) (le_refl (r N - r (N + 1)))
  have hm := mul_le_mul_of_nonneg_left hh (P_nonnegative r (lower hr) N)
  simp only [prefixPotential, prefixSpend_succ, P_succ]
  nlinarith only [hm]

theorem prefixPotential_succ_eq_of_one {w r : ℕ → ℝ}
    (hF : Nonempty (Floor w)) (N : ℕ) (hnow : r N = 1) (hnext : r (N + 1) = 1) :
    prefixPotential w r (N + 1) = prefixPotential w r N := by
  simp only [prefixPotential, prefixSpend_succ, P_succ, hnow, hnext,
    terminalSup_zero hF N le_rfl, terminalSup_zero hF (N + 1) le_rfl,
    sub_self, mul_zero, add_zero, mul_one]

theorem prefixPotential_eq_after {w r : ℕ → ℝ} (hF : Nonempty (Floor w))
    {M : ℕ} (hone : ∀ n : ℕ, M ≤ n → r n = 1) {N : ℕ} (hN : M ≤ N) :
    prefixPotential w r N = prefixPotential w r M := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    exact (prefixPotential_succ_eq_of_one hF N (hone N hN)
      (hone (N + 1) (by omega))).trans ih

/-- A finite-hit greedy completion bounds all finite minima.  It does not
bound the prefix potentials of every compatible path. -/
theorem bounded_witness {A p : ℝ} {w : ℕ → ℝ} (hA : 0 < A) (hp : 1 ≤ p)
    (hF : Nonempty (Floor w)) :
    ∃ r ∈ ratioPathSet A p, ∃ J : ℝ, ∀ N : ℕ, prefixPotential w r N ≤ J := by
  obtain ⟨r, hr, M, hone⟩ :=
    GreedyCompatibleRatioPath.exists_compatible_eventually_one hA hp
  refine ⟨r, hr, prefixPotential w r M, ?_⟩
  intro N
  by_cases hN : N ≤ M
  · exact prefixPotential_monotone hF hr hN
  · exact (prefixPotential_eq_after hF hone (by omega : M ≤ N)).le

theorem finiteValue_le {A p : ℝ} {w r : ℕ → ℝ} (hF : Nonempty (Floor w))
    (hr : r ∈ ratioPathSet A p) (N : ℕ) :
    finiteValue A p w N ≤ prefixPotential w r N :=
  minimumOn_le (isCompact_ratioPathSet_unrestricted A p)
    (prefixPotential_continuous hF N).continuousOn hr

theorem finiteValue_range_bounded {A p : ℝ} {w : ℕ → ℝ}
    (hA : 0 < A) (hp : 1 ≤ p) (hF : Nonempty (Floor w)) :
    BddAbove (Set.range (fun N : ℕ => finiteValue A p w N)) := by
  obtain ⟨r, hr, J, hJ⟩ := bounded_witness hA hp hF
  refine ⟨J, ?_⟩
  rintro y ⟨N, rfl⟩
  exact (finiteValue_le hF hr N).trans (hJ N)

theorem finiteValue_le_infiniteValue {A p : ℝ} {w : ℕ → ℝ}
    (hA : 0 < A) (hp : 1 ≤ p) (hF : Nonempty (Floor w)) (N : ℕ) :
    finiteValue A p w N ≤ infiniteValue A p w :=
  le_csSup (finiteValue_range_bounded hA hp hF) ⟨N, rfl⟩

/-- Compact nested sublevel selection with no improper-path finiteness premise. -/
theorem exists_selected_sublevel_path {A p : ℝ} {w : ℕ → ℝ}
    (hA : 0 < A) (hp : 1 ≤ p) (hF : Nonempty (Floor w)) :
    ∃ r ∈ ratioPathSet A p, ∀ N : ℕ,
      prefixPotential w r N ≤ infiniteValue A p w := by
  have hcompact := isCompact_ratioPathSet_unrestricted A p
  have hne := nonempty_ratioPathSet A p hA.le hp
  apply compact_simultaneous_sublevel hcompact
    (fun N r => prefixPotential w r N)
    (fun N => (prefixPotential_continuous hF N).continuousOn)
    (fun r hr => prefixPotential_monotone hF hr) (infiniteValue A p w)
  intro N
  obtain ⟨r, hr, he⟩ := hcompact.exists_sInf_image_eq hne
    (prefixPotential_continuous hF N).continuousOn
  have he' : prefixPotential w r N = finiteValue A p w N := he.symm
  exact ⟨r, hr, he'.le.trans (finiteValue_le_infiniteValue hA hp hF N)⟩

/-- Every fixed geometric terminal is bounded along the selected path. -/
theorem selected_geometric_bounds {A p : ℝ} {w r : ℕ → ℝ}
    (hw : FullFloors w) (hr : r ∈ ratioPathSet A p) {L : ℝ}
    (hpot : ∀ N : ℕ, prefixPotential w r N ≤ L) :
    ∀ ρ : ℝ, 1 < ρ → ∃ τ : ℝ, 0 < τ ∧ ∀ N : ℕ,
      P r N * (τ / ρ ^ (N + 2)) * max 0 (r N - ρ) ≤ L := by
  intro ρ hρ
  obtain ⟨τ, hτ, hlow⟩ := hw ρ hρ
  let f : Floor w := ⟨ρ, τ, hρ, hτ, hlow⟩
  have hF := floors_nonempty hw
  refine ⟨τ, hτ, ?_⟩
  intro N
  have hterm := mul_le_mul_of_nonneg_left (term_le_sup f N (r N))
    (P_nonnegative r (lower hr) N)
  have hterm' : P r N * ((τ / ρ ^ (N + 2)) * max 0 (r N - ρ)) ≤
      P r N * terminalSup w N (r N) := by
    simpa only [Floor.term, Floor.coeff, GeometricBellmanTerminal.B, f] using hterm
  have hs := prefixSpend_nonnegative hF hr N
  have hh := hpot N
  dsimp only [prefixPotential] at hh
  have hpaid : P r N * terminalSup w N (r N) ≤ L := by linarith only [hh, hs]
  simpa only [mul_assoc] using hterm'.trans hpaid

/-- The selected scalar path is proper: ratios enter every threshold above
one and its product has an all-rate subexponential envelope. -/
theorem exists_proper_selected_path {A p : ℝ} {w : ℕ → ℝ}
    (hA : 0 < A) (hp : 1 ≤ p) (hw : FullFloors w) :
    ∃ r : ℕ → ℝ, r ∈ ratioPathSet A p ∧
      (∀ N : ℕ, prefixPotential w r N ≤ infiniteValue A p w) ∧
      (∀ N : ℕ, prefixSpend w r N ≤ infiniteValue A p w) ∧
      (∀ q : ℝ, 1 < q → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → r n ≤ q) ∧
      (∀ q : ℝ, 1 < q → ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, P r n ≤ M * q ^ n) := by
  have hF := floors_nonempty hw
  obtain ⟨r, hr, hpot⟩ := exists_selected_sublevel_path hA hp hF
  have hterminal := selected_geometric_bounds hw hr hpot
  exact ⟨r, hr, hpot,
    fun N => (prefixSpend_le_potential hF hr N).trans (hpot N),
    eventual_ratio_le r (infiniteValue A p w) (antitone hr) (lower hr) hterminal,
    product_subexponential r (infiniteValue A p w) (antitone hr) (lower hr) hterminal⟩

end KLSConstantImprovement.ProperInfiniteRatioPathSelection

#print axioms KLSConstantImprovement.ProperInfiniteRatioPathSelection.prefixPotential_continuous
#print axioms KLSConstantImprovement.ProperInfiniteRatioPathSelection.prefixPotential_monotone
#print axioms KLSConstantImprovement.ProperInfiniteRatioPathSelection.exists_selected_sublevel_path
#print axioms KLSConstantImprovement.ProperInfiniteRatioPathSelection.exists_proper_selected_path
