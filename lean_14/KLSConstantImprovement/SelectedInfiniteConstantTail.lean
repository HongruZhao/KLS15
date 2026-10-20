import KLSConstantImprovement.ConstantTailFiniteHitting

/-! Literal infinite-horizon selection: the supremum of the increasing
proper finite horizons equals a finite value after a zero hit.  This is
the selected Bellman solution, not the spurious zero fixed point. -/
noncomputable section
namespace KLSConstantImprovement.SelectedInfiniteConstantTail
open KLSConstantImprovement.ProperConstantTailRecursion
open KLSConstantImprovement.ConstantTailFiniteHitting

def selectedExcess (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup (Set.range (fun n : ℕ => excess f n x))

def selectedValue (f : ℝ → ℝ) (τ r : ℝ) : ℝ :=
  τ*((r-1)+selectedExcess f (r-1))

theorem horizon_mono (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x) (x : ℝ) :
    Monotone (fun n : ℕ => excess f n x) :=
  monotone_nat_of_le_succ (fun n => excess_le_succ f hf n x)

theorem excess_le_at_hit (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    (hf0 : f 0=0) (N : ℕ) (x : ℝ) (hhit : path f N x=0)
    (n : ℕ) : excess f n x ≤ excess f N x := by
  by_cases hn : n ≤ N
  · exact horizon_mono f hf x hn
  · have he : n=N+(n-N) := by omega
    rw [he,excess_stabilizes f hf0 N (n-N) x hhit]

/-- This is the precise infinite-horizon limit theorem.  Boundedness of
the real supremum is proved from a finite hit, rather than assumed. -/
theorem selectedExcess_eq_at_hit (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    (hf0 : f 0=0) (N : ℕ) (x : ℝ) (hhit : path f N x=0) :
    selectedExcess f x=excess f N x := by
  have hb : BddAbove (Set.range (fun n : ℕ => excess f n x)) := by
    refine ⟨excess f N x,?_⟩
    rintro y ⟨n,rfl⟩
    exact excess_le_at_hit f hf hf0 N x hhit n
  have hn : (Set.range (fun n : ℕ => excess f n x)).Nonempty :=
    ⟨excess f 0 x,⟨0,rfl⟩⟩
  unfold selectedExcess
  apply le_antisymm
  · apply csSup_le hn
    rintro y ⟨n,rfl⟩
    exact excess_le_at_hit f hf hf0 N x hhit n
  · exact le_csSup hb ⟨N,rfl⟩

theorem selectedExcess_eq_later (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    (hf0 : f 0=0) (N n : ℕ) (x : ℝ) (hhit : path f N x=0)
    (hn : N ≤ n) : selectedExcess f x=excess f n x := by
  rw [selectedExcess_eq_at_hit f hf hf0 N x hhit]
  have he : n=N+(n-N) := by omega
  rw [he,excess_stabilizes f hf0 N (n-N) x hhit]

/-- Exact selected Bellman equation at the least permitted successor. -/
theorem selectedExcess_bellman (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    (hf0 : f 0=0) (N : ℕ) (x : ℝ) (hhit : path f N x=0) :
    selectedExcess f x=(f x)^2+(1+f x)*selectedExcess f (f x) := by
  cases N with
  | zero =>
      have hx : x=0 := hhit
      subst x
      have he : selectedExcess f 0=0 := by
        simpa only [excess] using selectedExcess_eq_at_hit f hf hf0 0 0 rfl
      simp [hf0,he]
  | succ N =>
      have hh : path f N (f x)=0 := hhit
      rw [selectedExcess_eq_at_hit f hf hf0 (N+1) x hhit,
        selectedExcess_eq_at_hit f hf hf0 N (f x) hh]
      rfl

/-- The selected equation is a minimum, not merely a fixed point: every
other allowed successor pays at least its left side. -/
theorem selectedExcess_le_action (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    (hm : Monotone f) (hf0 : f 0=0) (N M : ℕ) (x z : ℝ)
    (hxhit : path f N x=0) (hzhit : path f M z=0) (hz : f x ≤ z) :
    selectedExcess f x ≤ z^2+(1+z)*selectedExcess f z := by
  have hh := greedy_minimum f hf hm (N+M) x z hz
  rw [←selectedExcess_eq_later f hf hf0 N (N+M+1) x hxhit (by omega),
    ←selectedExcess_eq_later f hf hf0 M (N+M) z hzhit (by omega)] at hh
  exact hh

theorem selectedValue_greedy (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    (hf0 : f 0=0) (N : ℕ) (τ r : ℝ) (hhit : path f N (r-1)=0) :
    selectedValue f τ r=
      τ*(r-(1+f (r-1)))+(1+f (r-1))*selectedValue f τ (1+f (r-1)) := by
  have he := selectedExcess_bellman f hf hf0 N (r-1) hhit
  unfold selectedValue
  rw [show 1+f (r-1)-1=f (r-1) by ring,he]
  ring

theorem exact_selected_finite {A R x : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hx : 0 ≤ x) (hxR : x ≤ R-1) (N : ℕ)
    (hcount : R-1 ≤ (N : ℝ)*(A/R)) :
    selectedExcess (exactStep A) x=excess (exactStep A) N x := by
  exact selectedExcess_eq_at_hit (exactStep A) (exactStep_nonneg A)
    (exactStep_zero hA) N x (exactStep_hits hA hR hx hxR N hcount)

theorem chord_selected_finite {A R x : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hx : 0 ≤ x) (hxR : x ≤ R-1) (N : ℕ)
    (hcount : R-1 ≤ (N : ℝ)*(A/R)) :
    selectedExcess (chordStep A R) x=excess (chordStep A R) N x := by
  exact selectedExcess_eq_at_hit (chordStep A R) (chordStep_nonneg A R)
    (chordStep_zero hA) N x (chordStep_hits hA hR hx hxR N hcount)

theorem exact_selected_bellman {A R x : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hx : 0 ≤ x) (hxR : x ≤ R-1) (N : ℕ)
    (hcount : R-1 ≤ (N : ℝ)*(A/R)) :
    selectedExcess (exactStep A) x=(exactStep A x)^2+
      (1+exactStep A x)*selectedExcess (exactStep A) (exactStep A x) := by
  exact selectedExcess_bellman (exactStep A) (exactStep_nonneg A)
    (exactStep_zero hA) N x (exactStep_hits hA hR hx hxR N hcount)

end KLSConstantImprovement.SelectedInfiniteConstantTail
#print axioms KLSConstantImprovement.SelectedInfiniteConstantTail.selectedExcess_eq_at_hit
#print axioms KLSConstantImprovement.SelectedInfiniteConstantTail.selectedExcess_bellman
#print axioms KLSConstantImprovement.SelectedInfiniteConstantTail.selectedExcess_le_action
#print axioms KLSConstantImprovement.SelectedInfiniteConstantTail.selectedValue_greedy
#print axioms KLSConstantImprovement.SelectedInfiniteConstantTail.exact_selected_finite
#print axioms KLSConstantImprovement.SelectedInfiniteConstantTail.chord_selected_finite
#print axioms KLSConstantImprovement.SelectedInfiniteConstantTail.exact_selected_bellman
