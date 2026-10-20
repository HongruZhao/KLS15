import Mathlib

/-! A compact minimum commutes with a bounded increasing finite-horizon
limit. This is the core needed for the variable-weight Bellman equation;
it does not assume continuity of the limiting value. The application to
all normalized-orbit paths and an outer method optimum is separate. -/
noncomputable section
namespace KLSConstantImprovement.MonotoneCompactBellmanLimit

def minimumOn {X : Type*} (S : Set X) (f : X → ℝ) : ℝ := sInf (f '' S)
def selected {X : Type*} (f : ℕ → X → ℝ) (x : X) : ℝ :=
  sSup (Set.range (fun n : ℕ=>f n x))
def selectedMinimum {X : Type*} (S : Set X) (f : ℕ → X → ℝ) : ℝ :=
  sSup (Set.range (fun n : ℕ=>minimumOn S (f n)))

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem compact_simultaneous_sublevel {S : Set X} (hS : IsCompact S)
    (f : ℕ → X → ℝ) (hcont : ∀ n,ContinuousOn (f n) S)
    (hmono : ∀ x∈S,Monotone (fun n=>f n x)) (L : ℝ)
    (hne : ∀ n,∃ x∈S,f n x ≤ L) :
    ∃ x∈S,∀ n,f n x ≤ L := by
  let E : ℕ → Set X := fun n=>{x∈S | f n x ≤ L}
  have hclosed (n : ℕ) : IsClosed (E n) :=
    hS.isClosed.isClosed_le (hcont n) continuousOn_const
  have hcompact : IsCompact (E 0) := hS.of_isClosed_subset (hclosed 0) (fun x hx=>hx.1)
  have hEnonempty (n : ℕ) : (E n).Nonempty := by
    obtain ⟨x,hx,hf⟩ := hne n
    exact ⟨x,hx,hf⟩
  have hnested (n : ℕ) : E (n+1) ⊆ E n := by
    intro x hx
    exact ⟨hx.1,(hmono x hx.1 (by omega : n ≤ n+1)).trans hx.2⟩
  obtain ⟨x,hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    E hnested hEnonempty hcompact hclosed
  have hxe (n : ℕ) : x∈E n := Set.mem_iInter.mp hx n
  exact ⟨x,(hxe 0).1,fun n=>(hxe n).2⟩

theorem minimumOn_le {S : Set X} (hS : IsCompact S) {f : X → ℝ}
    (hcont : ContinuousOn f S) {x : X} (hx : x∈S) : minimumOn S f ≤ f x :=
  csInf_le (hS.image_of_continuousOn hcont).bddBelow ⟨x,hx,rfl⟩

/-- An optimizer for the pointwise selected value exists and has value
equal to the supremum of the finite minima. Pointwise finite boundedness
is explicit; no uniform-convergence or limit-continuity premise is used. -/
theorem selected_minimum_attained {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    (f : ℕ → X → ℝ) (hcont : ∀ n,ContinuousOn (f n) S)
    (hmono : ∀ x∈S,Monotone (fun n=>f n x))
    (hbounded : ∀ x∈S,BddAbove (Set.range (fun n=>f n x))) :
    ∃ x∈S,selected f x=selectedMinimum S f ∧
      ∀ y∈S,selectedMinimum S f ≤ selected f y := by
  obtain ⟨x0,hx0⟩ := hne
  obtain ⟨M,hM⟩ := hbounded x0 hx0
  have hminBound : BddAbove (Set.range (fun n : ℕ=>minimumOn S (f n))) := by
    refine ⟨M,?_⟩
    rintro y ⟨n,rfl⟩
    exact (minimumOn_le hS (hcont n) hx0).trans (hM ⟨n,rfl⟩)
  have hminle (n : ℕ) : minimumOn S (f n) ≤ selectedMinimum S f :=
    le_csSup hminBound ⟨n,rfl⟩
  have hlow (y : X) (hy : y∈S) : selectedMinimum S f ≤ selected f y := by
    apply csSup_le (show (Set.range (fun n : ℕ=>minimumOn S (f n))).Nonempty from
      ⟨minimumOn S (f 0),⟨0,rfl⟩⟩)
    rintro z ⟨n,rfl⟩
    exact (minimumOn_le hS (hcont n) hy).trans (le_csSup (hbounded y hy) ⟨n,rfl⟩)
  have hsublevel (n : ℕ) : ∃ x∈S,f n x ≤ selectedMinimum S f := by
    obtain ⟨x,hx,he⟩ := hS.exists_sInf_image_eq ⟨x0,hx0⟩ (hcont n)
    exact ⟨x,hx,he.symm.le.trans (hminle n)⟩
  obtain ⟨x,hx,hall⟩ := compact_simultaneous_sublevel hS f hcont hmono
    (selectedMinimum S f) hsublevel
  have hupp : selected f x ≤ selectedMinimum S f := by
    apply csSup_le (show (Set.range (fun n : ℕ=>f n x)).Nonempty from ⟨f 0 x,⟨0,rfl⟩⟩)
    rintro y ⟨n,rfl⟩
    exact hall n
  exact ⟨x,hx,le_antisymm hupp (hlow x hx),hlow⟩

/-- Literal minimum/supremum interchange on the compact action interval. -/
theorem minimum_selected_eq_selected_minimum {S : Set X}
    (hS : IsCompact S) (hne : S.Nonempty)
    (f : ℕ → X → ℝ) (hcont : ∀ n,ContinuousOn (f n) S)
    (hmono : ∀ x∈S,Monotone (fun n=>f n x))
    (hbounded : ∀ x∈S,BddAbove (Set.range (fun n=>f n x))) :
    minimumOn S (selected f)=selectedMinimum S f := by
  obtain ⟨x,hx,he,hlow⟩ := selected_minimum_attained hS hne f hcont hmono hbounded
  have hb : BddBelow (selected f '' S) := by
    refine ⟨selectedMinimum S f,?_⟩
    rintro y ⟨z,hz,rfl⟩
    exact hlow z hz
  apply le_antisymm
  · exact (csInf_le hb ⟨x,hx,rfl⟩).trans_eq he
  · apply le_csInf (hne.image (selected f))
    rintro y ⟨z,hz,rfl⟩
    exact hlow z hz

end KLSConstantImprovement.MonotoneCompactBellmanLimit
#print axioms KLSConstantImprovement.MonotoneCompactBellmanLimit.compact_simultaneous_sublevel
#print axioms KLSConstantImprovement.MonotoneCompactBellmanLimit.selected_minimum_attained
#print axioms KLSConstantImprovement.MonotoneCompactBellmanLimit.minimum_selected_eq_selected_minimum
