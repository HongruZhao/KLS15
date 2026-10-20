import PairProjectionDefinitions

/-! Simultaneous finite-set orbits. Equality of the intersection cardinality
is precisely the extra invariant for two pairs of fixed cardinality. -/
noncomputable section
namespace KLSBelow25.PairProjection
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

private def pairColor {α : Type*} [DecidableEq α] (s t : Finset α) (a : α) : Bool×Bool :=
  (decide (a∈s),decide (a∈t))

private theorem colorFiber_card {α : Type*} [Fintype α] [DecidableEq α]
    (s t : Finset α) (b c : Bool) :
    Fintype.card {a : α // pairColor s t a=(b,c)}=
      ((if b then s else Finset.univ\s)∩(if c then t else Finset.univ\t)).card := by
  let e : {a : α // pairColor s t a=(b,c)}≃
      {a : α // a∈((if b then s else Finset.univ\s)∩(if c then t else Finset.univ\t))} :=
    Equiv.subtypeEquivRight (fun a => by cases b <;> cases c <;> simp [pairColor])
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

theorem exists_finset_pair_permutation {α : Type*} [Fintype α] [DecidableEq α]
    (s t s' t' : Finset α) (hs : s.card=s'.card) (ht : t.card=t'.card)
    (hi : (s∩t).card=(s'∩t').card) :
    ∃ π : Equiv.Perm α,s.map π.toEmbedding=s' ∧ t.map π.toEmbedding=t' := by
  classical
  have hdiffs : (s\t).card=(s'\t').card := by
    have h1 := Finset.card_sdiff_add_card_inter s t
    have h2 := Finset.card_sdiff_add_card_inter s' t'
    omega
  have hdifft : (t\s).card=(t'\s').card := by
    have h1 := Finset.card_sdiff_add_card_inter t s
    have h2 := Finset.card_sdiff_add_card_inter t' s'
    rw [Finset.inter_comm t s] at h1
    rw [Finset.inter_comm t' s'] at h2
    omega
  have hunion : (s∪t).card=(s'∪t').card := by
    have h1 := Finset.card_union_add_card_inter s t
    have h2 := Finset.card_union_add_card_inter s' t'
    omega
  have hcomp : (Finset.univ\(s∪t)).card=(Finset.univ\(s'∪t')).card := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (s∪t))
    have h2 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (s'∪t'))
    omega
  have hcards (a : Bool×Bool) :
      Fintype.card {x : α // pairColor s t x=a}=
        Fintype.card {x : α // pairColor s' t' x=a} := by
    rcases a with ⟨b,c⟩
    rw [colorFiber_card,colorFiber_card]
    cases b <;> cases c
    · have he (a b : Finset α) : (Finset.univ\a)∩(Finset.univ\b)=Finset.univ\(a∪b) := by
        ext x;simp
      simpa only [Bool.false_eq_true,↓reduceIte,he] using hcomp
    · have he (a b : Finset α) : (Finset.univ\a)∩b=b\a := by ext x;simp;tauto
      simpa only [Bool.false_eq_true,↓reduceIte,he] using hdifft
    · have he (a b : Finset α) : a∩(Finset.univ\b)=a\b := by ext x;simp
      simpa only [Bool.false_eq_true,↓reduceIte,he] using hdiffs
    · simpa using hi
  let ef (a : Bool×Bool) : {x : α // pairColor s t x=a}≃{x : α // pairColor s' t' x=a} :=
    Fintype.equivOfCardEq (hcards a)
  let π : Equiv.Perm α := Equiv.ofFiberEquiv ef
  have hmap (x : α) : pairColor s' t' (π x)=pairColor s t x :=
    Equiv.ofFiberEquiv_map ef x
  have hm1 (x : α) : π x∈s' ↔ x∈s := by
    have hh := congrArg Prod.fst (hmap x)
    simpa [pairColor] using hh
  have hm2 (x : α) : π x∈t' ↔ x∈t := by
    have hh := congrArg Prod.snd (hmap x)
    simpa [pairColor] using hh
  refine ⟨π,?_,?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
      exact (hm1 a).mpr ha
    · intro hx
      apply Finset.mem_map.mpr
      refine ⟨π.symm x,?_,by simp⟩
      exact (hm1 (π.symm x)).mp (by simpa using hx)
  · ext x
    constructor
    · intro hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
      exact (hm2 a).mpr ha
    · intro hx
      apply Finset.mem_map.mpr
      refine ⟨π.symm x,?_,by simp⟩
      exact (hm2 (π.symm x)).mp (by simpa using hx)

theorem exists_pair_permutation {N : ℕ} (e f e' f' : Pair N)
    (hinter : (e.val∩f.val).card=(e'.val∩f'.val).card) :
    ∃ π : Equiv.Perm (Fin N),e.val.map π.toEmbedding=e'.val ∧ f.val.map π.toEmbedding=f'.val :=
  exists_finset_pair_permutation e.val f.val e'.val f'.val
    (e.property.trans e'.property.symm) (f.property.trans f'.property.symm) hinter

end KLSBelow25.PairProjection
#print axioms KLSBelow25.PairProjection.exists_finset_pair_permutation
#print axioms KLSBelow25.PairProjection.exists_pair_permutation
