import TripleProjectionDefinitions

/-! Exact triple counts, proved by counting contained coordinate subsets. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.TripleProjection
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

theorem sum_triple_values {M : Type*} [AddCommMonoid M]
    (f : Finset (Fin N) → M) :
    (∑ e : Triple N, f e.val) = ∑ e ∈ triples N, f e := by
  exact (Finset.sum_subtype (triples N) (fun e => mem_triples e) f).symm

theorem card_triple : Fintype.card (Triple N) = N.choose 3 := by
  have hh := sum_triple_values (N:=N) (fun _ => (1 : ℕ))
  simpa [triples] using hh

theorem triple_extension_count (s : Finset (Fin N)) (hs : s.card ≤ 3) :
    (∑ e : Triple N, if s ⊆ e.val then (1 : ℕ) else 0) =
      (N-s.card).choose (3-s.card) := by
  rw [sum_triple_values (fun e => if s ⊆ e then (1 : ℕ) else 0), ←Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  change ((Finset.univ.powersetCard 3).filter (fun e => s ⊆ e)).card = _
  rw [Finset.card_filter_powersetCard_subset s Finset.univ 3
    (Finset.subset_univ _) hs]
  simp

theorem triple_intersection_moment (e : Triple N) (k : ℕ) (hk : k ≤ 3) :
    (∑ f : Triple N, ((e.val ∩ f.val).card).choose k) =
      (3 : ℕ).choose k * (N-k).choose (3-k) := by
  classical
  have hc (f : Triple N) : ((e.val ∩ f.val).card).choose k =
      ∑ s ∈ e.val.powersetCard k, if s ⊆ f.val then (1 : ℕ) else 0 := by
    rw [←Finset.card_powersetCard, ←Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    ext s
    simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_inter_iff]
    tauto
  simp_rw [hc]
  rw [Finset.sum_comm]
  have hext (s : Finset (Fin N)) (hs : s ∈ e.val.powersetCard k) :
      (∑ f : Triple N, if s ⊆ f.val then (1 : ℕ) else 0) =
        (N-k).choose (3-k) := by
    have hcard := (Finset.mem_powersetCard.mp hs).2
    simpa [hcard] using triple_extension_count s (by omega)
  rw [Finset.sum_congr rfl hext]
  simp [Finset.card_powersetCard, e.property]

theorem triple_intersection_card_le_three (e f : Triple N) :
    (e.val ∩ f.val).card ≤ 3 :=
  (Finset.card_le_card Finset.inter_subset_left).trans_eq e.property

theorem triple_intersection_card_eq_three_iff (e f : Triple N) :
    (e.val ∩ f.val).card = 3 ↔ e=f := by
  constructor
  · intro hh
    apply Subtype.ext
    have he : e.val ∩ f.val=e.val :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [e.property,hh])
    have hsub : e.val ⊆ f.val := by rw [←he]; exact Finset.inter_subset_right
    exact Finset.eq_of_subset_of_card_le hsub (by rw [e.property,f.property])
  · intro hh
    subst f
    simp [e.property]

end KLSBelow25.TripleProjection
#print axioms KLSBelow25.TripleProjection.card_triple
#print axioms KLSBelow25.TripleProjection.triple_extension_count
#print axioms KLSBelow25.TripleProjection.triple_intersection_moment
