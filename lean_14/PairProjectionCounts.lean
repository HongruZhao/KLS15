import PairProjectionDefinitions

/-! Exact unordered-pair and vertex-incidence counts. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.PairProjection
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

theorem sum_pair_values {M : Type*} [AddCommMonoid M]
    (f : Finset (Fin N) → M) :
    (∑ e : Pair N, f e.val) = ∑ e ∈ pairs N, f e := by
  exact (Finset.sum_subtype (pairs N) (fun e => mem_pairs e) f).symm

theorem card_pair : Fintype.card (Pair N) = N.choose 2 := by
  have hh := sum_pair_values (N:=N) (fun _ => (1 : ℕ))
  simpa [pairs] using hh

theorem card_pair_real : (Fintype.card (Pair N) : ℝ) = (N : ℝ)*((N : ℝ)-1)/2 := by
  rw [card_pair,Nat.cast_choose_two]

theorem pair_incidence_count (i : Fin N) :
    ((Finset.univ.filter (fun e : Pair N => i ∈ e.val)).card : ℝ) = (N : ℝ)-1 := by
  have hs : (∑ e : Pair N, if i ∈ e.val then (1 : ℝ) else 0) =
      (N : ℝ)-1 := by
    rw [sum_pair_values (fun e => if i∈e then (1 : ℝ) else 0)]
    have hfilter : (pairs N).filter (fun e => i ∈ e) =
        (Finset.univ.powersetCard 2).filter (fun e => ({i} : Finset (Fin N)) ⊆ e) := by
      ext e
      simp [pairs]
    rw [←Finset.sum_filter,hfilter]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    rw [Finset.card_filter_powersetCard_subset {i} Finset.univ 2
      (Finset.subset_univ _) (by simp)]
    simp only [Finset.card_univ,Fintype.card_fin,Finset.card_singleton,
      Nat.reduceSub,Nat.choose_one_right]
    rw [Nat.cast_sub (by have hi:=i.isLt; omega : 1≤N)]
    norm_num
  simpa only [←Finset.sum_filter,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using hs

theorem sum_pair_incidence (i : Fin N) :
    (∑ e : Pair N, if i ∈ e.val then (1 : ℝ) else 0) = (N : ℝ)-1 := by
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,pair_incidence_count]

theorem sum_pair_intersection (e : Pair N) :
    (∑ f : Pair N, ((e.val ∩ f.val).card : ℝ)) = 2*((N : ℝ)-1) := by
  have hc (f : Pair N) : ((e.val ∩ f.val).card : ℝ) =
      ∑ i ∈ e.val, if i ∈ f.val then (1 : ℝ) else 0 := by
    rw [←Finset.sum_filter]
    have he : e.val.filter (fun i => i∈f.val) = e.val ∩ f.val := by ext i; simp
    rw [he]
    simp
  simp_rw [hc]
  rw [Finset.sum_comm]
  simp_rw [sum_pair_incidence]
  simp only [Finset.sum_const,nsmul_eq_mul,e.property,Nat.cast_ofNat]

theorem pair_intersection_card_le_two (e f : Pair N) : (e.val ∩ f.val).card ≤ 2 := by
  exact (Finset.card_le_card Finset.inter_subset_left).trans_eq e.property

theorem pair_intersection_card_eq_two_iff (e f : Pair N) :
    (e.val ∩ f.val).card = 2 ↔ e=f := by
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

theorem pair_intersection_card_of_ne {e f : Pair N} (hef : e≠f)
    (hne : (e.val ∩ f.val).Nonempty) : (e.val ∩ f.val).card=1 := by
  have hp := Finset.card_pos.mpr hne
  have hl := pair_intersection_card_le_two e f
  have hn : (e.val ∩ f.val).card≠2 := by
    intro hh
    exact hef ((pair_intersection_card_eq_two_iff e f).mp hh)
  omega

end KLSBelow25.PairProjection
#print axioms KLSBelow25.PairProjection.card_pair_real
#print axioms KLSBelow25.PairProjection.pair_incidence_count
#print axioms KLSBelow25.PairProjection.sum_pair_intersection
