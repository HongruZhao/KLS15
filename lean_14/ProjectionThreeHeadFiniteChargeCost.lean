import ProjectionSlackFiniteChargeCost

/-! Three true head denominators and a finite later-floor budget.
No actual scalar instance, orbit growth, or improved universal endpoint is assumed. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.ProjectionSlackRatio

theorem three_head_tail_ratio_cost_le
    (l V p u v H C c1 c2 c3 tailC d1 d2 d3 tailD : ℝ)
    (hl : 0 < l) (hl1 : l ≤ 1) (hV : 0 < V)
    (hp : 0 < p) (hu : 0 < u) (hv : 0 < v)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (hbudget : c1+c2+c3+tailC ≤ C)
    (hline : (1/p-1/V)*c1+(1/u-1/V)*c2+(1/v-1/V)*c3 ≤ H)
    (hd1 : d1 ≤ c1/p) (hd2 : d2 ≤ c2/u) (hd3 : d3 ≤ c3/v)
    (htail : tailD ≤ tailC/(l*V)) :
    d1+d2+d3+tailD ≤ (H+C/V)/l := by
  have h1 : l*d1 ≤ c1/p := (mul_le_mul_of_nonneg_left hd1 hl.le).trans
    (by nlinarith [div_nonneg hc1 hp.le])
  have h2 : l*d2 ≤ c2/u := (mul_le_mul_of_nonneg_left hd2 hl.le).trans
    (by nlinarith [div_nonneg hc2 hu.le])
  have h3 : l*d3 ≤ c3/v := (mul_le_mul_of_nonneg_left hd3 hl.le).trans
    (by nlinarith [div_nonneg hc3 hv.le])
  have he : l*(tailC/(l*V))=tailC/V := by field_simp
  have ht : l*tailD ≤ tailC/V := by
    simpa only [he] using mul_le_mul_of_nonneg_left htail hl.le
  have hb := div_le_div_of_nonneg_right hbudget hV.le
  have hid : (1/p-1/V)*c1+(1/u-1/V)*c2+(1/v-1/V)*c3+(c1+c2+c3+tailC)/V=
      c1/p+c2/u+c3/v+tailC/V := by ring
  apply (le_div_iff₀ hl).mpr
  nlinarith

theorem finite_prefix_three_head_ratio_cost_le
    (c z d : ℕ → ℝ) (l V p u v H C : ℝ)
    (hl : 0 < l) (hl1 : l ≤ 1) (hV : 0 < V)
    (hp : 0 < p) (hu : 0 < u) (hv : 0 < v)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, d i = c i/z i)
    (hz0 : p ≤ z 0) (hz1 : u ≤ z 1) (hz2 : v ≤ z 2)
    (N : ℕ) (hN : 3 ≤ N)
    (hfloor : ∀ i, 3 ≤ i → i < N → l*V ≤ z i)
    (hbudget : (∑ i∈Finset.range N,c i) ≤ C)
    (hline : (1/p-1/V)*c 0+(1/u-1/V)*c 1+(1/v-1/V)*c 2 ≤ H) :
    (∑ i∈Finset.range N,d i) ≤ (H+C/V)/l := by
  have hs (f : ℕ → ℝ) :
      (∑ i∈Finset.range N,f i)=f 0+f 1+f 2+∑ i∈Finset.range (N-3),f (i+3) := by
    have hn : N=3+(N-3) := by omega
    conv_lhs => rw [hn,Finset.sum_range_add]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm])
  have htail : (∑ i∈Finset.range (N-3),d (i+3)) ≤
      (∑ i∈Finset.range (N-3),c (i+3))/(l*V) := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    rw [hd]
    exact div_le_div_of_nonneg_left (hc _) (mul_pos hl hV)
      (hfloor (i+3) (by omega) (by have := Finset.mem_range.mp hi;omega))
  have hd0 : d 0 ≤ c 0/p := by
    rw [hd]
    exact div_le_div_of_nonneg_left (hc 0) hp hz0
  have hd1 : d 1 ≤ c 1/u := by
    rw [hd]
    exact div_le_div_of_nonneg_left (hc 1) hu hz1
  have hd2 : d 2 ≤ c 2/v := by
    rw [hd]
    exact div_le_div_of_nonneg_left (hc 2) hv hz2
  rw [hs] at hbudget ⊢
  exact three_head_tail_ratio_cost_le l V p u v H C (c 0) (c 1) (c 2)
    (∑ i∈Finset.range (N-3),c (i+3)) (d 0) (d 1) (d 2)
    (∑ i∈Finset.range (N-3),d (i+3))
    hl hl1 hV hp hu hv (hc 0) (hc 1) (hc 2) hbudget hline hd0 hd1 hd2 htail

end KLSBelow25.ProjectionSlackRatio
#print axioms KLSBelow25.ProjectionSlackRatio.three_head_tail_ratio_cost_le
#print axioms KLSBelow25.ProjectionSlackRatio.finite_prefix_three_head_ratio_cost_le
