import ProjectionSlackFiniteAnchor
noncomputable section
open scoped BigOperators
namespace KLSBelow25.ProjectionSlackRatio

/-- Head denominators use their individual lower bounds; only the later
amplitudes use the bootstrap floor. -/
theorem finite_prefix_ratio_cost_le
    (c z d : ℕ → ℝ) (l V p u H C : ℝ)
    (hl : 0 < l) (hl1 : l ≤ 1) (hV : 0 < V) (hp : 0 < p) (hu : 0 < u)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, d i = c i / z i)
    (hz0 : p ≤ z 0) (hz1 : u ≤ z 1)
    (N : ℕ) (hN : 2 ≤ N)
    (hfloor : ∀ i, 2 ≤ i → i < N → l*V ≤ z i)
    (hbudget : (∑ i∈Finset.range N, c i) ≤ C)
    (hline : (1/p-1/V)*c 0+(1/u-1/V)*c 1 ≤ H) :
    (∑ i∈Finset.range N, d i) ≤ (H+C/V)/l := by
  have hs (f : ℕ → ℝ) :
      (∑ i∈Finset.range N, f i) =
        f 0+f 1+∑ i∈Finset.range (N-2), f (i+2) := by
    have hn : N=2+(N-2) := by omega
    conv_lhs => rw [hn, Finset.sum_range_add]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm])
  have htail : (∑ i∈Finset.range (N-2), d (i+2)) ≤
      (∑ i∈Finset.range (N-2), c (i+2))/(l*V) := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    rw [hd]
    exact div_le_div_of_nonneg_left (hc _) (mul_pos hl hV)
      (hfloor (i+2) (by omega) (by have := Finset.mem_range.mp hi; omega))
  have hd0 : d 0 ≤ c 0/p := by
    rw [hd]
    exact div_le_div_of_nonneg_left (hc 0) hp hz0
  have hd1 : d 1 ≤ c 1/u := by
    rw [hd]
    exact div_le_div_of_nonneg_left (hc 1) hu hz1
  rw [hs] at hbudget ⊢
  exact head_tail_ratio_cost_le l V p u H C (c 0) (c 1)
    (∑ i∈Finset.range (N-2),c (i+2)) (d 0) (d 1)
    (∑ i∈Finset.range (N-2),d (i+2))
    hl hl1 hV hp hu (hc 0) (hc 1) hbudget hline hd0 hd1 htail

end KLSBelow25.ProjectionSlackRatio
#print axioms KLSBelow25.ProjectionSlackRatio.finite_prefix_ratio_cost_le
