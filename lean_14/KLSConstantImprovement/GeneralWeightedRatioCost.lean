import ProjectionThreeHeadFiniteChargeCost

/-! Three-head orbit payment with a positive degree-weight profile. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.GeneralWeightedRatioCost
open KLSBelow25.ProjectionSlackRatio
set_option maxHeartbeats 2000000

theorem finite_prefix_weighted_three_head_ratio_cost_le
    (c z d t : ℕ→ℝ) (l V p u v H C τ : ℝ)
    (hl : 0 < l) (hl1 : l ≤ 1) (hV : 0 < V) (hp : 0 < p) (hu : 0 < u) (hv : 0 < v)
    (hτ : 0 < τ) (ht : ∀ i, 0 < t i)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, d i=c i/z i)
    (hz0 : p ≤ z 0) (hz1 : u ≤ z 1) (hz2 : v ≤ z 2)
    (N : ℕ) (hN : 3 ≤ N)
    (hfloor : ∀ i, 3 ≤ i → i < N → l*V ≤ z i)
    (htail : ∀ i, 3 ≤ i → i < N → τ ≤ t i)
    (hbudget : (∑ i∈Finset.range N,t i*c i) ≤ C)
    (hline : (1/p-t 0/(τ*V))*c 0+(1/u-t 1/(τ*V))*c 1+
      (1/v-t 2/(τ*V))*c 2 ≤ H) :
    (∑ i∈Finset.range N,d i) ≤ (H+C/(τ*V))/l := by
  have he (i : ℕ) : d i=(t i*c i)/(t i*z i) := by
    rw [hd]
    field_simp [ne_of_gt (ht i)]
  apply finite_prefix_three_head_ratio_cost_le (fun i => t i*c i) (fun i => t i*z i) d
    l (τ*V) (t 0*p) (t 1*u) (t 2*v) H C hl hl1 (mul_pos hτ hV)
    (mul_pos (ht 0) hp) (mul_pos (ht 1) hu) (mul_pos (ht 2) hv)
    (fun i => mul_nonneg (ht i).le (hc i)) he
    (mul_le_mul_of_nonneg_left hz0 (ht 0).le)
    (mul_le_mul_of_nonneg_left hz1 (ht 1).le)
    (mul_le_mul_of_nonneg_left hz2 (ht 2).le) N hN
  · intro i hi hiN
    have hz := hfloor i hi hiN
    have hti := htail i hi hiN
    have h1 := mul_le_mul_of_nonneg_left hz (ht i).le
    have h2 := mul_le_mul_of_nonneg_right hti (mul_pos hl hV).le
    nlinarith only [h1,h2]
  · exact hbudget
  · convert hline using 1  <;> field_simp [ne_of_gt (ht 0),ne_of_gt (ht 1),ne_of_gt (ht 2)]  <;> ring

end KLSConstantImprovement.GeneralWeightedRatioCost
#print axioms KLSConstantImprovement.GeneralWeightedRatioCost.finite_prefix_weighted_three_head_ratio_cost_le
