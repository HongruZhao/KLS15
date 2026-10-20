import KLSConstantImprovement.PositiveFiniteHeadBellman
import JointObservationScalarEndgame

/-! A constant post-head weight pays the positive tail line. The proof
uses the existing all-rate scalar orbit theorem at the next orbit value;
finite head weights need only be nonnegative. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.WeightedOrbitBellmanTail
open KLSBelow25.CoupledEnergy
set_option maxHeartbeats 4500000

def spend (w c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N,w i*c i

theorem spend_nonneg (w c : ℕ → ℝ) (hw : ∀ i,0 ≤ w i)
    (hc : ∀ i,0 ≤ c i) (N : ℕ) : 0 ≤ spend w c N :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hc i))

theorem spend_succ (w c : ℕ → ℝ) (N : ℕ) :
    spend w c (N+1)=spend w c N+w N*c N := by
  simp [spend,Finset.sum_range_succ]

theorem spend_add_tail (w c : ℕ → ℝ) {τ : ℝ} (N j : ℕ)
    (ht : ∀ i,N ≤ i → w i=τ) :
    spend w c (N+j)=spend w c N+τ*(∑ i∈Finset.range j,c (N+i)) := by
  rw [spend,Finset.sum_range_add]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ht (N+i) (by omega)]

theorem tail_payment (Z c w : ℕ → ℝ) {C τ : ℝ} (N : ℕ)
    (hτ : 0 < τ) (hZ : ∀ i,0 ≤ Z i) (hc : ∀ i,0 ≤ c i)
    (hzero : ∀ i,Z i=0 → Z (i+1)=0)
    (hrec : ∀ i,0 < Z i → 0 < Z (i+1) →
      Z (i+1)^2/Z i-c i ≤ Z (i+2))
    (ht : ∀ i,N ≤ i → w i=τ)
    (hbudget : ∀ j,spend w c j ≤ C)
    (henv : ∀ ρ : ℝ,1 < ρ → ∃ M : ℝ,∀ i,Z i ≤ M*ρ^i) :
    Z (N+1)*max 0 (τ*(Z (N+1)/Z N-1)) ≤ C-spend w c N := by
  have hrem (j : ℕ) : 0 ≤ C-spend w c j := by linarith [hbudget j]
  by_cases hz0 : Z (N+1)=0
  · simp only [hz0,zero_mul]
    exact hrem N
  have hz : 0 < Z (N+1) := lt_of_le_of_ne (hZ _) (Ne.symm hz0)
  have hZN : 0 < Z N := by
    by_contra hn
    have he : Z N=0 := le_antisymm (le_of_not_gt hn) (hZ N)
    exact hz0 (hzero N he)
  let z : ℝ := Z (N+1)
  let u : ℕ → ℝ := fun j=>Z (N+1+j)/z
  let b : ℕ → ℝ := fun j=>c (N+j)/z
  let D : ℝ := (C-spend w c (N+1))/(τ*z)
  have hz' : 0 < z := hz
  have hD : 0 ≤ D := div_nonneg (hrem _) (mul_nonneg hτ.le hz'.le)
  have hu0 : u 0=1 := by simp [u,z,ne_of_gt hz]
  have hb : ∀ j,0 ≤ b (j+1) := by intro j;exact div_nonneg (hc _) hz'.le
  have hbud : ∀ j,prefixBudget b j ≤ D := by
    intro j
    have ht' : ∀ i,N+1 ≤ i → w i=τ := fun i hi=>ht i (by omega)
    have hh := hbudget (N+1+j)
    rw [spend_add_tail w c (N+1) j ht'] at hh
    have hsum : (∑ i∈Finset.range j,c (N+1+i)) ≤ (C-spend w c (N+1))/τ :=
      (le_div_iff₀ hτ).mpr (by linarith)
    have hp : prefixBudget b j=(∑ i∈Finset.range j,c (N+1+i))/z := by
      simp only [prefixBudget,b,Finset.sum_div,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    rw [hp]
    have hd := div_le_div_of_nonneg_right hsum hz'.le
    convert hd using 1  <;> dsimp only [D]  <;> field_simp  <;> ring
  have hurec : ∀ j,0 < u j → 0 < u (j+1) →
      u (j+1)^2/u j-b (j+1) ≤ u (j+2) := by
    intro j hj hj1
    have h0 : 0 < Z (N+1+j) := (div_pos_iff_of_pos_right hz').mp hj
    have h1 : 0 < Z (N+1+j+1) := by
      apply (div_pos_iff_of_pos_right hz').mp
      simpa only [u,Nat.add_assoc] using hj1
    have hh := div_le_div_of_nonneg_right (hrec (N+1+j) h0 h1) hz'.le
    convert hh using 1  <;> dsimp only [u,b]  <;>
      simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]  <;> field_simp  <;> ring
  have huenv : ∀ ρ : ℝ,1 < ρ → ∃ M : ℝ,∀ j,u j ≤ M*ρ^j := by
    intro ρ hρ
    obtain ⟨M,hM⟩ := henv ρ hρ
    refine ⟨M*ρ^(N+1)/z,fun j=>?_⟩
    have hh := div_le_div_of_nonneg_right (hM (N+1+j)) hz'.le
    convert hh using 1 <;> (try dsimp only [u]) <;> (try rw [pow_add]) <;> ring
  have hu := normalized_orbit_le_one_add_budget u b hD hu0 hb hbud hurec huenv
  have hu' : Z (N+2) ≤ z+(C-spend w c (N+1))/τ := by
    have hh := (div_le_iff₀ hz').mp hu
    convert hh using 1 <;> (try dsimp only [u,D]) <;>
      (try simp only [Nat.add_assoc,Nat.reduceAdd]) <;> field_simp <;> ring
  have hr := hrec N hZN hz
  have he : z*(z/Z N-1)=Z (N+1)^2/Z N-z := by dsimp only [z];ring
  have hf : z*(z/Z N-1) ≤ c N+(C-spend w c (N+1))/τ := by
    rw [he]
    linarith
  have hf' := mul_le_mul_of_nonneg_left hf hτ.le
  have hsp : spend w c (N+1)=spend w c N+τ*c N := by
    rw [spend_succ,ht N (le_refl _)]
  have hpaid : z*(τ*(z/Z N-1)) ≤ C-spend w c N := by
    rw [hsp] at hf'
    have hid : τ*(c N+(C-(spend w c N+τ*c N))/τ)=C-spend w c N := by
      field_simp
      ring
    rw [hid] at hf'
    nlinarith only [hf']
  change z*max 0 (τ*(z/Z N-1)) ≤ C-spend w c N
  by_cases hp : 0 ≤ τ*(z/Z N-1)
  · rwa [max_eq_right hp]
  · rw [max_eq_left (le_of_not_ge hp),mul_zero]
    exact hrem N

end KLSConstantImprovement.WeightedOrbitBellmanTail
#print axioms KLSConstantImprovement.WeightedOrbitBellmanTail.tail_payment
