import KLSConstantImprovement.WeightedOrbitBellmanTail

/-! A positive geometric terminal payment for weights without a uniform
floor.  Each exponential lower floor is kept with its exact stage factor.
This is valid for the actual normalized-orbit hypotheses and all-rate
envelope. No cap, upper ratio, or new analytic premise is used. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.GeometricWeightedTailPayment
open KLSConstantImprovement.WeightedOrbitBellmanTail

theorem rescaled_recurrence_identity (x y c ρ : ℝ) (i : ℕ)
    (hx : x≠0) (hρ : ρ≠0) :
    (y/ρ^(i+1))^2/(x/ρ^i)-c/ρ^(i+2)=(y^2/x-c)/ρ^(i+2) := by
  simp only [pow_succ]
  field_simp [hx,hρ] <;> ring

theorem rescaled_ratio (x y ρ : ℝ) (i : ℕ) (hρ : ρ≠0) :
    (y/ρ^(i+1))/(x/ρ^i)=(y/x)/ρ := by
  by_cases hx : x=0
  · simp [hx]
  · simp only [pow_succ]
    field_simp [hx,hρ] <;> ring

theorem terminal_scaling (z r τ ρ : ℝ) (N : ℕ) (hρ : 0 < ρ) :
    (z/ρ^(N+1))*max 0 (τ*(r/ρ-1))=
      z*max 0 ((τ/ρ^(N+2))*(r-ρ)) := by
  have he : (τ*(r/ρ-1))/ρ^(N+1)=(τ/ρ^(N+2))*(r-ρ) := by
    simp only [pow_succ]
    field_simp [ne_of_gt hρ] <;> ring
  calc
    _=z*(max 0 (τ*(r/ρ-1))/ρ^(N+1)) := by ring
    _=z*max 0 ((τ*(r/ρ-1))/ρ^(N+1)) := by
      rw [←max_div_div_right (pow_nonneg hρ.le (N+1)),zero_div]
    _=_ := by rw [he]

/-- A geometric lower floor provides the correct positive tail terminal
for a general weight profile.  In particular this applies to reciprocal
polynomial weights, for which a constant positive floor is unavailable. -/
theorem geometric_tail_payment (Z c w : ℕ → ℝ) {C τ ρ : ℝ} (N : ℕ)
    (hτ : 0 < τ) (hρ : 1 < ρ)
    (hZ : ∀ i,0 ≤ Z i) (hc : ∀ i,0 ≤ c i)
    (hzero : ∀ i,Z i=0 → Z (i+1)=0)
    (hrec : ∀ i,0 < Z i → 0 < Z (i+1) →
      Z (i+1)^2/Z i-c i ≤ Z (i+2))
    (hfloor : ∀ i,N ≤ i → τ ≤ w i*ρ^(i+2))
    (hbudget : ∀ j,spend w c j ≤ C)
    (henv : ∀ q : ℝ,1 < q → ∃ M : ℝ,∀ i,Z i ≤ M*q^i) :
    Z (N+1)*max 0 ((τ/ρ^(N+2))*(Z (N+1)/Z N-ρ)) ≤
      C-spend w c N := by
  have hρ0 : 0 < ρ := by linarith
  have hρne : ρ≠0 := ne_of_gt hρ0
  let Zρ : ℕ → ℝ := fun i=>Z i/ρ^i
  let cρ : ℕ → ℝ := fun i=>c i/ρ^(i+2)
  let v : ℕ → ℝ := fun i=>if i<N then w i*ρ^(i+2) else τ
  have hZρ (i : ℕ) : 0 ≤ Zρ i := div_nonneg (hZ i) (pow_nonneg hρ0.le i)
  have hcρ (i : ℕ) : 0 ≤ cρ i := div_nonneg (hc i) (pow_nonneg hρ0.le (i+2))
  have hzeroρ (i : ℕ) (hi : Zρ i=0) : Zρ (i+1)=0 := by
    have hz : Z i=0 := by
      have hh := congrArg (fun x : ℝ=>x*ρ^i) hi
      dsimp only [Zρ] at hh
      field_simp [hρne] at hh
      simpa using hh
    simp only [Zρ,hzero i hz,zero_div]
  have hrecρ (i : ℕ) (hi : 0 < Zρ i) (hi1 : 0 < Zρ (i+1)) :
      Zρ (i+1)^2/Zρ i-cρ i ≤ Zρ (i+2) := by
    have h0 : 0 < Z i := (div_pos_iff_of_pos_right (pow_pos hρ0 i)).mp hi
    have h1 : 0 < Z (i+1) :=
      (div_pos_iff_of_pos_right (pow_pos hρ0 (i+1))).mp hi1
    have hh := div_le_div_of_nonneg_right (hrec i h0 h1)
      (pow_nonneg hρ0.le (i+2))
    change (Z (i+1)/ρ^(i+1))^2/(Z i/ρ^i)-c i/ρ^(i+2) ≤
      Z (i+2)/ρ^(i+2)
    rw [rescaled_recurrence_identity (Z i) (Z (i+1)) (c i) ρ i
      (ne_of_gt h0) hρne]
    exact hh
  have hbudgetρ (j : ℕ) : spend v cρ j ≤ C := by
    apply le_trans _ (hbudget j)
    unfold spend
    apply Finset.sum_le_sum
    intro i hi
    by_cases hiN : i<N
    · change (if i<N then w i*ρ^(i+2) else τ)*(c i/ρ^(i+2)) ≤ w i*c i
      rw [if_pos hiN]
      have he : (w i*ρ^(i+2))*(c i/ρ^(i+2))=w i*c i := by
        field_simp [hρne] <;> ring
      exact he.le
    · have hNi : N ≤ i := by omega
      change (if i<N then w i*ρ^(i+2) else τ)*cρ i ≤ w i*c i
      rw [if_neg hiN]
      calc
        _ ≤ (w i*ρ^(i+2))*cρ i :=
          mul_le_mul_of_nonneg_right (hfloor i hNi) (hcρ i)
        _=w i*c i := by dsimp only [cρ]; field_simp [hρne] <;> ring
  have hpref : spend v cρ N=spend w c N := by
    unfold spend
    apply Finset.sum_congr rfl
    intro i hi
    have hiN : i<N := Finset.mem_range.mp hi
    change (if i<N then w i*ρ^(i+2) else τ)*(c i/ρ^(i+2))=w i*c i
    rw [if_pos hiN]
    field_simp [hρne] <;> ring
  have ht (i : ℕ) (hi : N ≤ i) : v i=τ := by
    exact if_neg (by omega)
  have henvρ : ∀ q : ℝ,1 < q → ∃ M : ℝ,∀ i,Zρ i ≤ M*q^i := by
    intro q hq
    have hρq : 1 < ρ*q := by nlinarith
    obtain ⟨M,hM⟩ := henv (ρ*q) hρq
    refine ⟨M,fun i=>?_⟩
    have hh := div_le_div_of_nonneg_right (hM i) (pow_nonneg hρ0.le i)
    change Z i/ρ^i ≤ M*q^i
    convert hh using 1
    rw [mul_pow]
    field_simp [hρne] <;> ring
  have hh := tail_payment Zρ cρ v N hτ hZρ hcρ hzeroρ hrecρ ht hbudgetρ henvρ
  rw [hpref] at hh
  change (Z (N+1)/ρ^(N+1))*
    max 0 (τ*((Z (N+1)/ρ^(N+1))/(Z N/ρ^N)-1)) ≤ C-spend w c N at hh
  rw [rescaled_ratio (Z N) (Z (N+1)) ρ N hρne,
    terminal_scaling (Z (N+1)) (Z (N+1)/Z N) τ ρ N hρ0] at hh
  exact hh

end KLSConstantImprovement.GeometricWeightedTailPayment
#print axioms KLSConstantImprovement.GeometricWeightedTailPayment.rescaled_recurrence_identity
#print axioms KLSConstantImprovement.GeometricWeightedTailPayment.terminal_scaling
#print axioms KLSConstantImprovement.GeometricWeightedTailPayment.geometric_tail_payment
