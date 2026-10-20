import KLSConstantImprovement.SelectedInfiniteConstantTail
import KLSConstantImprovement.WeightedOrbitBellmanTail

/-! The selected nonlinear constant-tail value is paid by the ACTUAL
normalized orbit hypotheses. The proof starts from the accepted all-rate
tail theorem and iterates the exact quadratic-cap payment. No upper ratio
or previous operator bound is needed in this scalar endgame. -/
noncomputable section
namespace KLSConstantImprovement.NonlinearBellmanTailPayment
open KLSConstantImprovement.ProperConstantTailRecursion
open KLSConstantImprovement.ConstantTailFiniteHitting
open KLSConstantImprovement.SelectedInfiniteConstantTail
open KLSConstantImprovement.WeightedOrbitBellmanTail

def positiveValue (f : ℝ → ℝ) (τ : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  max 0 (value f τ n r)

def selectedPositiveValue (A τ r : ℝ) : ℝ :=
  max 0 (selectedValue (exactStep A) τ r)

theorem positiveValue_nonneg (f : ℝ → ℝ) (τ : ℝ) (n : ℕ) (r : ℝ) :
    0 ≤ positiveValue f τ n r := le_max_left _ _

theorem positiveValue_zero (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    (hm : Monotone f) (hf0 : f 0=0) {τ r : ℝ} (hτ : 0 ≤ τ)
    (n : ℕ) (hr : r ≤ 1) : positiveValue f τ n r=0 := by
  have he : excess f n (r-1)=0 := by
    have hh := excess_mono f hf hm n (show r-1 ≤ 0 by linarith)
    rw [excess_at_zero f hf0 n] at hh
    exact le_antisymm hh (excess_nonneg f hf n _)
  unfold positiveValue value
  rw [he,add_zero]
  exact max_eq_left (mul_nonpos_of_nonneg_of_nonpos hτ (by linarith))

/-- This nonlinear transition handles both rising next ratios and next
ratios at most one. Its final premise is exactly the lower cap constraint. -/
theorem positiveValue_step (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    (hm : Monotone f) (hf0 : f 0=0) {τ r s d : ℝ}
    (hτ : 0 ≤ τ) (hs : 0 ≤ s) (hd : 0 ≤ d) (hdrop : r-s ≤ d)
    (hbound : f (r-1) ≤ max 0 (s-1)) (n : ℕ) :
    positiveValue f τ (n+1) r ≤ τ*d+s*positiveValue f τ n s := by
  have hpay0 : 0 ≤ τ*d := mul_nonneg hτ hd
  have hnext0 : 0 ≤ s*positiveValue f τ n s :=
    mul_nonneg hs (positiveValue_nonneg _ _ _ _)
  by_cases hs1 : s ≤ 1
  · have hfx : f (r-1)=0 := by
      rw [max_eq_left (by linarith : s-1 ≤ 0)] at hbound
      exact le_antisymm hbound (hf _)
    have he : excess f (n+1) (r-1)=0 := by
      norm_num [excess,hfx,excess_at_zero f hf0 n]
    have hp : positiveValue f τ (n+1) r ≤ τ*d := by
      unfold positiveValue value
      rw [he,add_zero]
      exact max_le hpay0 (mul_le_mul_of_nonneg_left (by linarith) hτ)
    exact hp.trans (le_add_of_nonneg_right hnext0)
  · have hs1' : 1 ≤ s := (lt_of_not_ge hs1).le
    have hb : f (r-1) ≤ s-1 := by
      simpa only [max_eq_right (by linarith : 0 ≤ s-1)] using hbound
    have hstage := value_stage f hf hm hτ n hb
    have hmore : τ*(r-s)+s*value f τ n s ≤
        τ*d+s*positiveValue f τ n s := by
      exact add_le_add (mul_le_mul_of_nonneg_left hdrop hτ)
        (mul_le_mul_of_nonneg_left (le_max_right 0 _) hs)
    exact max_le (add_nonneg hpay0 hnext0) (hstage.trans hmore)

theorem exactStep_bound {A r s d : ℝ} (hr : 1 ≤ r)
    (hdrop : r-s ≤ d) (hcap : d ≤ A/r) :
    exactStep A (r-1) ≤ max 0 (s-1) := by
  unfold exactStep
  rw [max_eq_right (by linarith : 0 ≤ r-1),show 1+(r-1)=r by ring]
  exact max_le_max_left 0 (by linarith)

/-- Iterating any finite number of exact-cap steps remains paid by the
same constant-weight budget and the same all-rate tail theorem. -/
theorem finite_tail_payment (Z c w : ℕ → ℝ) {A C τ : ℝ}
    (hA : 0 ≤ A) (hτ : 0 < τ)
    (hZ : ∀ i,0 ≤ Z i) (hc : ∀ i,0 ≤ c i)
    (hzero : ∀ i,Z i=0 → Z (i+1)=0)
    (hrec : ∀ i,0 < Z i → 0 < Z (i+1) →
      Z (i+1)^2/Z i-c i ≤ Z (i+2))
    (hcap : ∀ i,c i ≤ A*Z i)
    (hbudget : ∀ j,spend w c j ≤ C)
    (henv : ∀ ρ : ℝ,1 < ρ → ∃ M : ℝ,∀ i,Z i ≤ M*ρ^i)
    (n N : ℕ) (ht : ∀ i,N ≤ i → w i=τ) :
    Z (N+1)*positiveValue (exactStep A) τ n (Z (N+1)/Z N) ≤
      C-spend w c N := by
  induction n generalizing N with
  | zero =>
      simpa only [positiveValue,value,excess,add_zero] using
        tail_payment Z c w N hτ hZ hc hzero hrec ht hbudget henv
  | succ n ih =>
      have hrem : 0 ≤ C-spend w c N := by linarith [hbudget N]
      by_cases hz0 : Z (N+1)=0
      · simp only [hz0,zero_mul]
        exact hrem
      have hz : 0 < Z (N+1) := lt_of_le_of_ne (hZ _) (Ne.symm hz0)
      have hZN : 0 < Z N := by
        by_contra hn
        have he : Z N=0 := le_antisymm (le_of_not_gt hn) (hZ N)
        exact hz0 (hzero N he)
      let r : ℝ := Z (N+1)/Z N
      let s : ℝ := Z (N+2)/Z (N+1)
      let d : ℝ := c N/Z (N+1)
      have hs : 0 ≤ s := div_nonneg (hZ _) hz.le
      have hd : 0 ≤ d := div_nonneg (hc _) hz.le
      by_cases hr1 : r ≤ 1
      · rw [positiveValue_zero (exactStep A) (exactStep_nonneg A)
          (exactStep_mono hA) (exactStep_zero hA) hτ.le (n+1) hr1,mul_zero]
        exact hrem
      have hr1' : 1 ≤ r := (lt_of_not_ge hr1).le
      have hdrop : r-s ≤ d := by
        have hh := div_le_div_of_nonneg_right (hrec N hZN hz) hz.le
        have he : (Z (N+1)^2/Z N-c N)/Z (N+1)=r-d := by
          dsimp only [r,d]
          field_simp [ne_of_gt hz,ne_of_gt hZN]
        rw [he] at hh
        change r-d ≤ s at hh
        linarith
      have hdcap : d ≤ A/r := by
        have hh := div_le_div_of_nonneg_right (hcap N) hz.le
        convert hh using 1 <;> dsimp only [r,d] <;>
          field_simp [ne_of_gt hz,ne_of_gt hZN] <;> ring
      have hh := mul_le_mul_of_nonneg_left
        (positiveValue_step (exactStep A) (exactStep_nonneg A)
          (exactStep_mono hA) (exactStep_zero hA) hτ.le hs hd hdrop
          (exactStep_bound hr1' hdrop hdcap) n) hz.le
      have hcd : Z (N+1)*d=c N := by
        dsimp only [d]
        field_simp
      have hzs : Z (N+1)*s=Z (N+2) := by
        dsimp only [s]
        field_simp
      have hstep : Z (N+1)*positiveValue (exactStep A) τ (n+1) r ≤
          τ*c N+Z (N+2)*positiveValue (exactStep A) τ n s := by
        calc
          _ ≤ Z (N+1)*(τ*d+s*positiveValue (exactStep A) τ n s) := hh
          _ = _ := by rw [mul_add,←mul_assoc, mul_comm (Z (N+1)) τ,
            mul_assoc, hcd,←mul_assoc,hzs]
      have ht' : ∀ i,N+1 ≤ i → w i=τ := fun i hi=>ht i (by omega)
      have htail := ih (N+1) ht'
      have hsp : spend w c (N+1)=spend w c N+τ*c N := by
        rw [spend_succ,ht N (le_refl _)]
      change Z (N+2)*positiveValue (exactStep A) τ n s ≤
        C-spend w c (N+1) at htail
      rw [hsp] at htail
      change Z (N+1)*positiveValue (exactStep A) τ (n+1) r ≤ _
      linarith

/-- Every real initial ratio has a finite greedy hit when A>0.  R is
chosen locally from that ratio, so no bootstrap cap enters this theorem. -/
theorem exactStep_has_hit {A : ℝ} (hA : 0 < A) (x : ℝ) :
    ∃ n : ℕ,path (exactStep A) n x=0 := by
  by_cases hx : x ≤ 0
  · refine ⟨1,?_⟩
    change exactStep A x=0
    unfold exactStep
    rw [max_eq_left hx]
    simp only [add_zero,div_one,zero_sub]
    exact max_eq_left (by linarith)
  · have hx0 : 0 ≤ x := (lt_of_not_ge hx).le
    have hR : 0 < x+1 := by linarith
    have hδ : 0 < A/(x+1) := div_pos hA hR
    obtain ⟨n,hn⟩ := exists_nat_ge (x/(A/(x+1)))
    have hc : x ≤ (n : ℝ)*(A/(x+1)) := (div_le_iff₀ hδ).mp hn
    exact ⟨n,exactStep_hits hA.le hR hx0 (by linarith) n (by linarith)⟩

/-- The literal selected infinite-horizon value is paid under precisely
the normalized actual-orbit hypotheses, including the all-rate envelope. -/
theorem selected_tail_payment (Z c w : ℕ → ℝ) {A C τ : ℝ}
    (hA : 0 < A) (hτ : 0 < τ)
    (hZ : ∀ i,0 ≤ Z i) (hc : ∀ i,0 ≤ c i)
    (hzero : ∀ i,Z i=0 → Z (i+1)=0)
    (hrec : ∀ i,0 < Z i → 0 < Z (i+1) →
      Z (i+1)^2/Z i-c i ≤ Z (i+2))
    (hcap : ∀ i,c i ≤ A*Z i)
    (hbudget : ∀ j,spend w c j ≤ C)
    (henv : ∀ ρ : ℝ,1 < ρ → ∃ M : ℝ,∀ i,Z i ≤ M*ρ^i)
    (N : ℕ) (ht : ∀ i,N ≤ i → w i=τ) :
    Z (N+1)*selectedPositiveValue A τ (Z (N+1)/Z N) ≤
      C-spend w c N := by
  obtain ⟨n,hn⟩ := exactStep_has_hit hA (Z (N+1)/Z N-1)
  have hh := finite_tail_payment Z c w hA.le hτ hZ hc hzero hrec hcap
    hbudget henv n N ht
  have he := selectedExcess_eq_at_hit (exactStep A) (exactStep_nonneg A)
    (exactStep_zero hA.le) n (Z (N+1)/Z N-1) hn
  unfold selectedPositiveValue selectedValue
  rw [he]
  exact hh

end KLSConstantImprovement.NonlinearBellmanTailPayment
#print axioms KLSConstantImprovement.NonlinearBellmanTailPayment.positiveValue_step
#print axioms KLSConstantImprovement.NonlinearBellmanTailPayment.finite_tail_payment
#print axioms KLSConstantImprovement.NonlinearBellmanTailPayment.exactStep_has_hit
#print axioms KLSConstantImprovement.NonlinearBellmanTailPayment.selected_tail_payment
