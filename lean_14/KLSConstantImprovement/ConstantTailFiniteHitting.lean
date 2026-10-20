import KLSConstantImprovement.ProperConstantTailRecursion

/-! A finite, explicit meaning for the selected infinite constant tail.
The drift estimate applies to both the true quadratic cap and its chord.
This file is scalar-only and asserts no new numerical KLS endpoint. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.ConstantTailFiniteHitting
open KLSConstantImprovement.ProperConstantTailRecursion

def exactStep (A x : ℝ) : ℝ :=
  max 0 (max 0 x-A/(1+max 0 x))

def chordStep (A R x : ℝ) : ℝ := max 0 ((1+A/R)*x-A)

theorem path_succ (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    path f (n+1) x=f (path f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      change path f (n+1) (f x)=f (path f n (f x))
      exact ih (f x)

theorem path_nonneg (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ path f n x := by
  cases n with
  | zero => exact hx
  | succ n => rw [path_succ]; exact hf _

theorem max_zero_sub (u δ : ℝ) (hδ : 0 ≤ δ) :
    max 0 (max 0 u-δ)=max 0 (u-δ) := by
  by_cases hu : 0 ≤ u
  · rw [max_eq_right hu]
  · have hu' : u ≤ 0 := (lt_of_not_ge hu).le
    rw [max_eq_left hu',max_eq_left (by linarith : 0-δ ≤ 0),
      max_eq_left (by linarith : u-δ ≤ 0)]

/-- Uniform positive drift proves finite hitting without a limiting
argument. The hypotheses include x=0, hence also encode absorption. -/
theorem path_le_truncation (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    {B δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hxB : x ≤ B)
    (hdrift : ∀ y,0 ≤ y → y ≤ B → f y ≤ max 0 (y-δ))
    (n : ℕ) : path f n x ≤ max 0 (x-(n : ℝ)*δ) := by
  induction n with
  | zero => simpa only [Nat.cast_zero,zero_mul,sub_zero,path] using le_max_right 0 x
  | succ n ih =>
      have hnδ : 0 ≤ (n : ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ
      have hp0 : 0 ≤ path f n x := path_nonneg f hf hx n
      have hpx : path f n x ≤ x := ih.trans (max_le hx (by linarith))
      have hpB : path f n x ≤ B := hpx.trans hxB
      rw [path_succ]
      calc
        f (path f n x) ≤ max 0 (path f n x-δ) := hdrift _ hp0 hpB
        _ ≤ max 0 (max 0 (x-(n : ℝ)*δ)-δ) :=
          max_le_max_left 0 (sub_le_sub_right ih δ)
        _ = max 0 (x-((n+1 : ℕ) : ℝ)*δ) := by
          rw [max_zero_sub _ _ hδ]
          congr 1
          push_cast
          ring

theorem path_eq_zero_of_drift (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    {B δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hxB : x ≤ B)
    (hdrift : ∀ y,0 ≤ y → y ≤ B → f y ≤ max 0 (y-δ))
    (n : ℕ) (hcount : B ≤ (n : ℝ)*δ) : path f n x=0 := by
  have hp := path_le_truncation f hf hδ hx hxB hdrift n
  rw [max_eq_left (by linarith : x-(n : ℝ)*δ ≤ 0)] at hp
  exact le_antisymm hp (path_nonneg f hf hx n)

theorem exactStep_nonneg (A x : ℝ) : 0 ≤ exactStep A x := le_max_left _ _

theorem exactStep_zero {A : ℝ} (hA : 0 ≤ A) : exactStep A 0=0 := by
  simp only [exactStep,max_self,add_zero,div_one,zero_sub]
  exact max_eq_left (by linarith)

theorem exactStep_mono {A : ℝ} (hA : 0 ≤ A) : Monotone (exactStep A) := by
  intro x y hxy
  have hxy' : max 0 x ≤ max 0 y := max_le_max_left 0 hxy
  have hx0 : 0 ≤ max 0 x := le_max_left _ _
  have hy0 : 0 ≤ max 0 y := le_max_left _ _
  have hdiv : A/(1+max 0 y) ≤ A/(1+max 0 x) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hxy')]
  unfold exactStep
  exact max_le_max_left 0 (by linarith)

theorem exactStep_drift {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    {x : ℝ} (hx : 0 ≤ x) (hxR : x ≤ R-1) :
    exactStep A x ≤ max 0 (x-A/R) := by
  have hdiv : A/R ≤ A/(1+x) := by
    apply (div_le_div_iff₀ hR (by linarith)).mpr
    nlinarith [mul_nonneg hA (by linarith : 0 ≤ R-(1+x))]
  unfold exactStep
  rw [max_eq_right hx]
  exact max_le_max_left 0 (by linarith)

theorem exactStep_hits {A R x : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hx : 0 ≤ x) (hxR : x ≤ R-1) (n : ℕ)
    (hcount : R-1 ≤ (n : ℝ)*(A/R)) : path (exactStep A) n x=0 := by
  exact path_eq_zero_of_drift (exactStep A) (exactStep_nonneg A)
    (div_nonneg hA hR.le) hx hxR
    (fun y hy hyR => exactStep_drift hA hR hy hyR) n hcount

theorem chordStep_nonneg (A R x : ℝ) : 0 ≤ chordStep A R x := le_max_left _ _

theorem chordStep_zero {A R : ℝ} (hA : 0 ≤ A) : chordStep A R 0=0 := by
  unfold chordStep
  rw [mul_zero,zero_sub,max_eq_left (by linarith : -A ≤ 0)]

theorem chordStep_mono {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R) :
    Monotone (chordStep A R) := by
  intro x y hxy
  unfold chordStep
  exact max_le_max_left 0 (sub_le_sub_right
    (mul_le_mul_of_nonneg_left hxy (by positivity)) A)

theorem chordStep_drift {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    {x : ℝ} (hx : 0 ≤ x) (hxR : x ≤ R-1) :
    chordStep A R x ≤ max 0 (x-A/R) := by
  have he : (1+A/R)*x-A=x-A/R+(A/R)*(x+1-R) := by
    field_simp [ne_of_gt hR]
    ring
  have hh : (A/R)*(x+1-R) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_nonneg hA hR.le) (by linarith)
  unfold chordStep
  exact max_le_max_left 0 (by rw [he]; linarith)

theorem chordStep_hits {A R x : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hx : 0 ≤ x) (hxR : x ≤ R-1) (n : ℕ)
    (hcount : R-1 ≤ (n : ℝ)*(A/R)) : path (chordStep A R) n x=0 := by
  exact path_eq_zero_of_drift (chordStep A R) (chordStep_nonneg A R)
    (div_nonneg hA hR.le) hx hxR
    (fun y hy hyR => chordStep_drift hA hR hy hyR) n hcount

/-- Explicit squared-excess expansion by finite telescoping. When the
terminal excess is zero this is the finite-sum infinite-tail formula. -/
theorem finite_square_expansion (P x E : ℕ → ℝ) (hP0 : P 0=1)
    (hP : ∀ i,P (i+1)=P i*(1+x (i+1))) (N : ℕ)
    (hE : ∀ i,i<N → E i=x (i+1)^2+(1+x (i+1))*E (i+1)) :
    E 0=(∑ i∈Finset.range N,P i*x (i+1)^2)+P N*E N := by
  induction N with
  | zero => simp [hP0]
  | succ N ih =>
      have hh := ih (fun i hi => hE i (by omega))
      have hl := hE N (by omega)
      rw [hl] at hh
      rw [Finset.sum_range_succ,hP N]
      nlinarith only [hh]

end KLSConstantImprovement.ConstantTailFiniteHitting
#print axioms KLSConstantImprovement.ConstantTailFiniteHitting.path_eq_zero_of_drift
#print axioms KLSConstantImprovement.ConstantTailFiniteHitting.exactStep_mono
#print axioms KLSConstantImprovement.ConstantTailFiniteHitting.exactStep_hits
#print axioms KLSConstantImprovement.ConstantTailFiniteHitting.chordStep_hits
#print axioms KLSConstantImprovement.ConstantTailFiniteHitting.finite_square_expansion
