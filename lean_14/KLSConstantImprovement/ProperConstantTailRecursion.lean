import Mathlib

/-! Generic algebra/order theory for a proper constant-weight Bellman tail.
The finite-horizon terminal line is tau*x, not zero. These are scalar
lemmas; they do not assert a numerical Poincare endpoint. -/
noncomputable section
namespace KLSConstantImprovement.ProperConstantTailRecursion

def excess (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0,_ => 0
  | n+1,x => (f x)^2+(1+f x)*excess f n (f x)

def path (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0,x => x
  | n+1,x => path f n (f x)

def value (f : ℝ → ℝ) (τ : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  τ*((r-1)+excess f n (r-1))

def greedyCost (f : ℝ → ℝ) (τ : ℝ) : ℕ → ℝ → ℝ
  | 0,x => τ*x
  | n+1,x => τ*(x-f x)+(1+f x)*greedyCost f τ n (f x)

theorem excess_nonneg (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    (n : ℕ) (x : ℝ) : 0 ≤ excess f n x := by
  induction n generalizing x with
  | zero => simp [excess]
  | succ n ih =>
      exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith [hf x]) (ih _))

theorem excess_mono (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    (hm : Monotone f) (n : ℕ) : Monotone (excess f n) := by
  induction n with
  | zero => intro a b hab; simp [excess]
  | succ n ih =>
      intro a b hab
      change (f a)^2+(1+f a)*excess f n (f a) ≤
        (f b)^2+(1+f b)*excess f n (f b)
      have hfAB : f a ≤ f b := hm hab
      have hsq : (f a)^2 ≤ (f b)^2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hfAB)
          (add_nonneg (hf a) (hf b))]
      have hprod := mul_le_mul (by linarith : 1+f a ≤ 1+f b)
        (ih hfAB) (excess_nonneg f hf n (f a)) (by linarith [hf b])
      exact add_le_add hsq hprod

theorem excess_le_succ (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    (n : ℕ) (x : ℝ) : excess f n x ≤ excess f (n+1) x := by
  induction n generalizing x with
  | zero => exact excess_nonneg f hf 1 x
  | succ n ih =>
      change (f x)^2+(1+f x)*excess f n (f x) ≤
        (f x)^2+(1+f x)*excess f (n+1) (f x)
      have hh := mul_le_mul_of_nonneg_left (ih (f x))
        (show 0 ≤ 1+f x by linarith [hf x])
      exact add_le_add (le_refl ((f x)^2)) hh

/-- The least feasible successor realizes the full finite-horizon minimum.
This follows from order, without assuming a differentiable minimizer. -/
theorem greedy_minimum (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    (hm : Monotone f) (n : ℕ) (x z : ℝ) (hz : f x ≤ z) :
    excess f (n+1) x ≤ z^2+(1+z)*excess f n z := by
  have hz0 : 0 ≤ z := (hf x).trans hz
  have hsq : (f x)^2 ≤ z^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz) (add_nonneg (hf x) hz0)]
  have hprod := mul_le_mul (by linarith : 1+f x ≤ 1+z)
    (excess_mono f hf hm n hz) (excess_nonneg f hf n (f x)) (by linarith)
  exact add_le_add hsq hprod

/-- The Bellman inequality includes next ratios above the current one.
The exact-cap or chord lower constraint supplies the final hypothesis. -/
theorem value_stage (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    (hm : Monotone f) {τ r s : ℝ} (hτ : 0 ≤ τ)
    (n : ℕ) (hnext : f (r-1) ≤ s-1) :
    value f τ (n+1) r ≤ τ*(r-s)+s*value f τ n s := by
  have hh := mul_le_mul_of_nonneg_left
    (greedy_minimum f hf hm n (r-1) (s-1) hnext) hτ
  dsimp only [value]
  nlinarith only [hh]

theorem excess_at_zero (f : ℝ → ℝ) (hf0 : f 0=0) (n : ℕ) :
    excess f n 0=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [excess,hf0,ih]

/-- Once the greedy path reaches zero, the properly initialized finite
horizons stabilize exactly. The selected infinite value is then finite. -/
theorem excess_stabilizes (f : ℝ → ℝ) (hf0 : f 0=0)
    (n m : ℕ) (x : ℝ) (hhit : path f n x=0) :
    excess f (n+m) x=excess f n x := by
  induction n generalizing x with
  | zero =>
      have hx : x=0 := hhit
      subst x
      simp [excess,excess_at_zero f hf0]
  | succ n ih =>
      have hh : path f n (f x)=0 := hhit
      rw [Nat.succ_add]
      change (f x)^2+(1+f x)*excess f (n+m) (f x)=
        (f x)^2+(1+f x)*excess f n (f x)
      rw [ih (f x) hh]

/-- The greedy path is an exact scalar witness for each finite horizon,
including its positive terminal line. -/
theorem greedyCost_eq_value (f : ℝ → ℝ) (τ : ℝ) (n : ℕ) (x : ℝ) :
    greedyCost f τ n x=τ*(x+excess f n x) := by
  induction n generalizing x with
  | zero => simp [greedyCost,excess]
  | succ n ih =>
      simp only [greedyCost,excess,ih]
      ring

end KLSConstantImprovement.ProperConstantTailRecursion
#print axioms KLSConstantImprovement.ProperConstantTailRecursion.excess_nonneg
#print axioms KLSConstantImprovement.ProperConstantTailRecursion.excess_mono
#print axioms KLSConstantImprovement.ProperConstantTailRecursion.excess_le_succ
#print axioms KLSConstantImprovement.ProperConstantTailRecursion.greedy_minimum
#print axioms KLSConstantImprovement.ProperConstantTailRecursion.value_stage
#print axioms KLSConstantImprovement.ProperConstantTailRecursion.excess_stabilizes
#print axioms KLSConstantImprovement.ProperConstantTailRecursion.greedyCost_eq_value
