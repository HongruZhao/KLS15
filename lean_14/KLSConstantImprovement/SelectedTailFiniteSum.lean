import KLSConstantImprovement.SelectedInfiniteConstantTail

/-! A literal finite sum for the selected infinite constant-weight value.
All terms beyond a finite zero hit vanish.  This is a scalar formula. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.SelectedTailFiniteSum
open KLSConstantImprovement.ProperConstantTailRecursion
open KLSConstantImprovement.ConstantTailFiniteHitting
open KLSConstantImprovement.SelectedInfiniteConstantTail

def prefixProduct (f : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  ∏ i∈Finset.range n,(1+path f (i+1) x)

theorem path_add (f : ℝ → ℝ) (n m : ℕ) (x : ℝ) :
    path f (n+m) x=path f m (path f n x) := by
  induction n generalizing x with
  | zero => simp only [Nat.zero_add,path]
  | succ n ih =>
      rw [Nat.succ_add]
      change path f (n+m) (f x)=path f m (path f n (f x))
      exact ih (f x)

theorem path_zero (f : ℝ → ℝ) (hf0 : f 0=0) (n : ℕ) : path f n 0=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [path,hf0] using ih

theorem hit_at_every_node (f : ℝ → ℝ) (hf0 : f 0=0)
    (N : ℕ) (x : ℝ) (hhit : path f N x=0) (i : ℕ) :
    path f N (path f i x)=0 := by
  calc
    path f N (path f i x)=path f (i+N) x := (path_add f i N x).symm
    _=path f (N+i) x := by rw [Nat.add_comm i N]
    _=path f i (path f N x) := path_add f N i x
    _=0 := by rw [hhit,path_zero f hf0 i]

/-- The exact selected infinite horizon is an explicit finite sum of
squared excesses, with the products arising from the normalized orbit. -/
theorem selectedExcess_eq_sum (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    (hf0 : f 0=0) (N : ℕ) (x : ℝ) (hhit : path f N x=0) :
    selectedExcess f x=
      ∑ i∈Finset.range N,prefixProduct f x i*(path f (i+1) x)^2 := by
  have hP0 : prefixProduct f x 0=1 := by simp [prefixProduct]
  have hP (i : ℕ) : prefixProduct f x (i+1)=
      prefixProduct f x i*(1+path f (i+1) x) := by
    simp only [prefixProduct,Finset.prod_range_succ]
  have hE (i : ℕ) : selectedExcess f (path f i x)=
      (path f (i+1) x)^2+
        (1+path f (i+1) x)*selectedExcess f (path f (i+1) x) := by
    have hh := selectedExcess_bellman f hf hf0 N (path f i x)
      (hit_at_every_node f hf0 N x hhit i)
    rw [←path_succ f i x] at hh
    exact hh
  have hz : selectedExcess f 0=0 := by
    simpa only [excess] using selectedExcess_eq_at_hit f hf hf0 0 0 rfl
  have hh := finite_square_expansion (prefixProduct f x)
    (fun i=>path f i x) (fun i=>selectedExcess f (path f i x)) hP0 hP N
    (fun i _=>hE i)
  simpa only [path,hhit,hz,mul_zero,add_zero] using hh

theorem selectedValue_eq_sum (f : ℝ → ℝ) (hf : ∀ x,0 ≤ f x)
    (hf0 : f 0=0) (N : ℕ) (τ r : ℝ) (hhit : path f N (r-1)=0) :
    selectedValue f τ r=τ*((r-1)+
      ∑ i∈Finset.range N,prefixProduct f (r-1) i*(path f (i+1) (r-1))^2) := by
  unfold selectedValue
  rw [selectedExcess_eq_sum f hf hf0 N (r-1) hhit]

end KLSConstantImprovement.SelectedTailFiniteSum
#print axioms KLSConstantImprovement.SelectedTailFiniteSum.selectedExcess_eq_sum
#print axioms KLSConstantImprovement.SelectedTailFiniteSum.selectedValue_eq_sum
