import Mathlib

/-! A finite three-leg step in Gram-gap rigidity. The completely positive
fixed-space input and positive one-leg Gram remain explicit. No original-law
or quantitative positive-gap payment is asserted here. -/

namespace KLSConstantImprovement.TensorGramGapLegClosure

variable {ι : Type*} [Fintype ι]

def firstLeg (A : ι → ι → ℝ) (T : ι → ι → ι → ℝ) (i j k : ι) : ℝ :=
  ∑ a, A i a * T a j k

def secondLeg (A : ι → ι → ℝ) (T : ι → ι → ι → ℝ) (i j k : ι) : ℝ :=
  ∑ a, A j a * T i a k

def thirdLeg (A : ι → ι → ℝ) (T : ι → ι → ι → ℝ) (i j k : ι) : ℝ :=
  ∑ a, A k a * T i j a

theorem three_leg_fixed_space_closure
    (T : ι → ι → ι → ℝ) (H K : ι → ι → ℝ)
    (hfirst : ∀ i j k, T i j k = T j i k)
    (hlast : ∀ i j k, T i j k = T i k j)
    (hcross : ∀ i j k, firstLeg H T i j k = secondLeg K T i j k) :
    ∀ i j k, firstLeg H T i j k = firstLeg K T i j k := by
  intro i j k
  have h13 : firstLeg H T i j k = thirdLeg K T i j k := by
    calc
      firstLeg H T i j k = firstLeg H T i k j := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hlast a j k]
      _ = secondLeg K T i k j := hcross i k j
      _ = thirdLeg K T i j k := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hlast i a j]
  have h21 : secondLeg H T i j k = firstLeg K T i j k := by
    calc
      secondLeg H T i j k = firstLeg H T j i k := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfirst i a k]
      _ = secondLeg K T j i k := hcross j i k
      _ = firstLeg K T i j k := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfirst j a k]
  have h23 : secondLeg H T i j k = thirdLeg K T i j k := by
    calc
      secondLeg H T i j k = firstLeg H T j k i := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfirst i a k, hlast a i k]
      _ = secondLeg K T j k i := hcross j k i
      _ = thirdLeg K T i j k := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hlast j a i, hfirst j i a]
  exact h13.trans (h23.symm.trans h21)

theorem first_leg_difference_zero
    (T : ι → ι → ι → ℝ) (H K : ι → ι → ℝ)
    (hfirst : ∀ i j k, T i j k = T j i k)
    (hlast : ∀ i j k, T i j k = T i k j)
    (hcross : ∀ i j k, firstLeg H T i j k = secondLeg K T i j k) :
    ∀ i j k, ∑ a, (H i a - K i a) * T a j k = 0 := by
  intro i j k
  simp only [sub_mul, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr (three_leg_fixed_space_closure T H K hfirst hlast hcross i j k)

theorem full_support_matrix_eq
    (T : ι → ι → ι → ℝ) (H K : ι → ι → ℝ)
    (hfirst : ∀ i j k, T i j k = T j i k)
    (hlast : ∀ i j k, T i j k = T i k j)
    (hcross : ∀ i j k, firstLeg H T i j k = secondLeg K T i j k)
    (hflatten : ∀ r : ι → ℝ,
      (∀ j k, ∑ a, r a * T a j k = 0) → ∀ i, r i = 0) :
    H = K := by
  funext i j
  exact sub_eq_zero.mp (hflatten (fun a => H i a - K i a)
    (first_leg_difference_zero T H K hfirst hlast hcross i) j)

#print axioms KLSConstantImprovement.TensorGramGapLegClosure.three_leg_fixed_space_closure
#print axioms KLSConstantImprovement.TensorGramGapLegClosure.first_leg_difference_zero
#print axioms KLSConstantImprovement.TensorGramGapLegClosure.full_support_matrix_eq

end KLSConstantImprovement.TensorGramGapLegClosure
