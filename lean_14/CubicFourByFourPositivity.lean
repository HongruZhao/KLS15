import Mathlib

/-! A fraction-free Sylvester certificate for real symmetric 4-by-4
quadratic forms, and a closed-interval continuity lemma. The subsequent
two-cone proof supplies every principal minor by explicit polynomial
identities. -/
noncomputable section
namespace KLSImprovement.CubicFourByFour
set_option maxHeartbeats 5000000

def minorTwo (a b d : ℝ) : ℝ := a*b-d^2

def minorThree (a b c d e h : ℝ) : ℝ :=
  a*b*c-a*h^2-b*e^2-c*d^2+2*d*e*h

def minorFour (a b c k d e f h i j : ℝ) : ℝ :=
  a*b*c*k-a*b*j^2-a*c*i^2-a*k*h^2+2*a*h*i*j-
  b*c*f^2-b*k*e^2+2*b*e*f*j-c*k*d^2+2*c*d*f*i+
  2*k*d*e*h+d^2*j^2+e^2*i^2+f^2*h^2-
  2*d*e*i*j-2*d*f*h*j-2*e*f*h*i

def quadratic (a b c k d e f h i j x y z w : ℝ) : ℝ :=
  a*x^2+b*y^2+c*z^2+k*w^2+
  2*(d*x*y+e*x*z+f*x*w+h*y*z+i*y*w+j*z*w)

theorem fraction_free_squares (a b c k d e f h i j x y z w : ℝ) :
    a*minorTwo a b d*minorThree a b c d e h*
        quadratic a b c k d e f h i j x y z w =
      minorTwo a b d*minorThree a b c d e h*(a*x+d*y+e*z+f*w)^2+
      minorThree a b c d e h*
        (minorTwo a b d*y+(a*h-d*e)*z+(a*i-d*f)*w)^2+
      a*(minorThree a b c d e h*z+
        (minorTwo a b d*j-(a*h-d*e)*i-(b*e-d*h)*f)*w)^2+
      a*minorTwo a b d*minorFour a b c k d e f h i j*w^2 := by
  unfold minorTwo minorThree minorFour quadratic
  ring

theorem quadratic_nonneg_of_leading_minors
    (a b c k d e f h i j x y z w : ℝ)
    (h1 : 0 < a) (h2 : 0 < minorTwo a b d)
    (h3 : 0 < minorThree a b c d e h)
    (h4 : 0 ≤ minorFour a b c k d e f h i j) :
    0≤quadratic a b c k d e f h i j x y z w := by
  have hs := fraction_free_squares a b c k d e f h i j x y z w
  have hsum : 0≤
      minorTwo a b d*minorThree a b c d e h*(a*x+d*y+e*z+f*w)^2+
      minorThree a b c d e h*
        (minorTwo a b d*y+(a*h-d*e)*z+(a*i-d*f)*w)^2+
      a*(minorThree a b c d e h*z+
        (minorTwo a b d*j-(a*h-d*e)*i-(b*e-d*h)*f)*w)^2+
      a*minorTwo a b d*minorFour a b c k d e f h i j*w^2 := by
    positivity
  rw [←hs] at hsum
  exact nonneg_of_mul_nonneg_right hsum (mul_pos (mul_pos h1 h2) h3)

theorem continuous_nonneg_on_Icc {f : ℝ→ℝ} {a b : ℝ}
    (hf : Continuous f) (hab : a<b)
    (h : ∀x∈Set.Ioo a b, 0≤f x) : ∀x∈Set.Icc a b, 0≤f x := by
  have hc : IsClosed {x | 0≤f x} := isClosed_le continuous_const hf
  have hs : closure (Set.Ioo a b) ⊆ {x | 0≤f x} := closure_minimal h hc
  rw [closure_Ioo hab.ne] at hs
  exact hs

end KLSImprovement.CubicFourByFour
#print axioms KLSImprovement.CubicFourByFour.fraction_free_squares
#print axioms KLSImprovement.CubicFourByFour.quadratic_nonneg_of_leading_minors
#print axioms KLSImprovement.CubicFourByFour.continuous_nonneg_on_Icc
