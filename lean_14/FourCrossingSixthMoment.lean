import Mathlib

/-! A sixth-moment comparison from four matched moments and a density
crossing pattern. The crossing pattern is an explicit premise; this file
does not assert its existence for a general log-concave density. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace KLSImprovement.FourCrossing
set_option maxHeartbeats 2000000

def rootSum (r : Fin 4 → ℝ) : ℝ := r 0+r 1+r 2+r 3
def rootPairSum (r : Fin 4 → ℝ) : ℝ :=
  r 0*r 1+r 0*r 2+r 0*r 3+r 1*r 2+r 1*r 3+r 2*r 3
def rootTripleSum (r : Fin 4 → ℝ) : ℝ :=
  r 0*r 1*r 2+r 0*r 1*r 3+r 0*r 2*r 3+r 1*r 2*r 3
def rootProduct (r : Fin 4 → ℝ) : ℝ := r 0*r 1*r 2*r 3
def crossingPolynomial (r : Fin 4 → ℝ) (x : ℝ) : ℝ :=
  (x-r 0)*(x-r 1)*(x-r 2)*(x-r 3)
def nonnegativeQuotient (r : Fin 4 → ℝ) (x : ℝ) : ℝ :=
  x^2+rootSum r*x+(rootSum r)^2-rootPairSum r
def remainderCoefficients (r : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-rootProduct r*((rootSum r)^2-rootPairSum r),
    (rootSum r)^2*rootTripleSum r-rootPairSum r*rootTripleSum r-rootSum r*rootProduct r,
    -(rootSum r)^2*rootPairSum r+(rootPairSum r)^2+rootSum r*rootTripleSum r-rootProduct r,
    (rootSum r)^3-2*rootSum r*rootPairSum r+rootTripleSum r]
def cubicRemainder (r : Fin 4 → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin 4, remainderCoefficients r k*x^(k:ℕ)

theorem quotient_sum_of_squares (r : Fin 4 → ℝ) (x : ℝ) :
    nonnegativeQuotient r x = (x+rootSum r/2)^2+(rootSum r)^2/4+
      ((r 0)^2+(r 1)^2+(r 2)^2+(r 3)^2)/2 := by
  unfold nonnegativeQuotient rootSum rootPairSum
  ring

theorem quotient_nonneg (r : Fin 4 → ℝ) (x : ℝ) :
    0 ≤ nonnegativeQuotient r x := by
  rw [quotient_sum_of_squares]
  positivity

theorem sixth_power_division (r : Fin 4 → ℝ) (x : ℝ) :
    x^6 = crossingPolynomial r x*nonnegativeQuotient r x+cubicRemainder r x := by
  simp only [crossingPolynomial, nonnegativeQuotient, cubicRemainder,
    remainderCoefficients, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  norm_num
  unfold rootSum rootPairSum rootTripleSum rootProduct
  ring

theorem signed_remainder_integrable (μ : Measure ℝ) (h : ℝ → ℝ)
    (r : Fin 4 → ℝ)
    (hm : ∀ k ≤ 6, Integrable (fun x : ℝ => x^k*h x) μ) :
    Integrable (fun x => cubicRemainder r x*h x) μ := by
  have he : (fun x => cubicRemainder r x*h x) =
      (fun x => ∑ k : Fin 4, remainderCoefficients r k*(x^(k:ℕ)*h x)) := by
    funext x
    simp only [cubicRemainder, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  exact integrable_finsetSum _ (fun (k : Fin 4) _ =>
    (hm (k:ℕ) (by omega)).const_mul _)

theorem signed_remainder_integral_eq_zero (μ : Measure ℝ) (h : ℝ → ℝ)
    (r : Fin 4 → ℝ)
    (hm : ∀ k ≤ 6, Integrable (fun x : ℝ => x^k*h x) μ)
    (hzero : ∀ k ≤ 3, (∫ x, x^k*h x ∂μ) = 0) :
    (∫ x, cubicRemainder r x*h x ∂μ) = 0 := by
  have he : (fun x => cubicRemainder r x*h x) =
      (fun x => ∑ k : Fin 4, remainderCoefficients r k*(x^(k:ℕ)*h x)) := by
    funext x
    simp only [cubicRemainder, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he, integral_finsetSum _ (fun (k : Fin 4) _ =>
    (hm (k:ℕ) (by omega)).const_mul _)]
  apply Finset.sum_eq_zero
  intro k _
  rw [integral_const_mul, hzero k (by omega), mul_zero]

theorem signed_sixth_moment_nonpos_of_four_crossings
    (μ : Measure ℝ) (h : ℝ → ℝ) (r : Fin 4 → ℝ)
    (hm : ∀ k ≤ 6, Integrable (fun x : ℝ => x^k*h x) μ)
    (hzero : ∀ k ≤ 3, (∫ x, x^k*h x ∂μ) = 0)
    (hsign : ∀ᵐ x ∂μ, crossingPolynomial r x*h x ≤ 0) :
    (∫ x, x^6*h x ∂μ) ≤ 0 := by
  have hpoint : ∀ᵐ x ∂μ, x^6*h x ≤ cubicRemainder r x*h x := by
    filter_upwards [hsign] with x hx
    have hp := mul_nonpos_of_nonpos_of_nonneg hx (quotient_nonneg r x)
    rw [sixth_power_division r x]
    nlinarith only [hp]
  have hi := integral_mono_ae (hm 6 le_rfl) (signed_remainder_integrable μ h r hm) hpoint
  rw [signed_remainder_integral_eq_zero μ h r hm hzero] at hi
  exact hi

/-- The comparison applies to actual density moments; no interpretation as
an integral of an unspecified polynomial model is required. -/
theorem density_sixth_moment_le_of_four_crossings
    (μ : Measure ℝ) (f g : ℝ → ℝ) (r : Fin 4 → ℝ)
    (hf : ∀ k ≤ 6, Integrable (fun x : ℝ => x^k*f x) μ)
    (hg : ∀ k ≤ 6, Integrable (fun x : ℝ => x^k*g x) μ)
    (hmatched : ∀ k ≤ 3, (∫ x, x^k*f x ∂μ) = ∫ x, x^k*g x ∂μ)
    (hsign : ∀ᵐ x ∂μ, crossingPolynomial r x*(f x-g x) ≤ 0) :
    (∫ x, x^6*f x ∂μ) ≤ ∫ x, x^6*g x ∂μ := by
  have hi : ∀ k ≤ 6, Integrable (fun x : ℝ => x^k*(f x-g x)) μ := by
    intro k hk
    have he : (fun x : ℝ => x^k*(f x-g x)) =
        (fun x => x^k*f x-x^k*g x) := by funext x; ring
    rw [he]
    exact (hf k hk).sub (hg k hk)
  have hm : ∀ k ≤ 3, (∫ x, x^k*(f x-g x) ∂μ) = 0 := by
    intro k hk
    have he : (fun x : ℝ => x^k*(f x-g x)) =
        (fun x => x^k*f x-x^k*g x) := by funext x; ring
    rw [he, integral_sub (hf k (by omega)) (hg k (by omega)), hmatched k hk]
    ring
  have h := signed_sixth_moment_nonpos_of_four_crossings μ (fun x => f x-g x) r hi hm hsign
  have he : (fun x : ℝ => x^6*(f x-g x)) =
      (fun x => x^6*f x-x^6*g x) := by funext x; ring
  rw [he, integral_sub (hf 6 le_rfl) (hg 6 le_rfl)] at h
  linarith

end KLSImprovement.FourCrossing
#print axioms KLSImprovement.FourCrossing.quotient_nonneg
#print axioms KLSImprovement.FourCrossing.sixth_power_division
#print axioms KLSImprovement.FourCrossing.signed_sixth_moment_nonpos_of_four_crossings
#print axioms KLSImprovement.FourCrossing.density_sixth_moment_le_of_four_crossings
