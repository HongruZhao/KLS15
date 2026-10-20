import ExponentialMoments
import FiniteProductTensorization

/-! Integrability of every polynomial for the actual independent Exp(1)
product, derived from its scalar factorial moments. No log-concavity,
isotropy, coefficient bound or polynomial moment is assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.ProductPolynomial
open KLSImprovement.ExponentialMoments
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

abbrev product (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => expMeasure 1)

theorem integrable_monomial {n : ℕ} (s : Fin n → ℕ) :
    Integrable (fun y : Fin n → ℝ => ∏ i, y i ^ s i) (product n) :=
  Integrable.fintype_prod (fun i => (expMeasure_one_nat_moment (s i)).1)

theorem integral_monomial {n : ℕ} (s : Fin n → ℕ) :
    (∫ y : Fin n → ℝ, ∏ i, y i ^ s i ∂product n) =
      ∏ i, ((s i).factorial : ℝ) := by
  change (∫ y : Fin n → ℝ, ∏ i, y i ^ s i
    ∂Measure.pi (fun _ : Fin n => expMeasure 1)) = _
  rw [integral_fintype_prod_eq_prod (fun i (z : ℝ) => z ^ s i)]
  simp_rw [(expMeasure_one_nat_moment _).2]

theorem integrable_polynomial {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Integrable (fun y : Fin n → ℝ => MvPolynomial.eval y p) (product n) := by
  have he : (fun y : Fin n → ℝ => MvPolynomial.eval y p) =
      (fun y => ∑ s ∈ p.support, p.coeff s * ∏ i, y i ^ s i) := by
    funext y
    exact MvPolynomial.eval_eq' y p
  rw [he]
  exact integrable_finsetSum _ (fun s _ => (integrable_monomial s).const_mul (p.coeff s))

theorem memLp_polynomial {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    MemLp (fun y : Fin n → ℝ => MvPolynomial.eval y p) 2 (product n) := by
  apply (memLp_two_iff_integrable_sq
    (integrable_polynomial p).aestronglyMeasurable).mpr
  exact (integrable_polynomial (p^2)).congr
    (.of_forall (fun y => (MvPolynomial.eval y).map_pow p 2))

theorem integrable_polynomial_mul {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) :
    Integrable (fun y : Fin n → ℝ =>
      MvPolynomial.eval y p * MvPolynomial.eval y q) (product n) := by
  simpa only [MvPolynomial.eval_mul] using integrable_polynomial (p*q)

theorem integral_polynomial {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    (∫ y : Fin n → ℝ, MvPolynomial.eval y p ∂product n) =
      ∑ s ∈ p.support, p.coeff s * ∏ i, ((s i).factorial : ℝ) := by
  have he : (fun y : Fin n → ℝ => MvPolynomial.eval y p) =
      (fun y => ∑ s ∈ p.support, p.coeff s * ∏ i, y i ^ s i) := by
    funext y
    exact MvPolynomial.eval_eq' y p
  rw [he, integral_finsetSum _
    (fun (s : Fin n →₀ ℕ) _ => (integrable_monomial s).const_mul (p.coeff s))]
  simp_rw [integral_const_mul, integral_monomial]

end KLSImprovement.ProductPolynomial
#print axioms KLSImprovement.ProductPolynomial.integrable_polynomial
#print axioms KLSImprovement.ProductPolynomial.memLp_polynomial
#print axioms KLSImprovement.ProductPolynomial.integral_polynomial
