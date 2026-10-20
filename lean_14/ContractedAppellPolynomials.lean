import ActualAppellSpatialRecursion
import SymmetricTupleContraction

/-! Actual tensor contractions of Appell polynomials, their L² adjoint
identification, and the exact spatial derivative multiplicity. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def contractedAppellPolynomial (hμ : admissibleMeasure μ) (d : ℕ)
    (t : (Fin d → Fin n) → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ a, t a • actualBasisAppellPolynomial hμ d a

theorem contractedAppellPolynomial_eval (hμ : admissibleMeasure μ) (d : ℕ)
    (t : (Fin d → Fin n) → ℝ) (x : Space n) :
    polynomialEval (contractedAppellPolynomial hμ d t) x =
      ∑ a, t a*polynomialEval (actualBasisAppellPolynomial hμ d a) x := by
  change (MvPolynomial.eval (fun j => x j))
    (∑ a, t a • actualBasisAppellPolynomial hμ d a)=_
  rw [MvPolynomial.eval_sum]
  simp only [MvPolynomial.smul_eval]
  rfl

theorem contractedAppellPolynomial_pairing (hμ : admissibleMeasure μ) (d : ℕ)
    (t : (Fin d → Fin n) → ℝ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, polynomialEval (contractedAppellPolynomial hμ d t) x*f x ∂μ) =
      ∑ a, t a*actualAppellCoefficient μ f d a := by
  have hi (a : Fin d → Fin n) : Integrable (fun x =>
      t a*(polynomialEval (actualBasisAppellPolynomial hμ d a) x*f x)) μ := by
    exact ((polynomialEval_memLp_two hμ.logConcave _).integrable_mul hf).const_mul (t a)
  simp_rw [contractedAppellPolynomial_eval,Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum Finset.univ (fun a _ => hi a)]
  simp_rw [integral_const_mul,actualBasisAppellPolynomial_pairing hμ d _ hf]

theorem contractedAppellPolynomial_toLp (hμ : admissibleMeasure μ) (d : ℕ)
    (t : (Fin d → Fin n) → ℝ) :
    polynomialLp hμ.logConcave (contractedAppellPolynomial hμ d t) =
      actualAppellPolynomialLp hμ d (WithLp.toLp 2 t) := by
  apply ext_inner_right ℝ
  intro f
  rw [inner_polynomialLp_eq_integral,actualAppellPolynomialLp_pairing,
    contractedAppellPolynomial_pairing hμ d t (Lp.memLp f)]
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [RCLike.inner_apply,conj_trivial]
  exact mul_comm _ _

theorem contractedAppellPolynomial_norm_le (hμ : admissibleMeasure μ) (d : ℕ)
    (t : (Fin d → Fin n) → ℝ) :
    ‖polynomialLp hμ.logConcave (contractedAppellPolynomial hμ d t)‖ ≤
      ‖actualAppellObservation hμ d‖*‖(WithLp.toLp 2 t : EuclideanSpace ℝ (Fin d → Fin n))‖ := by
  rw [contractedAppellPolynomial_toLp]
  exact ((actualAppellObservation hμ d).adjoint.le_opNorm _).trans_eq
    (by rw [ContinuousLinearMap.adjoint.norm_map])

theorem contractedAppellPolynomial_integral_zero (hμ : admissibleMeasure μ)
    {d : ℕ} (hd : d ≠ 0) (t : (Fin d → Fin n) → ℝ) :
    (∫ x, polynomialEval (contractedAppellPolynomial hμ d t) x ∂μ)=0 := by
  have hp := contractedAppellPolynomial_pairing hμ d t
    (memLp_const (μ := μ) (p := 2) (1 : ℝ))
  simpa only [mul_one,actualAppellCoefficient_const_fullClass hμ.logConcave 1 hd,
    mul_zero,Finset.sum_const_zero] using hp

theorem contractedAppellPolynomial_spatial_derivative {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hμ : admissibleMeasure (potentialMeasure φ)) (d : ℕ)
    (t : (Fin (d+1) → Fin n) → ℝ)
    (hs : ∀ a b, List.Perm (List.ofFn a) (List.ofFn b) → t a=t b)
    (j : Fin n) (x : Space n) :
    coordinateDerivative (polynomialEval (contractedAppellPolynomial hμ (d+1) t)) j x =
      (d+1 : ℕ)*polynomialEval (contractedAppellPolynomial hμ d (fun b => t (Fin.cons j b))) x := by
  have he : polynomialEval (contractedAppellPolynomial hμ (d+1) t) =
      fun y => ∑ a, t a*polynomialEval (actualBasisAppellPolynomial hμ (d+1) a) y :=
    funext (contractedAppellPolynomial_eval hμ (d+1) t)
  have hd (a : Fin (d+1) → Fin n) : DifferentiableAt ℝ
      (fun y => t a*polynomialEval (actualBasisAppellPolynomial hμ (d+1) a) y) x :=
    ((polynomialEval_contDiff _).differentiable (by simp) x).const_mul (t a)
  rw [he,coordinateDerivative_sum hd]
  have hmul (a : Fin (d+1) → Fin n) :
      coordinateDerivative (fun y => t a*polynomialEval (actualBasisAppellPolynomial hμ (d+1) a) y) j x =
      t a*coordinateDerivative (polynomialEval (actualBasisAppellPolynomial hμ (d+1) a)) j x := by
    unfold coordinateDerivative
    have hf : HasFDerivAt (polynomialEval (actualBasisAppellPolynomial hμ (d+1) a))
        (fderiv ℝ (polynomialEval (actualBasisAppellPolynomial hμ (d+1) a)) x) x :=
      ((polynomialEval_contDiff _).differentiable (by simp) x).hasFDerivAt
    have he := congrArg (fun L : Space n →L[ℝ] ℝ => L (EuclideanSpace.single j 1))
      (hf.const_mul (t a)).fderiv
    simpa only [ContinuousLinearMap.smul_apply,smul_eq_mul] using he
  simp_rw [hmul,actualBasisAppellPolynomial_spatial_recursion hφ hκ hlower hμ]
  rw [contractedAppellPolynomial_eval]
  exact symmetric_tuple_erased_contraction t hs
    (fun b => polynomialEval (actualBasisAppellPolynomial hμ d b) x) j

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.contractedAppellPolynomial_toLp
#print axioms KLS.DeterministicBridgeNext.contractedAppellPolynomial_norm_le
#print axioms KLS.DeterministicBridgeNext.contractedAppellPolynomial_spatial_derivative
