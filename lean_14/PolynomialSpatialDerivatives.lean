import ActualAppellObservationOperators
import KLS.WeightedDiffusionCommutator
import KLS.WeightedDiffusionLinear
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Analytic.CPolynomialDef

/-! Actual spatial derivatives of the finite polynomial representatives. -/
noncomputable section
open MeasureTheory InnerProductSpace Set
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem polynomialEval_C (c : ℝ) : polynomialEval (MvPolynomial.C c : MvPolynomial (Fin n) ℝ) =
    fun _ => c := by
  funext x
  change (MvPolynomial.eval (fun j => x j)) (MvPolynomial.C c)=c
  simp only [MvPolynomial.eval_C]

theorem polynomialEval_add (p q : MvPolynomial (Fin n) ℝ) :
    polynomialEval (p+q)=fun x => polynomialEval p x+polynomialEval q x := by
  funext x
  change (MvPolynomial.eval (fun j => x j)) (p+q)=
    (MvPolynomial.eval (fun j => x j)) p+(MvPolynomial.eval (fun j => x j)) q
  exact MvPolynomial.eval_add

theorem polynomialEval_mul (p q : MvPolynomial (Fin n) ℝ) :
    polynomialEval (p*q)=fun x => polynomialEval p x*polynomialEval q x := by
  funext x
  change (MvPolynomial.eval (fun j => x j)) (p*q)=
    (MvPolynomial.eval (fun j => x j)) p*(MvPolynomial.eval (fun j => x j)) q
  exact MvPolynomial.eval_mul

theorem polynomialEval_X (i : Fin n) :
    polynomialEval (MvPolynomial.X i : MvPolynomial (Fin n) ℝ) = fun x => x i := by
  funext x
  change (MvPolynomial.eval (fun j => x j)) (MvPolynomial.X i)=x i
  simp only [MvPolynomial.eval_X]

theorem polynomialEval_contDiff (p : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (polynomialEval p) := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [polynomialEval_C]; exact contDiff_const
  | add p q hp hq =>
      rw [polynomialEval_add]; exact hp.add hq
  | mul_X p j hp =>
      rw [polynomialEval_mul,polynomialEval_X]
      exact hp.mul (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff

theorem coordinateDerivative_polynomialEval (p : MvPolynomial (Fin n) ℝ)
    (j : Fin n) (x : Space n) :
    coordinateDerivative (polynomialEval p) j x =
      polynomialEval (MvPolynomial.pderiv j p) x := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [polynomialEval_C]; simp [coordinateDerivative,MvPolynomial.pderiv_C,polynomialEval]
  | add p q hp hq =>
      rw [polynomialEval_add]
      change coordinateDerivative (polynomialEval p+polynomialEval q) j x=_
      rw [coordinateDerivative_add
        ((polynomialEval_contDiff p).differentiable (by simp) x)
        ((polynomialEval_contDiff q).differentiable (by simp) x),hp,hq]
      rw [map_add,polynomialEval_add]
  | mul_X p i hp =>
      have hx : DifferentiableAt ℝ (fun y : Space n => y i) x :=
        (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt
      rw [polynomialEval_mul,polynomialEval_X,coordinateDerivative_mul
        ((polynomialEval_contDiff p).differentiable (by simp) x) hx,hp]
      have hd : coordinateDerivative (fun y : Space n => y i) j x =
          if i=j then 1 else 0 := by
        change fderiv ℝ (EuclideanSpace.proj (𝕜 := ℝ) i) x (EuclideanSpace.single j 1)=_
        rw [ContinuousLinearMap.fderiv]
        change (EuclideanSpace.single j (1 : ℝ)) i = _
        simp [PiLp.single_apply]
      rw [hd]
      rw [MvPolynomial.pderiv_mul,polynomialEval_add,polynomialEval_mul,
        polynomialEval_mul,polynomialEval_X,MvPolynomial.pderiv_X]
      simp [polynomialEval,Pi.single_apply,eq_comm]

theorem memLp_coordinateDerivative_polynomialEval {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (p : MvPolynomial (Fin n) ℝ) (j : Fin n) :
    MemLp (coordinateDerivative (polynomialEval p) j) 2 μ := by
  have he : coordinateDerivative (polynomialEval p) j =
      polynomialEval (MvPolynomial.pderiv j p) := funext (coordinateDerivative_polynomialEval p j)
  rw [he]
  exact polynomialEval_memLp_two hLC _

theorem exists_actualAppellPolynomial_representative {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (d : ℕ)
    (T : EuclideanSpace ℝ (Fin d → Fin n)) :
    ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧
      polynomialLp hμ.logConcave p = actualAppellPolynomialLp hμ d T := by
  obtain ⟨c,hc⟩ := actualAppellPolynomialLp_mem hμ d T
  refine ⟨boundedDegreePolynomial c,boundedDegreePolynomial_totalDegree_le c,?_⟩
  exact (polynomialCoefficientLp_eq hμ.logConcave (degreeExponent n d) c).symm.trans hc

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.polynomialEval_contDiff
#print axioms KLS.DeterministicBridgeNext.coordinateDerivative_polynomialEval
#print axioms KLS.DeterministicBridgeNext.memLp_coordinateDerivative_polynomialEval
#print axioms KLS.DeterministicBridgeNext.exists_actualAppellPolynomial_representative
