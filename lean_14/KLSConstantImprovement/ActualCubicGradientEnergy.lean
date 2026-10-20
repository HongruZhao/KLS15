import PolynomialSpatialDerivatives
import KLSConstantImprovement.ActualCubicRepresenter
import KLSConstantImprovement.LongPrefixCubicBellmanEndpoint

/-! The literal cubic Appell polynomial is an original locally Lipschitz L2
test. Its gradient is three times its vector of centered quadratic slices.
Every integrability and extended-to-real energy step is discharged on the
original measure; no regular potential or fixed-family assumption is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal ContDiff
namespace KLSConstantImprovement.ActualCubicGradientEnergy
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter
variable {n : ℕ}
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def tensorMvPolynomial (μ : Measure (Space n)) (T : Array3 (Fin n)) :
    MvPolynomial (Fin n) ℝ :=
  ∑ a, ∑ b, ∑ c, MvPolynomial.C (T a b c)*coordinateCubicPolynomial μ a b c

def centeredQuadratic (H : Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  matrixQuadratic H x-Matrix.trace H

theorem tensorMvPolynomial_eval (μ : Measure (Space n)) (T : Array3 (Fin n)) :
    polynomialEval (tensorMvPolynomial μ T)=tensorPolynomial μ T := by
  funext x
  change (MvPolynomial.eval (fun j => x j)) (tensorMvPolynomial μ T)=_
  unfold tensorMvPolynomial tensorPolynomial
  rw [MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [MvPolynomial.eval_mul,MvPolynomial.eval_C]
  exact congrArg (fun z => T a b c*z) (congrFun (coordinateCubic_eval μ a b c) x)

theorem tensorPolynomial_contDiff (μ : Measure (Space n)) (T : Array3 (Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (tensorPolynomial μ T) := by
  rw [←tensorMvPolynomial_eval]
  exact polynomialEval_contDiff _

theorem tensorPolynomial_original_test {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) : LocallyLipschitzTests μ (tensorPolynomial μ T) :=
  ⟨((tensorPolynomial_contDiff μ T).of_le (by simp)).locallyLipschitz,
    tensorPolynomial_memLp hμ T⟩

theorem coordinateCubic_derivative (μ : Measure (Space n)) (a b c i : Fin n) (x : Space n) :
    coordinateDerivative (coordinateCubic μ a b c) i x=
      δ i a*(x b*x c-δ b c)+δ i b*(x a*x c-δ a c)+δ i c*(x a*x b-δ a b) := by
  rw [←coordinateCubic_eval,coordinateDerivative_polynomialEval]
  change (MvPolynomial.eval (fun j => x j))
    (MvPolynomial.pderiv i (coordinateCubicPolynomial μ a b c))=_
  have hs (p q : MvPolynomial (Fin n) ℝ) :
      MvPolynomial.pderiv i (p-q)=MvPolynomial.pderiv i p-MvPolynomial.pderiv i q :=
    map_sub (MvPolynomial.pderiv i) p q
  have hX (j : Fin n) : MvPolynomial.pderiv i (MvPolynomial.X j : MvPolynomial (Fin n) ℝ)=
      MvPolynomial.C (δ i j) := by
    by_cases h : i=j
    · subst j
      simp [δ]
    · simp [MvPolynomial.pderiv_X,δ,Pi.single_apply,h,eq_comm]
  simp only [coordinateCubicPolynomial,hs,MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_C,hX,zero_mul,zero_sub,sub_zero,
    MvPolynomial.eval_add,MvPolynomial.eval_sub,MvPolynomial.eval_mul,
    MvPolynomial.eval_C,MvPolynomial.eval_X,map_zero]
  ring

theorem centeredQuadratic_eq_sum (H : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    centeredQuadratic H x=∑ a,∑ b,H a b*(x a*x b-δ a b) := by
  have ht : (∑ a,∑ b,H a b*δ a b)=Matrix.trace H := by
    simp [δ,Matrix.trace,mul_ite]
  unfold centeredQuadratic matrixQuadratic
  rw [←ht]
  simp only [mul_sub,Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tensorPolynomial_derivative (μ : Measure (Space n)) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (i : Fin n) (x : Space n) :
    coordinateDerivative (tensorPolynomial μ T) i x=3*centeredQuadratic (T i) x := by
  have hd (a b c : Fin n) : DifferentiableAt ℝ (coordinateCubic μ a b c) x := by
    rw [←coordinateCubic_eval]
    exact (polynomialEval_contDiff _).differentiable (by simp) x
  unfold tensorPolynomial
  rw [coordinateDerivative_sum (fun a =>
    DifferentiableAt.fun_sum fun b _ => DifferentiableAt.fun_sum fun c _ => (hd a b c).const_mul _) i]
  simp_rw [coordinateDerivative_sum (fun b =>
    DifferentiableAt.fun_sum fun c _ => (hd _ b c).const_mul _) i,
    coordinateDerivative_sum (fun c => (hd _ _ c).const_mul _) i]
  have hscale (a b c : Fin n) :
      coordinateDerivative (fun y => T a b c*coordinateCubic μ a b c y) i x=
        T a b c*coordinateDerivative (coordinateCubic μ a b c) i x := by
    change coordinateDerivative (T a b c • coordinateCubic μ a b c) i x=_
    exact coordinateDerivative_smul (hd a b c) (T a b c) i
  simp_rw [hscale,coordinateCubic_derivative,mul_add,Finset.sum_add_distrib]
  have hfirst : (∑ a,∑ b,∑ c,T a b c*(δ i a*(x b*x c-δ b c)))=
      ∑ b,∑ c,T i b c*(x b*x c-δ b c) := by
    simp only [δ]
    simp only [mul_ite, ite_mul, mul_one,mul_zero,zero_mul,
      Finset.sum_ite_irrel]
    simp
  have hsecond : (∑ a,∑ b,∑ c,T a b c*(δ i b*(x a*x c-δ a c)))=
      ∑ a,∑ c,T i a c*(x a*x c-δ a c) := by
    apply Finset.sum_congr rfl
    intro a _
    have he : (∑ b,∑ c,T a b c*(δ i b*(x a*x c-δ a c)))=
        ∑ c,T a i c*(x a*x c-δ a c) := by
      simp only [δ]
      simp only [mul_ite,ite_mul,mul_one,mul_zero,zero_mul,Finset.sum_ite_irrel]
      simp
    rw [he]
    apply Finset.sum_congr rfl
    intro c _
    rw [hT12 a i c]
  have hthird : (∑ a,∑ b,∑ c,T a b c*(δ i c*(x a*x b-δ a b)))=
      ∑ a,∑ b,T i a b*(x a*x b-δ a b) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    have he : (∑ c,T a b c*(δ i c*(x a*x b-δ a b)))=
        T a b i*(x a*x b-δ a b) := by
      calc
        _ = ∑ c,δ i c*(T a b c*(x a*x b-δ a b)) := by
          apply Finset.sum_congr rfl
          intro c _
          ring
        _ = _ := by simp [δ,ite_mul,eq_comm]
    rw [he]
    rw [hT23 a b i,hT12 a i b]
  rw [hfirst,hsecond,hthird,centeredQuadratic_eq_sum]
  ring

end KLSConstantImprovement.ActualCubicGradientEnergy
#print axioms KLSConstantImprovement.ActualCubicGradientEnergy.tensorMvPolynomial_eval
#print axioms KLSConstantImprovement.ActualCubicGradientEnergy.tensorPolynomial_contDiff
#print axioms KLSConstantImprovement.ActualCubicGradientEnergy.tensorPolynomial_original_test
#print axioms KLSConstantImprovement.ActualCubicGradientEnergy.coordinateCubic_derivative
#print axioms KLSConstantImprovement.ActualCubicGradientEnergy.centeredQuadratic_eq_sum
#print axioms KLSConstantImprovement.ActualCubicGradientEnergy.tensorPolynomial_derivative
