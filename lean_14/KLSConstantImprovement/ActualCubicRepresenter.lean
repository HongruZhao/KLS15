import ActualCubicPolynomialFormula
import PolynomialLawNondegeneracy
import KLSConstantImprovement.ActualDeficitTensorBounds
import KLSConstantImprovement.CubicVarianceObservationTransfer

/-! Literal centered cubic Appell polynomials and actual L2 pairings on
the entire admissible original-law class. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualCubicRepresenter
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise ActualDeficitTensorBounds
variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def δ (a b : Fin n) : ℝ := if a=b then 1 else 0
def coordinateCubic (μ : Measure (Space n)) (a b c : Fin n) (x : Space n) : ℝ :=
  x a*(x b*x c)-δ b c*x a-δ a c*x b-δ a b*x c-actualThirdCubicArray μ a b c
def coordinateCubicPolynomial (μ : Measure (Space n)) (a b c : Fin n) :
    MvPolynomial (Fin n) ℝ :=
  MvPolynomial.X a*(MvPolynomial.X b*MvPolynomial.X c)-
    MvPolynomial.C (δ b c)*MvPolynomial.X a-
    MvPolynomial.C (δ a c)*MvPolynomial.X b-
    MvPolynomial.C (δ a b)*MvPolynomial.X c-MvPolynomial.C (actualThirdCubicArray μ a b c)
def tensorPolynomial (μ : Measure (Space n)) (T : Array3 (Fin n)) (x : Space n) : ℝ :=
  ∑ a,∑ b,∑ c,T a b c*coordinateCubic μ a b c x

set_option maxHeartbeats 200000 in
theorem coordinateCubic_eval (μ : Measure (Space n)) (a b c : Fin n) :
    polynomialEval (coordinateCubicPolynomial μ a b c)=coordinateCubic μ a b c := by
  funext x
  change (MvPolynomial.eval (fun j=>x j)) (coordinateCubicPolynomial μ a b c)=_
  simp only [coordinateCubicPolynomial,coordinateCubic,MvPolynomial.eval_sub,
    MvPolynomial.eval_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]

theorem coordinateCubic_memLp {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (a b c : Fin n) : MemLp (coordinateCubic μ a b c) 2 μ := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  rw [←coordinateCubic_eval]
  exact polynomialEval_memLp_two hμ.logConcave _

theorem coordinateCubic_pairing {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n→ℝ} (hf : MemLp f 2 μ) (a b c : Fin n) :
    (∫ x,coordinateCubic μ a b c x*f x ∂μ)=actualAppellCoefficient μ f 3 ![a,b,c] := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hx (i : Fin n) : MemLp (fun x : Space n=>x i) 2 μ := hμ.isotropic.memLp_coordinate i
  have hxxx : MemLp (fun x : Space n=>x a*(x b*x c)) 2 μ := by
    have he:polynomialEval (MvPolynomial.X a*(MvPolynomial.X b*MvPolynomial.X c))=
        fun x : Space n=>x a*(x b*x c) := by
      funext x;change (MvPolynomial.eval (fun j=>x j)) _=_
      simp only [map_mul,MvPolynomial.eval_X]
    rw [←he]
    exact polynomialEval_memLp_two hμ.logConcave _
  have hi0 : Integrable (fun x=>x a*(x b*x c)*f x) μ := hxxx.integrable_mul hf
  have hi1 : Integrable (fun x=>δ b c*(x a*f x)) μ := ((hx a).integrable_mul hf).const_mul (δ b c)
  have hi2 : Integrable (fun x=>δ a c*(x b*f x)) μ := ((hx b).integrable_mul hf).const_mul (δ a c)
  have hi3 : Integrable (fun x=>δ a b*(x c*f x)) μ := ((hx c).integrable_mul hf).const_mul (δ a b)
  have hi4 := (hf.integrable (by norm_num)).const_mul (actualThirdCubicArray μ a b c)
  have he : (fun x=>coordinateCubic μ a b c x*f x)=fun x=>
      (x a*(x b*x c))*f x-δ b c*(x a*f x)-δ a c*(x b*f x)-
        δ a b*(x c*f x)-actualThirdCubicArray μ a b c*f x := by
    funext x;unfold coordinateCubic;ring
  have he1:=integral_sub hi0 hi1
  have he2:=integral_sub (hi0.sub hi1) hi2
  have he3:=integral_sub ((hi0.sub hi1).sub hi2) hi3
  have he4:=integral_sub (((hi0.sub hi1).sub hi2).sub hi3) hi4
  simp only [Pi.sub_apply] at he1 he2 he3 he4
  rw [he,he4,he3,he2,he1,integral_const_mul,integral_const_mul,integral_const_mul,
    integral_const_mul]
  have hp:=KLSImprovement.CubicFormula.actualAppellCoefficient_three_moment_formula
    hμ.logConcave hμ.isotropic hf a b c
  have hm:actualThirdCubicArray μ a b c=∫ x,x a*x b*x c ∂μ := by
    unfold actualThirdCubicArray
    rw [thirdCumulantMatrix_coordinate_eq_cubic]
    apply integral_congr_ae;exact .of_forall fun x=>by ring
  have hraw:(∫ x,(x a*(x b*x c))*f x ∂μ)=∫ x,x a*f x*(x b*x c) ∂μ := by
    apply integral_congr_ae;exact .of_forall fun x=>by ring
  have ha:(∫ x,x b*f x ∂μ)=∫ x,f x*x b ∂μ := by
    apply integral_congr_ae;exact .of_forall fun x=>by ring
  have hb:(∫ x,x c*f x ∂μ)=∫ x,f x*x c ∂μ := by
    apply integral_congr_ae;exact .of_forall fun x=>by ring
  rw [hm,hraw,ha,hb]
  simpa only [δ,mul_comm] using hp.symm

theorem tensorPolynomial_memLp {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) : MemLp (tensorPolynomial μ T) 2 μ := by
  unfold tensorPolynomial
  exact memLp_finsetSum _ fun a _=>memLp_finsetSum _ fun b _=>
    memLp_finsetSum _ fun c _=>(coordinateCubic_memLp hμ a b c).const_mul (T a b c)

theorem tensorPolynomial_pairing {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    (∫ x,tensorPolynomial μ T x*f x ∂μ)=
      ∑ a,∑ b,∑ c,T a b c*actualAppellCoefficient μ f 3 ![a,b,c] := by
  have hi (a b c : Fin n) : Integrable (fun x=>T a b c*(coordinateCubic μ a b c x*f x)) μ :=
    ((coordinateCubic_memLp hμ a b c).integrable_mul hf).const_mul (T a b c)
  unfold tensorPolynomial
  simp only [Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum Finset.univ (fun a _=>integrable_finsetSum Finset.univ fun b _=>
    integrable_finsetSum Finset.univ fun c _=>hi a b c)]
  apply Finset.sum_congr rfl;intro a _
  rw [integral_finsetSum Finset.univ (fun b _=>integrable_finsetSum Finset.univ fun c _=>hi a b c)]
  apply Finset.sum_congr rfl;intro b _
  rw [integral_finsetSum Finset.univ (fun c _=>hi a b c)]
  simp_rw [integral_const_mul,coordinateCubic_pairing hμ hf]

theorem tensorPolynomial_centered {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) : (∫ x,tensorPolynomial μ T x ∂μ)=0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hp:=tensorPolynomial_pairing hμ T (memLp_const (μ:=μ) (p:=2) (1:ℝ))
  simpa only [mul_one,actualAppellCoefficient_const_fullClass hμ.logConcave 1 (by norm_num : 3≠0),
    mul_zero,Finset.sum_const_zero] using hp

theorem tensorPolynomial_variance_pairing {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ=
      ∑ a,∑ b,∑ c,T a b c*actualAppellCoefficient μ (tensorPolynomial μ T) 3 ![a,b,c] := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  rw [ProbabilityTheory.variance_eq_sub (tensorPolynomial_memLp hμ T),
    tensorPolynomial_centered hμ T]
  simp only [zero_pow (by decide : 2≠0),sub_zero,Pi.pow_apply,pow_two]
  simpa only [pow_two] using tensorPolynomial_pairing hμ T (tensorPolynomial_memLp hμ T)

end KLSConstantImprovement.ActualCubicRepresenter
#print axioms KLSConstantImprovement.ActualCubicRepresenter.coordinateCubic_pairing
#print axioms KLSConstantImprovement.ActualCubicRepresenter.tensorPolynomial_pairing
#print axioms KLSConstantImprovement.ActualCubicRepresenter.tensorPolynomial_centered
#print axioms KLSConstantImprovement.ActualCubicRepresenter.tensorPolynomial_variance_pairing
