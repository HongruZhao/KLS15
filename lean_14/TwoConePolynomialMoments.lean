import SingleSlotCounterexampleMoments

/-! Actual two-cone probability measures and their polynomial expectation.
All identities are derived from the actual product exponential measure.
The parameters are not supplied as moment assumptions. -/
noncomputable section
open MeasureTheory MvPolynomial
open ProbabilityTheory hiding moment
open scoped BigOperators ENNReal
namespace KLSImprovement.TwoConeMoments
open KLS KLSImprovement.ProductPolynomial
open KLSImprovement.TwoDimensionalExponential
open KLSImprovement.SingleSlotCounterexample
  (Poly component polyEval polynomialMap polynomialMap_measurable
   integrable_component integral_component polyEval_measurable)
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

def leftPoly : Fin 2→Poly := ![X 0,X 1]
def rightPoly (d g:ℝ) : Fin 2→Poly :=
  ![X 0+C ((d+1)*g)*X 1,C (-d)*X 1]

def rawMeasure (d g:ℝ):Measure (Space 2) :=
  ENNReal.ofReal (1/(d+1)) • component leftPoly+
  ENNReal.ofReal (d/(d+1)) • component (rightPoly d g)

def rawMoment (d g:ℝ) (p:Poly):ℝ :=
  ∫x,polyEval p x ∂rawMeasure d g

def qMoment (d g:ℝ) (p:Poly):ℝ :=
  (moment (MvPolynomial.eval₂ C leftPoly p)+
    d*moment (MvPolynomial.eval₂ C (rightPoly d g) p))/(d+1)

theorem integrable_raw_polynomial (d g:ℝ) (p:Poly):
    Integrable (polyEval p) (rawMeasure d g) :=
  ((integrable_component leftPoly p).smul_measure (by simp)).add_measure
    ((integrable_component (rightPoly d g) p).smul_measure (by simp))

theorem rawMoment_eq_qMoment {d:ℝ} (hd:0≤d) (g:ℝ) (p:Poly):
    rawMoment d g p=qMoment d g p := by
  have hden : 0 < d+1 := by linarith
  unfold rawMoment rawMeasure
  rw [integral_add_measure
    ((integrable_component leftPoly p).smul_measure (by simp))
    ((integrable_component (rightPoly d g) p).smul_measure (by simp)),
    integral_smul_measure,integral_smul_measure,integral_component,integral_component]
  have hw1 : 0≤1/(d+1) := div_nonneg zero_le_one hden.le
  have hw2 : 0≤d/(d+1) := div_nonneg hd hden.le
  rw [ENNReal.toReal_ofReal hw1,ENNReal.toReal_ofReal hw2]
  simp only [smul_eq_mul]
  unfold qMoment
  ring

theorem raw_isProbability {d:ℝ} (hd:0≤d) (g:ℝ):
    IsProbabilityMeasure (rawMeasure d g) := by
  have hden : 0 < d+1 := by linarith
  have hcomp (q:Fin 2→Poly):IsProbabilityMeasure (component q) :=
    (Measure.isProbabilityMeasure_map_iff (polynomialMap_measurable q).aemeasurable).mpr
      inferInstance
  haveI := hcomp leftPoly
  haveI := hcomp (rightPoly d g)
  constructor
  simp only [rawMeasure,Measure.add_apply,Measure.smul_apply,measure_univ,
    smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_add (div_nonneg (by norm_num) hden.le) (div_nonneg hd hden.le)]
  have hsum : 1/(d+1)+d/(d+1)=(1:ℝ) := by field_simp [hden.ne'];ring
  rw [hsum]
  simp

theorem qMoment_add (d g:ℝ) (p q:Poly):
    qMoment d g (p+q)=qMoment d g p+qMoment d g q := by
  simp only [qMoment,MvPolynomial.eval₂_add,moment_add]
  ring

theorem qMoment_sub (d g:ℝ) (p q:Poly):
    qMoment d g (p-q)=qMoment d g p-qMoment d g q := by
  simp only [qMoment,MvPolynomial.eval₂_sub,moment_sub]
  ring

theorem qMoment_C_mul (d g c:ℝ) (p:Poly):
    qMoment d g (C c*p)=c*qMoment d g p := by
  simp only [qMoment,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,moment_C_mul]
  ring

theorem moment_sum {ι:Type*} (s:Finset ι) (p:ι→Poly):
    moment (∑i∈s,p i)=∑i∈s,moment (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [moment]
  | @insert a s ha ih => simp [ha,moment_add,ih]

theorem moment_linear_pow_mul (a b:ℝ) (p q:ℕ):
    moment ((C a*X (0:Fin 2)+C b*X 1)^p*X 1^q)=
      ∑j∈Finset.range (p+1),
        (Nat.choose p j:ℝ)*a^j*b^(p-j)*(Nat.factorial j:ℝ)*Nat.factorial (p-j+q) := by
  rw [add_pow,Finset.sum_mul,moment_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hp : ((C a*X (0:Fin 2))^j*(C b*X 1)^(p-j)*
        (Nat.choose p j:Poly))*X 1^q=
      C ((Nat.choose p j:ℝ)*a^j*b^(p-j))*(X 0^j*X 1^(p-j+q)) := by
    simp only [mul_pow,pow_add,map_mul,map_pow,map_natCast]
    ring
  rw [hp,moment_C_mul,moment_Xpow_Xpow]
  ring

theorem qMoment_monomial (d g:ℝ) (p q:ℕ):
    qMoment d g (X (0:Fin 2)^p*X 1^q)=
      ((Nat.factorial p:ℝ)*Nat.factorial q+
        d*((-d)^q*∑j∈Finset.range (p+1),
          (Nat.choose p j:ℝ)*((d+1)*g)^(p-j)*(Nat.factorial j:ℝ)*
            Nat.factorial (p-j+q)))/(d+1) := by
  unfold qMoment
  simp only [leftPoly,rightPoly,eval₂_mul,eval₂_pow,eval₂_X,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [moment_Xpow_Xpow]
  have hp : (X (0:Fin 2)+C ((d+1)*g)*X 1)^p*(C (-d)*X 1)^q=
      C ((-d)^q)*((C 1*X 0+C ((d+1)*g)*X 1)^p*X 1^q) := by
    simp only [map_one,mul_pow,map_pow]
    ring
  rw [hp,moment_C_mul,moment_linear_pow_mul]
  simp only [one_pow,mul_one]

end KLSImprovement.TwoConeMoments
#print axioms KLSImprovement.TwoConeMoments.raw_isProbability
#print axioms KLSImprovement.TwoConeMoments.rawMoment_eq_qMoment
#print axioms KLSImprovement.TwoConeMoments.qMoment_monomial
