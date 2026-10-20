import ProductExponentialPolynomialMoments

/-! A computable polynomial expectation for the actual two-dimensional
rate-one exponential product. Every rewrite below is justified by actual
integrability, not a supplied moment table. -/
noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped BigOperators
namespace KLSImprovement.TwoDimensionalExponential
open KLSImprovement.ProductPolynomial
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

def moment (p:MvPolynomial (Fin 2) ℝ):ℝ :=
  ∫y:Fin 2→ℝ,MvPolynomial.eval y p ∂product 2

@[simp] theorem moment_add (p q:MvPolynomial (Fin 2) ℝ):
    moment (p+q)=moment p+moment q := by
  unfold moment
  simp only [MvPolynomial.eval_add]
  exact integral_add (integrable_polynomial p) (integrable_polynomial q)

@[simp] theorem moment_sub (p q:MvPolynomial (Fin 2) ℝ):
    moment (p-q)=moment p-moment q := by
  unfold moment
  simp only [MvPolynomial.eval_sub]
  exact integral_sub (integrable_polynomial p) (integrable_polynomial q)

@[simp] theorem moment_neg (p:MvPolynomial (Fin 2) ℝ):
    moment (-p)= -moment p := by
  unfold moment
  simp only [MvPolynomial.eval_neg,integral_neg]

@[simp] theorem moment_C (c:ℝ):moment (MvPolynomial.C c)=c := by
  unfold moment
  simp only [MvPolynomial.eval_C,integral_const,Measure.real,measure_univ,
    ENNReal.toReal_one,one_smul]

@[simp] theorem moment_C_mul (c:ℝ) (p:MvPolynomial (Fin 2) ℝ):
    moment (C c*p)=c*moment p := by
  unfold moment
  simp only [eval_mul,eval_C]
  exact integral_const_mul _ _

@[simp] theorem moment_mul_C (p:MvPolynomial (Fin 2) ℝ) (c:ℝ):
    moment (p*C c)=moment p*c := by
  rw [mul_comm,moment_C_mul,mul_comm]

@[simp] theorem moment_C_middle (p q:MvPolynomial (Fin 2) ℝ) (c:ℝ):
    moment (p*(C c*q))=c*moment (p*q) := by
  rw [←mul_assoc,mul_comm p (C c),mul_assoc,moment_C_mul]

@[simp] theorem moment_nat (n:ℕ):moment (n:MvPolynomial (Fin 2) ℝ)=(n:ℝ) := by
  simpa only [map_natCast] using moment_C (n:ℝ)

@[simp] theorem moment_mul_nat (p:MvPolynomial (Fin 2) ℝ) (n:ℕ):
    moment (p*(n:MvPolynomial (Fin 2) ℝ))=moment p*(n:ℝ) := by
  simpa only [map_natCast] using moment_mul_C p (n:ℝ)

@[simp] theorem moment_nat_right (p q:MvPolynomial (Fin 2) ℝ) (n:ℕ):
    moment (p*(q*(n:MvPolynomial (Fin 2) ℝ)))=moment (p*q)*(n:ℝ) := by
  rw [←mul_assoc,moment_mul_nat]

@[simp] theorem moment_ofNat (n:ℕ) [n.AtLeastTwo]:
    moment (OfNat.ofNat n:MvPolynomial (Fin 2) ℝ)=(OfNat.ofNat n:ℝ) := by
  exact moment_nat n

@[simp] theorem moment_mul_ofNat (p:MvPolynomial (Fin 2) ℝ) (n:ℕ) [n.AtLeastTwo]:
    moment (p*(OfNat.ofNat n:MvPolynomial (Fin 2) ℝ))=moment p*(OfNat.ofNat n:ℝ) := by
  exact moment_mul_nat p n

@[simp] theorem moment_ofNat_right (p q:MvPolynomial (Fin 2) ℝ) (n:ℕ) [n.AtLeastTwo]:
    moment (p*(q*(OfNat.ofNat n:MvPolynomial (Fin 2) ℝ)))=
      moment (p*q)*(OfNat.ofNat n:ℝ) := by
  rw [←mul_assoc,moment_mul_ofNat]

@[simp] theorem moment_C_deep (p q r:MvPolynomial (Fin 2) ℝ) (c:ℝ):
    moment (p*(q*(C c*r)))=c*moment (p*(q*r)) := by
  rw [←mul_assoc p q,moment_C_middle,mul_assoc]

@[simp] theorem moment_C_right (p q:MvPolynomial (Fin 2) ℝ) (c:ℝ):
    moment (p*(q*C c))=moment (p*q)*c := by
  rw [←mul_assoc,moment_mul_C]

@[simp] theorem moment_two :moment (2:MvPolynomial (Fin 2) ℝ)=2 := moment_nat 2
@[simp] theorem moment_three :moment (3:MvPolynomial (Fin 2) ℝ)=3 := moment_nat 3
@[simp] theorem moment_mul_two (p:MvPolynomial (Fin 2) ℝ):
    moment (p*2)=moment p*2 := moment_mul_nat p 2
@[simp] theorem moment_mul_three (p:MvPolynomial (Fin 2) ℝ):
    moment (p*3)=moment p*3 := moment_mul_nat p 3
@[simp] theorem moment_mul_four (p:MvPolynomial (Fin 2) ℝ):
    moment (p*4)=moment p*4 := moment_mul_nat p 4
@[simp] theorem moment_mul_six (p:MvPolynomial (Fin 2) ℝ):
    moment (p*6)=moment p*6 := moment_mul_nat p 6
@[simp] theorem moment_mul_eight (p:MvPolynomial (Fin 2) ℝ):
    moment (p*8)=moment p*8 := moment_mul_nat p 8
@[simp] theorem moment_two_right (p q:MvPolynomial (Fin 2) ℝ):
    moment (p*(q*2))=moment (p*q)*2 := by rw [←mul_assoc,moment_mul_two]
@[simp] theorem moment_three_right (p q:MvPolynomial (Fin 2) ℝ):
    moment (p*(q*3))=moment (p*q)*3 := by rw [←mul_assoc,moment_mul_three]
@[simp] theorem moment_four_right (p q:MvPolynomial (Fin 2) ℝ):
    moment (p*(q*4))=moment (p*q)*4 := by rw [←mul_assoc,moment_mul_four]
@[simp] theorem moment_six_right (p q:MvPolynomial (Fin 2) ℝ):
    moment (p*(q*6))=moment (p*q)*6 := by rw [←mul_assoc,moment_mul_six]
@[simp] theorem moment_eight_right (p q:MvPolynomial (Fin 2) ℝ):
    moment (p*(q*8))=moment (p*q)*8 := by rw [←mul_assoc,moment_mul_eight]

@[simp] theorem moment_Xpow_Xpow (p q:ℕ):
    moment ((X (0:Fin 2))^p*(X (1:Fin 2))^q)=(Nat.factorial p:ℝ)*Nat.factorial q := by
  unfold moment
  have hm := integral_monomial (n:=2) ![p,q]
  simpa [Fin.prod_univ_two] using hm

@[simp] theorem moment_X0pow (p:ℕ):moment (X (0:Fin 2)^p)=(Nat.factorial p:ℝ) := by
  simpa using moment_Xpow_Xpow p 0

@[simp] theorem moment_X1pow (q:ℕ):moment (X (1:Fin 2)^q)=(Nat.factorial q:ℝ) := by
  simpa using moment_Xpow_Xpow 0 q

@[simp] theorem moment_X0pow_mulX1 (p:ℕ):
    moment (X (0:Fin 2)^p*X 1)=(Nat.factorial p:ℝ) := by
  simpa using moment_Xpow_Xpow p 1

@[simp] theorem moment_X0_mulX1pow (q:ℕ):
    moment (X (0:Fin 2)*X 1^q)=(Nat.factorial q:ℝ) := by
  simpa using moment_Xpow_Xpow 1 q

@[simp] theorem moment_X0mulX1 :moment (X (0:Fin 2)*X 1)=1 := by
  simpa using moment_Xpow_Xpow 1 1

@[simp] theorem moment_X0 :moment (X (0:Fin 2))=1 := by
  simpa using moment_X0pow 1

@[simp] theorem moment_X1 :moment (X (1:Fin 2))=1 := by
  simpa using moment_X1pow 1

end KLSImprovement.TwoDimensionalExponential
#print axioms KLSImprovement.TwoDimensionalExponential.moment_Xpow_Xpow
#print axioms KLSImprovement.TwoDimensionalExponential.moment_add
