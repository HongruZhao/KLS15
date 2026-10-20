import BernsteinIntervalPositivity

/-! Computable integer coefficient lists with a real evaluation bridge.
Numerical list equalities can be checked by ordinary kernel reduction, while
the real Bernstein identity follows from the generic algebra below. This
module supplies no KLS constant or numerical positivity certificate. -/
namespace KLSConstantImprovement.IntegerListPolynomialCertificate
open scoped BigOperators
open KLSBelow25.BernsteinInterval
set_option maxHeartbeats 2000000

def addCoeff : List ℤ → List ℤ → List ℤ
  | [], q => q
  | p, [] => p
  | a::p, b::q => (a+b)::addCoeff p q

def mulCoeff : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a::p, q => addCoeff (q.map (fun b => a*b)) (0::mulCoeff p q)

def powCoeff (p : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n+1 => mulCoeff p (powCoeff p n)

def sumCoeff : List (List ℤ) → List ℤ
  | [] => []
  | p::ps => addCoeff p (sumCoeff ps)

def eval : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a::p, t => (a:ℝ)+t*eval p t

theorem eval_addCoeff (p q : List ℤ) (t : ℝ) :
    eval (addCoeff p q) t = eval p t+eval q t := by
  induction p generalizing q with
  | nil => simp [addCoeff,eval]
  | cons a p ih =>
      cases q with
      | nil => simp [addCoeff,eval]
      | cons b q =>
          simp only [addCoeff,eval,Int.cast_add,ih]
          ring

theorem eval_scaleCoeff (a : ℤ) (p : List ℤ) (t : ℝ) :
    eval (p.map (fun b => a*b)) t = (a:ℝ)*eval p t := by
  induction p with
  | nil => simp [eval]
  | cons b p ih =>
      simp only [List.map_cons,eval,Int.cast_mul,ih]
      ring

theorem eval_mulCoeff (p q : List ℤ) (t : ℝ) :
    eval (mulCoeff p q) t = eval p t*eval q t := by
  induction p with
  | nil => simp [mulCoeff,eval]
  | cons a p ih =>
      simp only [mulCoeff,eval_addCoeff,eval_scaleCoeff,eval,Int.cast_zero,zero_add,ih]
      ring

theorem eval_powCoeff (p : List ℤ) (n : ℕ) (t : ℝ) :
    eval (powCoeff p n) t = (eval p t)^n := by
  induction n with
  | zero => simp [powCoeff,eval]
  | succ n ih =>
      rw [powCoeff,eval_mulCoeff,ih,pow_succ]
      ring

theorem eval_sumCoeff (ps : List (List ℤ)) (t : ℝ) :
    eval (sumCoeff ps) t = (ps.map (fun p => eval p t)).sum := by
  induction ps with
  | nil => simp [sumCoeff,eval]
  | cons p ps ih => simp [sumCoeff,eval_addCoeff,ih]

def bernsteinCoeff (n : ℕ) (b : Fin (n+1) → ℤ) (span slope offset : ℤ) : List ℤ :=
  sumCoeff (List.ofFn (fun i : Fin (n+1) =>
    mulCoeff [b i] (mulCoeff (powCoeff [-offset,slope] i.val)
      (powCoeff [span+offset,-slope] (n-i.val)))))

theorem eval_bernsteinCoeff (n : ℕ) (b : Fin (n+1) → ℤ)
    (span slope offset : ℤ) (t : ℝ) :
    eval (bernsteinCoeff n b span slope offset) t =
      unnormalizedSum n (fun i => (b i:ℝ)) (span:ℝ) ((slope:ℝ)*t-(offset:ℝ)) := by
  have he1 : eval [-offset,slope] t = (slope:ℝ)*t-(offset:ℝ) := by
    simp [eval]
    ring
  have he2 : eval [span+offset,-slope] t =
      (span:ℝ)-((slope:ℝ)*t-(offset:ℝ)) := by
    simp [eval]
    ring
  simp only [bernsteinCoeff,eval_sumCoeff,List.map_ofFn,Fin.sum_ofFn]
  unfold unnormalizedSum
  apply Finset.sum_congr rfl
  intro i _
  change eval (mulCoeff [b i] (mulCoeff (powCoeff [-offset,slope] i.val)
    (powCoeff [span+offset,-slope] (n-i.val)))) t = _
  rw [eval_mulCoeff,eval_mulCoeff,eval_powCoeff,eval_powCoeff,he1,he2]
  simp [eval,mul_assoc]

theorem real_bernstein_identity_of_coeff_eq {n : ℕ} {p : List ℤ}
    {b : Fin (n+1) → ℤ} {span slope offset : ℤ}
    (heq : p = bernsteinCoeff n b span slope offset) (t : ℝ) :
    eval p t = unnormalizedSum n (fun i => (b i:ℝ)) (span:ℝ)
      ((slope:ℝ)*t-(offset:ℝ)) := by
  rw [heq,eval_bernsteinCoeff]

end KLSConstantImprovement.IntegerListPolynomialCertificate
#print axioms KLSConstantImprovement.IntegerListPolynomialCertificate.eval_addCoeff
#print axioms KLSConstantImprovement.IntegerListPolynomialCertificate.eval_scaleCoeff
#print axioms KLSConstantImprovement.IntegerListPolynomialCertificate.eval_mulCoeff
#print axioms KLSConstantImprovement.IntegerListPolynomialCertificate.eval_powCoeff
#print axioms KLSConstantImprovement.IntegerListPolynomialCertificate.eval_sumCoeff
#print axioms KLSConstantImprovement.IntegerListPolynomialCertificate.eval_bernsteinCoeff
#print axioms KLSConstantImprovement.IntegerListPolynomialCertificate.real_bernstein_identity_of_coeff_eq
