import KLSConstantImprovement.ExponentialPolynomialIntegerJets
import KLSConstantImprovement.RadialHingeDominantEntries

/-! Convert a checked integer dominant-exponential budget to an analytic sign.
No actual-law identification or universal curvature assertion occurs here. -/
noncomputable section
namespace KLSConstantImprovement.ExponentialPolynomialIntegerBudget
open RadialHingeInitialJetEntries RadialHingeDominantEntries
open ExponentialPolynomialDerivatives ExponentialPolynomialIntegerJets
set_option maxHeartbeats 2000000

def negativeCost (t : JetTerm) (P : ℕ) : ℝ :=
  if t.2.1<P ∧ t.2.2<0 then
    (-t.2.2:ℝ)*(t.1.factorial:ℝ)/((P:ℝ)-(t.2.1:ℝ))^t.1 else 0
def totalNegativeCost (ts : List JetTerm) (P : ℕ) : ℝ :=
  (ts.map fun t=>negativeCost t P).sum

theorem negativeBudget_cast (ts : List JetTerm) (P Q : ℕ)
    (hdiv : ∀ t∈ts, t.2.1<P ∧ t.2.2<0 → (P-t.2.1)^t.1 ∣ Q) :
    (negativeBudget ts P Q:ℝ)=(Q:ℝ)*totalNegativeCost ts P := by
  induction ts with
  | nil => simp [negativeBudget,totalNegativeCost]
  | cons t ts ih =>
    have htail:∀ u∈ts, u.2.1<P ∧ u.2.2<0 → (P-u.2.1)^u.1 ∣ Q :=
      fun u hu=>hdiv u (by simp [hu])
    have hi:=ih htail
    change (((if t.2.1<P ∧ t.2.2<0 then
      (-t.2.2)*(t.1.factorial:ℤ)*(Q/(P-t.2.1)^t.1:ℕ) else 0)+
      negativeBudget ts P Q:ℤ):ℝ) = _
    rw [Int.cast_add,hi]
    by_cases ht:t.2.1<P ∧ t.2.2<0
    · have hd:=hdiv t (by simp) ht
      have hd0:0<(P-t.2.1)^t.1 := pow_pos (Nat.sub_pos_of_lt ht.1) _
      have hcast:((Q/((P-t.2.1)^t.1):ℕ):ℝ)=
          (Q:ℝ)/((P:ℝ)-(t.2.1:ℝ))^t.1 := by
        rw [Nat.cast_div hd,Nat.cast_pow,Nat.cast_sub (Nat.le_of_lt ht.1)]
        exact_mod_cast (ne_of_gt hd0)
      change _ = (Q:ℝ)*(negativeCost t P+totalNegativeCost ts P)
      simp only [negativeCost,ht,ht.1,ht.2,and_self,ite_true,
        Int.cast_ite,Int.cast_mul,Int.cast_neg,Int.cast_natCast]
      rw [hcast]
      ring
    · change _ = (Q:ℝ)*(negativeCost t P+totalNegativeCost ts P)
      simp [negativeCost,ht]

theorem monomial_lower {t : JetTerm} {P : ℕ} {L : ℝ}
    (hp : t.2.1 ≤ P) (hc : t.2.1=P → 0 ≤ t.2.2) (hL : 0 ≤ L) :
    ((if t.1=0 ∧ t.2.1=P then t.2.2 else 0:ℤ):ℝ)*Real.exp ((P:ℝ)*L)-
      negativeCost t P*Real.exp ((P:ℝ)*L) ≤
        monomial (t.1,(t.2.1:ℝ),(t.2.2:ℝ)) L := by
  by_cases hcharge:t.1=0 ∧ t.2.1=P
  · simp [hcharge,negativeCost,hcharge.1,hcharge.2,monomial]
  · simp only [hcharge,ite_false,Int.cast_zero,zero_mul,zero_sub]
    by_cases htop:t.2.1=P
    · have hnonneg:(0:ℝ) ≤ t.2.2 := by exact_mod_cast hc htop
      simp only [negativeCost,htop,lt_self_iff_false,false_and,ite_false,zero_mul,neg_zero]
      exact mul_nonneg (mul_nonneg hnonneg (pow_nonneg hL _)) (Real.exp_pos _).le
    · have hlt:t.2.1<P := lt_of_le_of_ne hp htop
      by_cases hneg:t.2.2<0
      · have hb:=ExponentialPolynomialSign.exponential_monomial_domination t.1 hL
          (show (t.2.1:ℝ)<(P:ℝ) by exact_mod_cast hlt)
        have hh:=mul_le_mul_of_nonpos_left hb
          (show (t.2.2:ℝ) ≤ 0 by exact_mod_cast hneg.le)
        simp only [negativeCost,hlt,hneg,and_self,ite_true,monomial]
        convert hh using 1 <;> ring
      · have hnonneg:(0:ℝ) ≤ t.2.2 := by exact_mod_cast (le_of_not_gt hneg)
        simp only [negativeCost,hneg,and_false,ite_false,zero_mul,neg_zero]
        exact mul_nonneg (mul_nonneg hnonneg (pow_nonneg hL _)) (Real.exp_pos _).le

theorem polynomial_lower (ts : List JetTerm) {P : ℕ} {L : ℝ}
    (hp : ∀ t∈ts, t.2.1 ≤ P) (hc : ∀ t∈ts, t.2.1=P → 0 ≤ t.2.2)
    (hL : 0 ≤ L) :
    ((coefficient ts 0 P:ℝ)-totalNegativeCost ts P)*Real.exp ((P:ℝ)*L) ≤
      integerPolynomial ts L := by
  induction ts with
  | nil => simp [coefficient,totalNegativeCost,integerPolynomial,realTerms,polynomial]
  | cons t ts ih =>
    have ht:=monomial_lower (hp t (by simp)) (hc t (by simp)) hL
    have hi:=ih (fun u hu=>hp u (by simp [hu])) (fun u hu=>hc u (by simp [hu]))
    have h:=add_le_add ht hi
    simp only [coefficient,List.map_cons,List.sum_cons,Int.cast_add,
      totalNegativeCost,integerPolynomial,realTerms,polynomial] at *
    convert h using 1 <;> ring

theorem integerPolynomial_nonnegative_of_budget (ts : List JetTerm) (B P Q : ℕ)
    (hvalid : validRow ts B P Q=true) (hQ : 0<Q)
    (hbudget : negativeBudget ts P Q ≤ coefficient ts 0 P*(Q:ℤ)) :
    ∀ L, 0 ≤ L → 0 ≤ integerPolynomial ts L := by
  have hv:∀ t∈ts, t.1 ≤ B ∧ t.2.1 ≤ P ∧ (t.2.1=P → 0 ≤ t.2.2) ∧
      (t.2.1<P ∧ t.2.2<0 → (P-t.2.1)^t.1 ∣ Q) := by
    intro t ht
    exact of_decide_eq_true ((List.all_eq_true.mp hvalid) t ht)
  have hq:(0:ℝ)<Q := by exact_mod_cast hQ
  have hc:totalNegativeCost ts P ≤ (coefficient ts 0 P:ℝ) := by
    have h:(negativeBudget ts P Q:ℝ) ≤ (coefficient ts 0 P:ℝ)*(Q:ℝ) := by
      exact_mod_cast hbudget
    rw [negativeBudget_cast ts P Q (fun t ht=> (hv t ht).2.2.2)] at h
    nlinarith
  intro L hL
  have h:=polynomial_lower ts (fun t ht=>(hv t ht).2.1)
    (fun t ht=>(hv t ht).2.2.1) hL
  exact (mul_nonneg (sub_nonneg.mpr hc) (Real.exp_pos _).le).trans h

theorem entry_derivative_rows_nonnegative (a : Fin 19) {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ integerPolynomial (E11DerivativeRows a) L ∧
      0 ≤ integerPolynomial (O11DerivativeRows a) L := by
  rcases E11_dominant_budgets_valid a with ⟨he,hq,hb⟩
  rcases O11_dominant_budgets_valid a with ⟨oe,oq,ob⟩
  exact ⟨integerPolynomial_nonnegative_of_budget _ 11 6 _ he hq hb L hL,
    integerPolynomial_nonnegative_of_budget _ 11 6 _ oe oq ob L hL⟩

end KLSConstantImprovement.ExponentialPolynomialIntegerBudget
#print axioms KLSConstantImprovement.ExponentialPolynomialIntegerBudget.negativeBudget_cast
#print axioms KLSConstantImprovement.ExponentialPolynomialIntegerBudget.integerPolynomial_nonnegative_of_budget
#print axioms KLSConstantImprovement.ExponentialPolynomialIntegerBudget.entry_derivative_rows_nonnegative
