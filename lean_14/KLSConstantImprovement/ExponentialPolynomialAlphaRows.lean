import KLSConstantImprovement.ExponentialPolynomialIntegerJets

/-! Bind exact integer alpha rows to the original rational polynomial table. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.ExponentialPolynomialAlphaRows
open RadialHingePolynomialData RadialHingeInitialJetEntries
open ExponentialPolynomialDerivatives ExponentialPolynomialIntegerJets
set_option maxHeartbeats 2000000

def rationalPolynomial (ts : List (ℕ×ℕ×ℚ)) (L : ℝ) : ℝ :=
  (ts.map fun t=>(t.2.2:ℝ)*L^t.1*Real.exp ((t.2.1:ℝ)*L)).sum
def unscaledRow (ts : List Term) (a : ℕ) (L : ℝ) : ℝ :=
  ((ts.filter fun t=>decide (t.1=a)).map
    fun t=>(t.2.2.2:ℝ)*L^t.2.1*Real.exp ((t.2.2.1:ℝ)*L)).sum

theorem originalRow_value (ts : List Term) (a : ℕ) (D : ℚ) (L : ℝ) :
    rationalPolynomial (originalRow ts a D) L=(D:ℝ)*unscaledRow ts a L := by
  unfold originalRow unscaledRow rationalPolynomial
  rw [List.map_map]
  simp only [Function.comp_apply,Rat.cast_mul,mul_assoc]
  induction (ts.filter fun t=>decide (t.1=a)) with
  | nil => simp
  | cons t us ih =>
    simp only [List.map_cons,List.sum_cons,mul_add]
    rw [ih]
    dsimp only [Function.comp_apply]
    simp only [Rat.cast_mul,mul_assoc]

theorem rationalRow_value (ts : List JetTerm) (L : ℝ) :
    rationalPolynomial (rationalRow ts) L=integerPolynomial ts L := by
  induction ts with
  | nil => simp [rationalPolynomial,rationalRow,integerPolynomial,realTerms,polynomial]
  | cons t ts ih =>
    simpa [rationalPolynomial,rationalRow,integerPolynomial,realTerms,polynomial,monomial,
      Rat.cast_intCast] using congrArg (fun x=>(t.2.2:ℝ)*L^t.1*Real.exp ((t.2.1:ℝ)*L)+x) ih

theorem evalTerms_alpha_partition (ts : List Term) {A : ℕ}
    (hs : ∀ t∈ts, t.1 ≤ A) (α L : ℝ) :
    evalTerms ts α L=∑ a ∈ Finset.range (A+1), α^a*unscaledRow ts a L := by
  induction ts with
  | nil => simp [evalTerms,unscaledRow]
  | cons t ts ih =>
    have hi:=ih (fun u hu=>hs u (by simp [hu]))
    have hhead:termEval t α L=∑ a ∈ Finset.range (A+1),
      α^a*(if t.1=a then (t.2.2.2:ℝ)*L^t.2.1*Real.exp ((t.2.2.1:ℝ)*L) else 0) := by
      rw [Finset.sum_eq_single t.1]
      · simp [termEval];ring
      · intro a ha hne
        simp [Ne.symm hne]
      · intro hnot
        exact False.elim (hnot (by simpa only [Finset.mem_range,Nat.lt_succ_iff]
          using (hs t (by simp))))
    change termEval t α L+evalTerms ts α L=_
    rw [hhead,hi,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases ht:t.1=a <;> simp [unscaledRow,ht,mul_add]

theorem evalTerms_eq_integer_rows (ts : List Term) {A : ℕ} (D : ℚ)
    (rows : Fin (A+1)→List JetTerm) (hD : D≠0)
    (hs : ∀ t∈ts, t.1 ≤ A)
    (heq : ∀ a : Fin (A+1), originalRow ts a D=rationalRow (rows a)) (α L : ℝ) :
    evalTerms ts α L=∑ a : Fin (A+1), α^(a:ℕ)/(D:ℝ)*integerPolynomial (rows a) L := by
  rw [evalTerms_alpha_partition ts hs α L,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro a ha
  have h:=originalRow_value ts a D L
  rw [heq a,rationalRow_value] at h
  have hd:(D:ℝ)≠0 := by exact_mod_cast hD
  rw [h]
  field_simp

theorem evalTerms_nonnegative_of_integer_rows (ts : List Term) {A : ℕ} (D : ℚ)
    (rows : Fin (A+1)→List JetTerm) (hD : 0<D)
    (hs : ∀ t∈ts, t.1 ≤ A)
    (heq : ∀ a : Fin (A+1), originalRow ts a D=rationalRow (rows a))
    {α L : ℝ} (hα : 0 ≤ α) (hrows : ∀ a, 0 ≤ integerPolynomial (rows a) L) :
    0 ≤ evalTerms ts α L := by
  rw [evalTerms_eq_integer_rows ts D rows (ne_of_gt hD) hs heq α L]
  apply Finset.sum_nonneg
  intro a ha
  have hd:(0:ℝ)<D := by exact_mod_cast hD
  exact mul_nonneg (div_nonneg (pow_nonneg hα _) hd.le) (hrows a)

theorem evalTerms_zero_le_of_integer_rows (ts : List Term) {A : ℕ} (D : ℚ)
    (rows : Fin (A+1)→List JetTerm) (hD : 0<D)
    (hs : ∀ t∈ts, t.1 ≤ A)
    (heq : ∀ a : Fin (A+1), originalRow ts a D=rationalRow (rows a))
    {α L : ℝ} (hα : 0 ≤ α) (hrows : ∀ a, 0 ≤ integerPolynomial (rows a) L) :
    evalTerms ts 0 L ≤ evalTerms ts α L := by
  rw [evalTerms_eq_integer_rows ts D rows (ne_of_gt hD) hs heq 0 L,
    evalTerms_eq_integer_rows ts D rows (ne_of_gt hD) hs heq α L]
  apply Finset.sum_le_sum
  intro a ha
  have hd:(0:ℝ)<D := by exact_mod_cast hD
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 0) hα _) hd.le)
    (hrows a)

end KLSConstantImprovement.ExponentialPolynomialAlphaRows
#print axioms KLSConstantImprovement.ExponentialPolynomialAlphaRows.evalTerms_eq_integer_rows
#print axioms KLSConstantImprovement.ExponentialPolynomialAlphaRows.evalTerms_nonnegative_of_integer_rows
#print axioms KLSConstantImprovement.ExponentialPolynomialAlphaRows.evalTerms_zero_le_of_integer_rows
