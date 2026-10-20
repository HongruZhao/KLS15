import KLSConstantImprovement.ExponentialPolynomialIntegerJets
import KLSConstantImprovement.RadialHingeDominantEntries

/-! Reindex the actual analytic derivative into its checked finite coefficients. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.ExponentialPolynomialCoefficientExpansion
open ExponentialPolynomialDerivatives ExponentialPolynomialIntegerJets
open RadialHingeInitialJetEntries RadialHingeDominantEntries
set_option maxHeartbeats 2000000

theorem monomial_derivative_reflected (t : JetTerm) {n B : ℕ}
    (hB : t.1 ≤ B) (hn : B ≤ n) (L : ℝ) :
    iteratedDeriv n (monomial (t.1,(t.2.1:ℝ),(t.2.2:ℝ))) L =
      ∑ b ∈ Finset.range (B+1), if b ≤ t.1 then
        (t.2.2:ℝ)*(n.choose (t.1-b):ℝ)*(t.1.descFactorial (t.1-b):ℝ)*
          (t.2.1:ℝ)^(n-(t.1-b))*L^b*Real.exp ((t.2.1:ℝ)*L) else 0 := by
  rw [monomial_iteratedDeriv,Finset.mul_sum]
  let f : ℕ→ℝ := fun i=>(t.2.2:ℝ)*(n.choose i:ℝ)*(t.1.descFactorial i:ℝ)*
    L^(t.1-i)*(t.2.1:ℝ)^(n-i)*Real.exp ((t.2.1:ℝ)*L)
  have hcut : (∑ i ∈ Finset.range (n+1), f i)=
      ∑ i ∈ Finset.range (t.1+1), f i := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i hi hnot
    have ht:t.1 < i := by simp only [Finset.mem_range] at hnot;omega
    simp [f,Nat.descFactorial_eq_zero_iff_lt.mpr ht]
  have hreverse : (∑ i ∈ Finset.range (t.1+1), f i)=
      ∑ b ∈ Finset.range (t.1+1), f (t.1-b) := by
    simpa only [Nat.add_sub_cancel] using (Finset.sum_range_reflect f (t.1+1)).symm
  have hextend : (∑ b ∈ Finset.range (t.1+1), if b ≤ t.1 then f (t.1-b) else 0)=
      ∑ b ∈ Finset.range (B+1), if b ≤ t.1 then f (t.1-b) else 0 := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro b hb hnot
    have hlt:t.1 < b := by simp only [Finset.mem_range] at hnot;omega
    simp [not_le.mpr hlt]
  calc
    _ = ∑ i ∈ Finset.range (n+1), f i := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [f]
      ring
    _ = ∑ b ∈ Finset.range (t.1+1), f (t.1-b) := hcut.trans hreverse
    _ = ∑ b ∈ Finset.range (t.1+1), if b ≤ t.1 then f (t.1-b) else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [if_pos (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hb)]
    _ = ∑ b ∈ Finset.range (B+1), if b ≤ t.1 then f (t.1-b) else 0 := hextend
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases ht:b ≤ t.1
      · simp only [ht,ite_true,f,Nat.sub_sub_self ht]
        ring
      · simp only [ht,ite_false]

theorem singleton_derivative_coefficients (t : JetTerm) {n B P : ℕ}
    (hB : t.1 ≤ B) (hp : t.2.1 ≤ P) (hn : B ≤ n) (L : ℝ) :
    iteratedDeriv n (monomial (t.1,(t.2.1:ℝ),(t.2.2:ℝ))) L =
      ∑ b ∈ Finset.range (B+1), ∑ p ∈ Finset.range (P+1),
        (derivativeCoefficient [t] n b p:ℝ)*L^b*Real.exp ((p:ℝ)*L) := by
  rw [monomial_derivative_reflected t hB hn L]
  apply Finset.sum_congr rfl
  intro b hb
  have hbn:b ≤ B := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hb
  simp only [derivativeCoefficient,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,Int.cast_ite,Int.cast_mul,Int.cast_natCast,Int.cast_pow,Int.cast_zero]
  by_cases ht:b ≤ t.1
  · have hdiff:t.1-b ≤ n := by omega
    simp only [ht,hdiff,and_true,ite_true,ite_mul,zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range,Nat.lt_succ_iff,hp,ite_true]
  · simp only [ht,and_false,false_and,ite_false,Int.cast_zero,zero_mul,Finset.sum_const_zero]

theorem integerPolynomial_derivative_coefficients (ts : List JetTerm) {n B P : ℕ}
    (hB : ∀ t∈ts, t.1 ≤ B) (hp : ∀ t∈ts, t.2.1 ≤ P) (hn : B ≤ n) (L : ℝ) :
    iteratedDeriv n (integerPolynomial ts) L =
      ∑ b ∈ Finset.range (B+1), ∑ p ∈ Finset.range (P+1),
        (derivativeCoefficient ts n b p:ℝ)*L^b*Real.exp ((p:ℝ)*L) := by
  rw [integerPolynomial,polynomial_iteratedDeriv]
  induction ts with
  | nil => simp [realTerms,derivativeCoefficient]
  | cons t ts ih =>
    have ht:=singleton_derivative_coefficients t (hB t (by simp)) (hp t (by simp)) hn L
    have hi:=ih (fun u hu=>hB u (by simp [hu])) (fun u hu=>hp u (by simp [hu]))
    change iteratedDeriv n (monomial (t.1,(t.2.1:ℝ),(t.2.2:ℝ))) L+
      ((realTerms ts).map fun t=>iteratedDeriv n (monomial t) L).sum = _
    rw [ht,hi,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [derivativeCoefficient,List.map_cons,List.sum_cons,List.map_nil,
      List.sum_nil,add_zero,Int.cast_add]
    ring

theorem integerPolynomial_coefficients (ts : List JetTerm) {B P : ℕ}
    (hB : ∀ t∈ts, t.1 ≤ B) (hp : ∀ t∈ts, t.2.1 ≤ P) (L : ℝ) :
    integerPolynomial ts L =
      ∑ b ∈ Finset.range (B+1), ∑ p ∈ Finset.range (P+1),
        (coefficient ts b p:ℝ)*L^b*Real.exp ((p:ℝ)*L) := by
  induction ts with
  | nil => simp [integerPolynomial,realTerms,polynomial,coefficient]
  | cons t ts ih =>
    have hi:=ih (fun u hu=>hB u (by simp [hu])) (fun u hu=>hp u (by simp [hu]))
    have hmono:monomial (t.1,(t.2.1:ℝ),(t.2.2:ℝ)) L=
      ∑ b ∈ Finset.range (B+1), ∑ p ∈ Finset.range (P+1),
        (coefficient [t] b p:ℝ)*L^b*Real.exp ((p:ℝ)*L) := by
      rw [Finset.sum_eq_single t.1]
      · rw [Finset.sum_eq_single t.2.1]
        · simp [coefficient,monomial]
        · intro p hp hne
          simp [coefficient,Ne.symm hne]
        · intro hnot
          exact False.elim (hnot (by simpa only [Finset.mem_range,Nat.lt_succ_iff]
            using (hp t (by simp))))
      · intro b hb hne
        simp [coefficient,Ne.symm hne]
      · intro hnot
        exact False.elim (hnot (by simpa only [Finset.mem_range,Nat.lt_succ_iff]
          using (hB t (by simp))))
    change monomial (t.1,(t.2.1:ℝ),(t.2.2:ℝ)) L+integerPolynomial ts L = _
    rw [hmono,hi,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [coefficient,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,add_zero,
      Int.cast_add]
    ring

theorem integerPolynomial_derivative_eq_checked (ts us : List JetTerm) {n B P : ℕ}
    (hB : ∀ t∈ts, t.1 ≤ B) (hp : ∀ t∈ts, t.2.1 ≤ P)
    (huB : ∀ t∈us, t.1 ≤ B) (hup : ∀ t∈us, t.2.1 ≤ P) (hn : B ≤ n)
    (heq : ∀ b : Fin (B+1), ∀ p : Fin (P+1),
      derivativeCoefficient ts n b p=coefficient us b p) (L : ℝ) :
    iteratedDeriv n (integerPolynomial ts) L=integerPolynomial us L := by
  rw [integerPolynomial_derivative_coefficients ts hB hp hn L,
    integerPolynomial_coefficients us huB hup L]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro p hp
  rw [heq ⟨b,by simpa only [Finset.mem_range] using hb⟩
    ⟨p,by simpa only [Finset.mem_range] using hp⟩]

end KLSConstantImprovement.ExponentialPolynomialCoefficientExpansion
#print axioms KLSConstantImprovement.ExponentialPolynomialCoefficientExpansion.monomial_derivative_reflected
#print axioms KLSConstantImprovement.ExponentialPolynomialCoefficientExpansion.integerPolynomial_derivative_coefficients
#print axioms KLSConstantImprovement.ExponentialPolynomialCoefficientExpansion.integerPolynomial_derivative_eq_checked
