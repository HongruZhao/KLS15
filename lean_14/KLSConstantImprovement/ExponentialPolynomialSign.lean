import Mathlib

/-! Analytic sign lemmas for the finite radial-hinge certificate.
Initial jets and the dominant-exponential allocation remain concrete
certificate obligations, rather than floating or external success flags.
-/
noncomputable section
open Set
open scoped BigOperators
namespace KLSConstantImprovement.ExponentialPolynomialSign
set_option maxHeartbeats 2000000

theorem derivative_chain_nonnegative (N : ℕ) (f : ℕ → ℝ → ℝ)
    (hderiv : ∀ n, n<N → ∀ x, HasDerivAt (f n) (f (n+1) x) x)
    (hinitial : ∀ n, n<N → 0 ≤ f n 0)
    (htop : ∀ x, 0 ≤ x → 0 ≤ f N x) : ∀ x, 0 ≤ x → 0 ≤ f 0 x := by
  induction N generalizing f with
  | zero => simpa using htop
  | succ N ih =>
    have htail : ∀ x, 0 ≤ x → 0 ≤ f 1 x := by
      apply ih (fun n => f (n+1))
      · intro n hn x
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hderiv (n+1) (by omega) x
      · intro n hn
        exact hinitial (n+1) (by omega)
      · exact htop
    have hcontinuous : Continuous (f 0) :=
      continuous_iff_continuousAt.mpr (fun x => (hderiv 0 (by omega) x).continuousAt)
    have hmono : MonotoneOn (f 0) (Ici (0:ℝ)) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        hcontinuous.continuousOn
        (fun x _ => (hderiv 0 (by omega) x).hasDerivWithinAt)
      intro x hx
      exact htail x (interior_subset hx)
    intro x hx
    exact (hinitial 0 (by omega)).trans (hmono (by simp) hx hx)

theorem exponential_monomial_domination {L p P : ℝ} (b : ℕ)
    (hL : 0 ≤ L) (hp : p<P) :
    L^b*Real.exp (p*L) ≤ (b.factorial : ℝ)/(P-p)^b*Real.exp (P*L) := by
  have hdelta : 0 < P-p := sub_pos.mpr hp
  have hfactorial : 0 < (b.factorial : ℝ) := by exact_mod_cast b.factorial_pos
  have hpower : 0 < (P-p)^b := pow_pos hdelta b
  have he := Real.pow_div_factorial_le_exp ((P-p)*L)
    (mul_nonneg hdelta.le hL) b
  have hscaled : (P-p)^b*L^b ≤ (b.factorial : ℝ)*Real.exp ((P-p)*L) := by
    have h := (div_le_iff₀ hfactorial).mp he
    simpa only [mul_pow, mul_comm] using h
  have hproduct := mul_le_mul_of_nonneg_right hscaled (Real.exp_pos (p*L)).le
  have hexp : Real.exp ((P-p)*L)*Real.exp (p*L)=Real.exp (P*L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcombined : (P-p)^b*(L^b*Real.exp (p*L)) ≤
      (b.factorial : ℝ)*Real.exp (P*L) := by
    simpa only [mul_assoc, hexp] using hproduct
  calc
    L^b*Real.exp (p*L) ≤ (b.factorial : ℝ)*Real.exp (P*L)/(P-p)^b :=
      (le_div_iff₀ hpower).mpr (by simpa [mul_comm] using hcombined)
    _ = (b.factorial : ℝ)/(P-p)^b*Real.exp (P*L) := by ring

theorem finite_dominant_exponential_budget {ι : Type*} (s : Finset ι)
    (b : ι → ℕ) (p c : ι → ℝ) (P A : ℝ) (f : ℝ → ℝ)
    (hc : ∀ i∈s, 0 ≤ c i) (hp : ∀ i∈s, p i<P)
    (hbudget : (∑ i∈s, c i*(b i).factorial/(P-p i)^(b i)) ≤ A)
    (hform : ∀ L, 0 ≤ L → A*Real.exp (P*L) -
        (∑ i∈s, c i*L^(b i)*Real.exp (p i*L)) ≤ f L) :
    ∀ L, 0 ≤ L → 0 ≤ f L := by
  intro L hL
  have hsum : (∑ i∈s, c i*L^(b i)*Real.exp (p i*L)) ≤
      (∑ i∈s, c i*(b i).factorial/(P-p i)^(b i))*Real.exp (P*L) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left
      (exponential_monomial_domination (b i) hL (hp i hi)) (hc i hi)
    convert h using 1 <;> ring
  have hcharge := mul_le_mul_of_nonneg_right hbudget (Real.exp_pos (P*L)).le
  have hnonneg : 0 ≤ A*Real.exp (P*L) -
      (∑ i∈s, c i*L^(b i)*Real.exp (p i*L)) := by linarith
  exact hnonneg.trans (hform L hL)

end KLSConstantImprovement.ExponentialPolynomialSign
#print axioms KLSConstantImprovement.ExponentialPolynomialSign.derivative_chain_nonnegative
#print axioms KLSConstantImprovement.ExponentialPolynomialSign.exponential_monomial_domination
#print axioms KLSConstantImprovement.ExponentialPolynomialSign.finite_dominant_exponential_budget
