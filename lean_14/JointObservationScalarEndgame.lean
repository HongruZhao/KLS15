import ScalarSpectralContradiction

/-! A summable joint observation budget controls the entire adjoint orbit.
This is the scalar endgame; actual law and observation premises are
supplied separately by the coupled Appell development. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.CoupledEnergy
set_option maxHeartbeats 1000000

def prefixBudget (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, c (i+1)

@[simp] theorem prefixBudget_zero (c : ℕ → ℝ) : prefixBudget c 0=0 := by
  simp [prefixBudget]

@[simp] theorem prefixBudget_succ (c : ℕ → ℝ) (n : ℕ) :
    prefixBudget c (n+1)=prefixBudget c n+c (n+1) := by
  simp [prefixBudget,Finset.sum_range_succ]

theorem normalized_orbit_le_one_add_budget
    (z c : ℕ → ℝ) {C : ℝ} (_hC : 0 ≤ C)
    (hz0 : z 0=1) (hc : ∀ n, 0 ≤ c (n+1))
    (hbudget : ∀ n, prefixBudget c n ≤ C)
    (hrec : ∀ n, 0<z n → 0<z (n+1) →
      z (n+1)^2/z n-c (n+1) ≤ z (n+2))
    (henvelope : ∀ rho : ℝ, 1<rho → ∃ M : ℝ, ∀ n, z n ≤ M*rho^n) :
    z 1 ≤ 1+C := by
  by_contra hnot
  have ha : 1+C<z 1 := not_le.mp hnot
  let r : ℝ := z 1-C
  have hr : 1<r := by dsimp [r]; linarith
  have hr0 : 0<r := by linarith
  have hinv : ∀ n, r^n ≤ z n ∧ z 1-prefixBudget c n ≤ z (n+1)/z n := by
    intro n
    induction n with
    | zero =>
        simp [hz0]
    | succ n ih =>
        have hz : 0<z n := lt_of_lt_of_le (pow_pos hr0 n) ih.1
        have hratio : r ≤ z (n+1)/z n := by
          dsimp [r]
          linarith [hbudget n,ih.2]
        have hmul : r*z n ≤ z (n+1) := (le_div_iff₀ hz).mp hratio
        have hnext : r^(n+1) ≤ z (n+1) := by
          rw [pow_succ]
          calc
            r^n*r ≤ z n*r := mul_le_mul_of_nonneg_right ih.1 hr0.le
            _ ≤ z (n+1) := by simpa only [mul_comm] using hmul
        have hznext : 0<z (n+1) := lt_of_lt_of_le (pow_pos hr0 (n+1)) hnext
        have hone : 1≤z (n+1) := (one_le_pow₀ hr.le).trans hnext
        have hdrop : c (n+1)/z (n+1) ≤ c (n+1) :=
          div_le_self (hc n) hone
        have hratioRec : z (n+1)/z n-c (n+1)/z (n+1) ≤ z (n+2)/z (n+1) := by
          apply (le_div_iff₀ hznext).mpr
          have he : (z (n+1)/z n-c (n+1)/z (n+1))*z (n+1)=
              z (n+1)^2/z n-c (n+1) := by
            field_simp
          rw [he]
          exact hrec n hz hznext
        refine ⟨hnext,?_⟩
        rw [prefixBudget_succ]
        simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.reduceAdd] using
          (show z 1-(prefixBudget c n+c (n+1)) ≤ z (n+2)/z (n+1) by linarith [ih.2])
  let rho : ℝ := (1+r)/2
  have hrho : 1<rho := by dsimp [rho]; linarith
  obtain ⟨M,hM⟩ := henvelope rho hrho
  exact no_growth_above_exponential_envelope
    (by linarith : 0<rho) (by dsimp [rho]; linarith : rho<r)
    (fun n => (hinv n).1) hM

theorem prefixBudget_eq_Icc (c : ℕ → ℝ) (n : ℕ) :
    prefixBudget c n=∑ m∈Finset.Icc 1 n,c m := by
  induction n with
  | zero => simp [prefixBudget]
  | succ n ih =>
      rw [prefixBudget_succ,ih,Finset.sum_Icc_succ_top (by omega : 1≤n+1)]

theorem scalar_orbit_le_rate_mul_one_add_budget
    (u b : ℕ → ℝ) {K C : ℝ} (hK : 0<K) (hC : 0≤C)
    (hu0 : u 0=1) (hb : ∀ n,0≤b (n+1))
    (hbudget : ∀ N,∑ m∈Finset.Icc 1 N,K⁻¹^(m+1)*b m ≤ C)
    (hrec : ∀ n,0<u n → 0<u (n+1) →
      u (n+1)^2/u n-b (n+1) ≤ u (n+2))
    (henvelope : ∀ rho : ℝ,1<rho → ∃ M : ℝ,∀ n,u n≤M*(K*rho)^n) :
    u 1≤K*(1+C) := by
  let z : ℕ → ℝ := fun n => u n/K^n
  let c : ℕ → ℝ := fun n => K⁻¹^(n+1)*b n
  have hz0 : z 0=1 := by simp [z,hu0]
  have hc : ∀ n,0≤c (n+1) := by intro n; dsimp [c]; positivity [hb n]
  have hcBudget : ∀ n,prefixBudget c n≤C := by
    intro n
    rw [prefixBudget_eq_Icc]
    exact hbudget n
  have hzrec : ∀ n,0<z n → 0<z (n+1) →
      z (n+1)^2/z n-c (n+1)≤z (n+2) := by
    intro n hn hn1
    have hu : 0<u n := (div_pos_iff_of_pos_right (pow_pos hK n)).mp hn
    have hu1 : 0<u (n+1) := (div_pos_iff_of_pos_right (pow_pos hK (n+1))).mp hn1
    have hr := div_le_div_of_nonneg_right (hrec n hu hu1) (pow_nonneg hK.le (n+2))
    have he : (u (n+1)^2/u n-b (n+1))/K^(n+2)=z (n+1)^2/z n-c (n+1) := by
      dsimp [z,c]
      simp only [inv_pow,Nat.add_assoc,Nat.reduceAdd]
      rw [pow_add K n 2,pow_succ]
      field_simp [ne_of_gt hK,ne_of_gt hu]
      ring
    rw [he] at hr
    exact hr
  have hzenv : ∀ rho : ℝ,1<rho → ∃ M : ℝ,∀ n,z n≤M*rho^n := by
    intro rho hrho
    obtain ⟨M,hM⟩ := henvelope rho hrho
    refine ⟨M,fun n => ?_⟩
    have he := div_le_div_of_nonneg_right (hM n) (pow_nonneg hK.le n)
    have hid : M*(K*rho)^n/K^n=M*rho^n := by
      rw [mul_pow]
      field_simp
    rwa [hid] at he
  have hh := normalized_orbit_le_one_add_budget z c hC hz0 hc hcBudget hzrec hzenv
  have hh' : u 1/K≤1+C := by simpa [z] using hh
  exact (div_le_iff₀ hK).mp hh' |>.trans_eq (mul_comm _ _)

end KLSBelow25.CoupledEnergy
#print axioms KLSBelow25.CoupledEnergy.normalized_orbit_le_one_add_budget

#print axioms KLSBelow25.CoupledEnergy.scalar_orbit_le_rate_mul_one_add_budget
