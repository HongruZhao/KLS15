import ActualAppellMoments
import FiniteIntegralGram

/-! The actual rate-one exponential Appell Gram, at every degree.
The half budget at K=4 follows from its exact nonnegative row sums. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.ExponentialCriticalGram
open KLSImprovement.Exponential KLSImprovement.ExponentialMoments
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

theorem appell_mul_expansion (m n : ℕ) :
    (fun y : ℝ => appell m y*appell n y)=
      (fun y => y^(m+n+2)-((m:ℝ)+(n:ℝ)+2)*y^(m+n+1)+
        ((m:ℝ)+1)*((n:ℝ)+1)*y^(m+n)) := by
  funext y
  simp only [appell,pow_add,pow_one,pow_two]
  ring

theorem integral_appell_mul (m n : ℕ) :
    (∫ y, appell m y*appell n y ∂expMeasure 1)=
      ((m:ℝ)+1)*((n:ℝ)+1)*((m+n).factorial:ℝ) := by
  rw [appell_mul_expansion]
  have h₂ := (expMeasure_one_nat_moment (m+n+2)).1
  have h₁ := (expMeasure_one_nat_moment (m+n+1)).1
  have h₀ := (expMeasure_one_nat_moment (m+n)).1
  rw [integral_add (f := fun y : ℝ => y^(m+n+2)-((m:ℝ)+(n:ℝ)+2)*y^(m+n+1))
    (g := fun y : ℝ => ((m:ℝ)+1)*((n:ℝ)+1)*y^(m+n))
    (h₂.sub (h₁.const_mul _)) (h₀.const_mul _),
    integral_sub h₂ (h₁.const_mul _),integral_const_mul,integral_const_mul,
    (expMeasure_one_nat_moment _).2,(expMeasure_one_nat_moment _).2,
    (expMeasure_one_nat_moment _).2]
  rw [show m+n+2=(m+n+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
  push_cast
  ring

def weightedAppell (m : ℕ) (y : ℝ) : ℝ :=
  appell m y/((2:ℝ)^(m+1)*((m+1).factorial:ℝ))

theorem weightedAppell_memLp (m : ℕ) :
    MemLp (weightedAppell m) 2 (expMeasure 1) := by
  apply (memLp_two_iff_integrable_sq (by unfold weightedAppell appell;fun_prop)).mpr
  simpa only [weightedAppell,div_pow] using (integrable_appell_sq m).div_const _

theorem integral_weightedAppell_mul (m n : ℕ) :
    (∫ y,weightedAppell m y*weightedAppell n y ∂expMeasure 1)=
      ((m+n).choose m:ℝ)/(2:ℝ)^(m+n+2) := by
  have he : (fun y => weightedAppell m y*weightedAppell n y)=
      (fun y => (appell m y*appell n y)/
        ((2:ℝ)^(m+n+2)*((m+1).factorial:ℝ)*((n+1).factorial:ℝ))) := by
    funext y
    unfold weightedAppell
    rw [show m+n+2=(m+1)+(n+1) by omega,pow_add]
    ring
  rw [he,integral_div,integral_appell_mul,Nat.factorial_succ,Nat.factorial_succ]
  have hf : (m.factorial:ℝ)≠0 := by exact_mod_cast m.factorial_ne_zero
  have hg : (n.factorial:ℝ)≠0 := by exact_mod_cast n.factorial_ne_zero
  have hc : ((m+n).choose m:ℝ)*(m.factorial:ℝ)*(n.factorial:ℝ)=
      ((m+n).factorial:ℝ) := by
    have hh := Nat.choose_mul_factorial_mul_factorial (show m ≤ m+n by omega)
    rw [show m+n-m=n by omega] at hh
    exact_mod_cast hh
  push_cast
  field_simp [hf,hg]
  nlinarith [hc]

def gramEntry (m n : ℕ) : ℝ := ((m+n).choose m:ℝ)/(2:ℝ)^(m+n+2)

theorem gramEntry_nonneg (m n : ℕ) : 0≤gramEntry m n := by
  unfold gramEntry
  positivity

theorem gramEntry_row_hasSum (m : ℕ) :
    HasSum (gramEntry m) (1/2:ℝ) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one m
    (r := (1/2:ℝ)) (by norm_num)).mul_left (1/(2:ℝ)^(m+2))
  convert h using 1
  · funext n
    unfold gramEntry
    rw [show m+n+2=(m+2)+n by omega,pow_add,Nat.add_comm n m]
    simp only [div_pow,one_pow]
    ring
  · norm_num only [show (1-1/2:ℝ)=1/2 by norm_num]
    simp only [one_div]
    rw [show m+2=(m+1)+1 by omega,pow_succ]
    field_simp
    rw [←mul_pow]
    norm_num

theorem finite_gram_row_le_half (M : ℕ) (m : ℕ) :
    (∑ n : Fin M, gramEntry m n.val)≤(1/2:ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => gramEntry m n) M]
  exact sum_le_hasSum (Finset.range M) (fun _ _ => gramEntry_nonneg _ _)
    (gramEntry_row_hasSum m)

theorem exponential_weighted_Appell_finite_budget (M : ℕ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (expMeasure 1)) :
    (∑ m : Fin M, (∫ y,f y*weightedAppell m.val y ∂expMeasure 1)^2)≤
      (1/2:ℝ)*(∫ y,(f y)^2 ∂expMeasure 1) := by
  apply KLSImprovement.FiniteIntegralGram.observation_le_of_integral_gram_rows
    (expMeasure 1) (fun m : Fin M => weightedAppell m.val)
    (fun m => weightedAppell_memLp m.val) (by norm_num) _ hf
  intro m
  simp_rw [integral_weightedAppell_mul]
  change (∑ n : Fin M, |gramEntry m.val n.val|)≤(1/2:ℝ)
  simp_rw [abs_of_nonneg (gramEntry_nonneg _ _)]
  exact finite_gram_row_le_half M m.val

end KLSImprovement.ExponentialCriticalGram
#print axioms KLSImprovement.ExponentialCriticalGram.integral_appell_mul
#print axioms KLSImprovement.ExponentialCriticalGram.gramEntry_row_hasSum
#print axioms KLSImprovement.ExponentialCriticalGram.exponential_weighted_Appell_finite_budget
