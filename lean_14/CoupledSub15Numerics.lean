import Mathlib

/-! Exact scalar certificates for the strict sub15 candidate. This module
contains no law-specific theorem and does not itself establish a universal bound. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.CoupledEnergy.NumericsSub15
set_option maxHeartbeats 0

def K : ℝ := 67/5
def C : ℝ := 6/125
def c : ℝ := 149/10
def p : ℝ := 2089/2000
def young (b : ℕ) : ℝ := if b=2 then 8563/10000 else if b=3 then 1061/1000
  else if b ≤ 24 then 3801/2000+(442/625)*((b : ℝ)-4) else 81/5
def youngPrefix (d : ℕ) : ℝ := if d=2 then 0 else if d=3 then 8563/10000
  else if d ≤ 25 then 8563/10000+1061/1000+((d : ℝ)-4)*(3801/2000)+
    (221/625)*((d : ℝ)-4)*((d : ℝ)-5)
  else (951699/5000)+(81/5)*((d : ℝ)-25)
def alpha (d : ℕ) : ℝ :=
  if d=2 then 589/1250 else
  if d=3 then 5797/10000 else
  if d=4 then 4773/10000 else
  if d=5 then 8517/20000 else
  if d=6 then 39593/100000 else
  if d=7 then 4711/12500 else
  if d=8 then 36401/100000 else
  if d=9 then 4437/12500 else
  if d=10 then 34847/100000 else
  if d=11 then 17191/50000 else
  if d=12 then 34061/100000 else
  if d=13 then 16933/50000 else
  if d=14 then 1056/3125 else
  if d=15 then 33849/100000 else 17/50
def A (d : ℕ) : ℝ := 4/(1-alpha d)-2
def coefficient (d : ℕ) : ℝ :=
  (K*alpha (d-1)-A d-K*C/young d)*(d : ℝ)^2-
    (A d-3)*(d : ℝ)-1-youngPrefix d
def head : ℝ := 64/(3*(1-alpha 2))-17+4*K*C/young 2

theorem K_positive : 0 < K := by norm_num [K]
theorem C_positive : 0 < C := by norm_num [C]
theorem c_positive : 0 < c := by norm_num [c]
theorem p_gt_one : 1 < p := by norm_num [p]
theorem alpha_two_ge_third : (1 : ℝ)/3 ≤ alpha 2 := by norm_num [alpha]
theorem young_positive (b : ℕ) (hb : 2 ≤ b) : 0 < young b := by
  by_cases hs : b ≤ 24
  · interval_cases b  <;> norm_num [young]
  · simp only [young,show b≠2 by omega,show b≠3 by omega,show ¬b ≤ 24 by omega,ite_false]
    norm_num

theorem youngPrefix_eq_sum (d : ℕ) (hd : 2 ≤ d) :
    youngPrefix d=∑ b∈Finset.Icc 2 (d-1),young b := by
  classical
  induction d,hd using Nat.le_induction with
  | base => norm_num [youngPrefix]
  | succ d hd ih =>
    have hset : Finset.Icc 2 d=insert d (Finset.Icc 2 (d-1)) := by
      ext b; simp only [Finset.mem_Icc,Finset.mem_insert]; omega
    have hnot : d∉Finset.Icc 2 (d-1) := by simp only [Finset.mem_Icc]; omega
    simp only [Nat.add_sub_cancel]
    rw [hset,Finset.sum_insert hnot,←ih]
    by_cases hs : d ≤ 25
    · interval_cases d  <;> norm_num [youngPrefix,young]
    · simp only [youngPrefix,young,show d≠2 by omega,show d≠3 by omega,
        show d+1≠2 by omega,show d+1≠3 by omega,show ¬d ≤ 25 by omega,
        show ¬d+1 ≤ 25 by omega,show ¬d ≤ 24 by omega,ite_false,Nat.cast_add,Nat.cast_one]
      ring

theorem alpha_eq_tail (d : ℕ) (hd : 16 ≤ d) : alpha d=(17 : ℝ)/50 := by
  simp only [alpha,show d≠2 by omega,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,ite_false]
theorem alpha_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ alpha d := by
  by_cases hs : d ≤ 15
  · interval_cases d  <;> norm_num [alpha]
  · rw [alpha_eq_tail d (by omega)]; norm_num
theorem alpha_lt_one (d : ℕ) (hd : 2 ≤ d) : alpha d < 1 := by
  by_cases hs : d ≤ 15
  · interval_cases d  <;> norm_num [alpha]
  · rw [alpha_eq_tail d (by omega)]; norm_num

theorem coefficient_tail (d : ℕ) (hd : 26 ≤ d) :
    coefficient d=(6767 : ℝ)/14850*(d : ℝ)^2-(2848 : ℝ)/165*(d : ℝ)+(1068301 : ℝ)/5000 := by
  unfold coefficient A
  rw [alpha_eq_tail (d-1) (by omega),alpha_eq_tail d (by omega)]
  simp only [young,youngPrefix,show d≠2 by omega,show d≠3 by omega,
    show ¬d ≤ 24 by omega,show ¬d ≤ 25 by omega,ite_false]
  norm_num [K,C]
  ring

theorem coefficient_lower (d : ℕ) (hd : 4 ≤ d) : c ≤ coefficient d := by
  by_cases hs : d ≤ 25
  · interval_cases d  <;> norm_num [coefficient,K,C,c,A,alpha,young,youngPrefix]
  · have hd26 : 26 ≤ d := by omega
    have hr : (26 : ℝ) ≤ d := by exact_mod_cast hd26
    rw [coefficient_tail d hd26]
    have hprod : 0 ≤ ((d : ℝ)-26)*((6767 : ℝ)/14850*((d : ℝ)+26)-(2848 : ℝ)/165) := by
      apply mul_nonneg (by linarith)
      linarith
    norm_num [c]
    nlinarith

theorem coefficient_three : coefficient 3=(-2355275515819 : ℝ)/74323050000 := by
  norm_num [coefficient,K,C,A,alpha,young,youngPrefix]
theorem head_value : head=(447391331 : ℝ)/16980429 := by
  norm_num [head,alpha,K,C,young]
theorem c_sub_coefficient_three_nonneg : 0 ≤ c-coefficient 3 := by
  rw [coefficient_three]; norm_num [c]
theorem c_add_head_nonneg : 0 ≤ c+head := by rw [head_value]; norm_num [c]

def firstCap : ℝ := 2/K^2
def secondCap : ℝ := (49/2)/K^3
def secondLower : ℝ := p^2-firstCap
def thirdLower : ℝ := secondLower*(p-firstCap/p)-secondCap
def residualRatio : ℝ := p-firstCap/p-secondCap/secondLower-
  (C-firstCap-secondCap)/thirdLower

theorem caps_nonneg : 0 ≤ firstCap ∧ 0 ≤ secondCap := by norm_num [firstCap,secondCap,K]
theorem caps_sum_le_budget : firstCap+secondCap ≤ C := by norm_num [firstCap,secondCap,K,C]
theorem secondLower_ge_p : p ≤ secondLower := by norm_num [secondLower,firstCap,p,K]
theorem thirdLower_ge_second : secondLower ≤ thirdLower := by
  norm_num [thirdLower,secondLower,firstCap,secondCap,p,K]
theorem residualRatio_gt_one : 1 < residualRatio := by
  norm_num [residualRatio,thirdLower,secondLower,firstCap,secondCap,p,K,C]
theorem endpoint_value : 1+K*p=(149963 : ℝ)/10000 := by norm_num [K,p]
theorem endpoint_lt_fifteen : (149963 : ℝ)/10000 < 15 := by norm_num

end KLSBelow25.CoupledEnergy.NumericsSub15
#print axioms KLSBelow25.CoupledEnergy.NumericsSub15.coefficient_lower
#print axioms KLSBelow25.CoupledEnergy.NumericsSub15.residualRatio_gt_one
