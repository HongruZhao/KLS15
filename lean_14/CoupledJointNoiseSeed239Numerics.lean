import TripleCreationExactCap
import HarmonicSelectiveBudgetParameters
import TwoRowsHarmonicBudgetParameters
noncomputable section
open scoped BigOperators
namespace KLSBelow25.CoupledEnergy.NumericsJointNoiseSeed239
open KLS.DeterministicBridgeNext
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def K : ℝ := 8051/625
def C : ℝ := 1957/40000
def c : ℝ := 6883/500
def p : ℝ := 523/500
def young (b : ℕ) : ℝ := if b=2 then 16501/20000 else if b=3 then 122451/100000
  else if b  ≤  19 then 225643/100000+(75019/100000)*((b : ℝ)-4) else 27429/2000
def youngPrefix (d : ℕ) : ℝ := if d=2 then 0 else if d=3 then 16501/20000
  else if d  ≤  20 then 16501/20000+122451/100000+((d : ℝ)-4)*(225643/100000)+
    (75019/200000)*((d : ℝ)-4)*((d : ℝ)-5)
  else (16694637/50000)+(27429/2000)*((d : ℝ)-35)
def alpha (d : ℕ) : ℝ :=
  if d=2 then 44449/100000 else
  if d=3 then 2258527/4000000 else
  if d=4 then 48430193/100000000 else
  if d=5 then 22105661/50000000 else
  if d=6 then 20871899/50000000 else
  if d=7 then 20074573/50000000 else
  if d=8 then 7812543/20000000 else
  if d=9 then 2393621/6250000 else
  if d=10 then 18879119/50000000 else
  if d=11 then 7471801/20000000 else
  if d=12 then 18529837/50000000 else
  if d=13 then 4603001/12500000 else
  if d=14 then 7326269/20000000 else
  if d=15 then 36488477/100000000 else
  if d=16 then 9096773/25000000 else
  if d=17 then 7264429/20000000 else
  if d=18 then 36291139/100000000 else
  if d=19 then 9073439/25000000 else
  if d=20 then 36309203/100000000 else
  if d=21 then 36340639/100000000 else
  if d=22 then 36390561/100000000 else
  if d=23 then 36469107/100000000 else
  if d=24 then 4590153/12500000 else
  if d=25 then 36625507/100000000 else
  if d=26 then 18199561/50000000 else
  if d=27 then 9046173/25000000 else
  if d=28 then 35983097/100000000 else
  if d=29 then 178977/500000 else
  if d=30 then 1113219/3125000 else
  if d=31 then 3546787/10000000 else
  if d=32 then 35332711/100000000 else
  if d=33 then 17610669/50000000 else
  if d=34 then 2196189/6250000 else
  35093/100000
def zeta2 (d : ℕ) : ℝ :=
  if d=2 then 126263/1000000 else
  if d=3 then 55143/125000 else
  if d=4 then 933043/1000000 else
  if d=5 then 491393/500000 else
  if d=6 then 992449/1000000 else
  if d=7 then 975921/1000000 else
  if d=8 then 941209/1000000 else
  if d=9 then 993453/1000000 else
  if d=10 then 16272/15625 else
  if d=11 then 1086069/1000000 else
  if d=12 then 56407/50000 else
  if d=13 then 230831/200000 else
  if d=14 then 235617/200000 else
  if d=15 then 240059/200000 else
  if d=16 then 1221069/1000000 else
  if d=17 then 1240631/1000000 else
  if d=18 then 629581/500000 else
  if d=19 then 1276807/1000000 else
  if d=20 then 258737/200000 else
  if d=21 then 126939/100000 else
  if d=22 then 622019/500000 else
  if d=23 then 243551/200000 else
  0
def zeta3 (d : ℕ) : ℝ :=
  if d=2 then 0 else
  if d=3 then 1408773/1000000 else
  if d=4 then 992629/500000 else
  if d=5 then 77159/40000 else
  if d=6 then 1056427/500000 else
  if d=7 then 2409673/1000000 else
  if d=8 then 2763239/1000000 else
  if d=9 then 643527/250000 else
  if d=10 then 598127/250000 else
  if d=11 then 441799/200000 else
  if d=12 then 2015571/1000000 else
  if d=13 then 2318047/1000000 else
  if d=14 then 527303/200000 else
  if d=15 then 1485479/500000 else
  if d=16 then 3320383/1000000 else
  if d=17 then 3684651/1000000 else
  if d=18 then 4062929/1000000 else
  if d=19 then 4455019/1000000 else
  if d=20 then 1215051/250000 else
  if d=21 then 494699/100000 else
  if d=22 then 5030429/1000000 else
  if d=23 then 1277659/250000 else
  0
def A (d : ℕ) : ℝ := if 4 ≤ d ∧ d ≤ 24 then 4/(1-alpha d)-2-4*alpha d/(3*((d : ℝ)-1)*(1-alpha d)) else (if d=3 then 11/3 else 4)/(1-alpha d)-2
def pairGain (b : ℕ) : ℝ := young b-young b/harmonicBudgetDenom (b : ℝ) (zeta2 b)
def tripleGain (b : ℕ) : ℝ := young b-young b/harmonicRatioDenom (tripleHarmonicRatio (b : ℝ)) (zeta3 b)
def pairCharge (b : ℕ) : ℝ := zeta2 b*(b : ℝ)*((b : ℝ)^2+5*(b : ℝ)/3-10/3)/(K*((b : ℝ)+1)*young b)
def tripleCharge (b : ℕ) : ℝ := zeta3 b*TripleCreation.affineRest (TripleCreation.exactCap b) ((b : ℝ)+2)/
  (K^2*((b : ℝ)+2)^2*((b : ℝ)+1)^2*young b)
def coefficient (d : ℕ) : ℝ :=
  (K*alpha (d-1)-A d-K*C/young d)*(d : ℝ)^2-(A d-3)*(d : ℝ)-1-youngPrefix d+
    pairGain (d-1)+tripleGain (d-2)-pairCharge d-tripleCharge d+
    (if d=3 then young 2-pairGain 2 else 0)
def head : ℝ := 64*(1+1/(6*K))^2/(3*(1-alpha 2))-17+4*K*C/young 2-8/(K*young 2)+tripleCharge 2

theorem K_positive : 0<K := by norm_num [K]
theorem C_positive : 0<C := by norm_num [C]
theorem c_positive : 0<c := by norm_num [c]
theorem p_gt_one : 1<p := by norm_num [p]
theorem alpha_two_ge_third : (1:ℝ)/3 ≤ alpha 2 := by norm_num [alpha]
theorem alpha_three_ge_half : (1:ℝ)/2 ≤ alpha 3 := by norm_num [alpha]
theorem young_positive (b : ℕ) (hb : 2 ≤ b) : 0<young b := by
  by_cases hs : b ≤ 19
  · interval_cases b <;> norm_num [young]
  · simp only [young,show b≠2 by omega,show b≠3 by omega,show ¬b ≤ 19 by omega,ite_false]
    norm_num

theorem youngPrefix_eq_sum (d : ℕ) (hd : 2 ≤ d) :
    youngPrefix d=∑ b∈Finset.Icc 2 (d-1),young b := by
  classical
  induction d,hd using Nat.le_induction with
  | base => norm_num [youngPrefix]
  | succ d hd ih =>
    have hs : Finset.Icc 2 d=insert d (Finset.Icc 2 (d-1)) := by
      ext b;simp only [Finset.mem_Icc,Finset.mem_insert];omega
    have hn : d∉Finset.Icc 2 (d-1) := by simp only [Finset.mem_Icc];omega
    simp only [Nat.add_sub_cancel]
    rw [hs,Finset.sum_insert hn,←ih]
    by_cases hh : d ≤ 20
    · interval_cases d <;> norm_num [youngPrefix,young]
    · simp only [youngPrefix,young,show d≠2 by omega,show d≠3 by omega,
        show d+1≠2 by omega,show d+1≠3 by omega,show ¬d ≤ 20 by omega,
        show ¬d+1 ≤ 20 by omega,show ¬d ≤ 19 by omega,ite_false,Nat.cast_add,Nat.cast_one]
      ring

theorem alpha_eq_tail (d : ℕ) (hd : 35 ≤ d) : alpha d=(35093/100000 : ℝ) := by
  simp only [alpha,show d≠2 by omega,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,show d≠20 by omega,show d≠21 by omega,show d≠22 by omega,show d≠23 by omega,show d≠24 by omega,show d≠25 by omega,show d≠26 by omega,show d≠27 by omega,show d≠28 by omega,show d≠29 by omega,show d≠30 by omega,show d≠31 by omega,show d≠32 by omega,show d≠33 by omega,show d≠34 by omega,ite_false]

theorem zeta2_eq_tail (d : ℕ) (hd : 24 ≤ d) : zeta2 d=(0 : ℝ) := by
  simp only [zeta2,show d≠2 by omega,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,show d≠20 by omega,show d≠21 by omega,show d≠22 by omega,show d≠23 by omega,ite_false]

theorem zeta3_eq_tail (d : ℕ) (hd : 24 ≤ d) : zeta3 d=(0 : ℝ) := by
  simp only [zeta3,show d≠2 by omega,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,show d≠20 by omega,show d≠21 by omega,show d≠22 by omega,show d≠23 by omega,ite_false]
theorem alpha_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ alpha d := by
  by_cases hs : d ≤ 34
  · interval_cases d <;> norm_num [alpha]
  · rw [alpha_eq_tail d (by omega)];norm_num
theorem alpha_lt_one (d : ℕ) (hd : 2 ≤ d) : alpha d<1 := by
  by_cases hs : d ≤ 34
  · interval_cases d <;> norm_num [alpha]
  · rw [alpha_eq_tail d (by omega)];norm_num
theorem zeta2_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ zeta2 d := by
  by_cases hs : d ≤ 23
  · interval_cases d <;> norm_num [zeta2]
  · rw [zeta2_eq_tail d (by omega)]
theorem zeta3_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ zeta3 d := by
  by_cases hs : d ≤ 23
  · interval_cases d <;> norm_num [zeta3]
  · rw [zeta3_eq_tail d (by omega)]
theorem zeta2_cap (d : ℕ) (hd : 2 ≤ d) : 2*zeta2 d<(d : ℝ)*((d : ℝ)+1) := by
  by_cases hs : d ≤ 23
  · interval_cases d <;> norm_num [zeta2]
  · rw [zeta2_eq_tail d (by omega)]
    have hh : (2:ℝ) ≤ d := by exact_mod_cast hd
    nlinarith

theorem zeta3_cap (d : ℕ) (hd : 2 ≤ d) : tripleHarmonicRatio (d : ℝ)*zeta3 d<1 := by
  by_cases hs : d ≤ 23
  · interval_cases d <;> norm_num [zeta3,tripleHarmonicRatio,TripleCreation.chargeRatio]
  · rw [zeta3_eq_tail d (by omega)];norm_num

theorem pairGain_eq_zero (d : ℕ) (hd : 24 ≤ d) : pairGain d=0 := by
  rw [pairGain,zeta2_eq_tail d hd]
  simp [harmonicBudgetDenom]
theorem tripleGain_eq_zero (d : ℕ) (hd : 24 ≤ d) : tripleGain d=0 := by
  rw [tripleGain,zeta3_eq_tail d hd]
  simp [harmonicRatioDenom,selectedHarmonicDenom]
theorem pairCharge_eq_zero (d : ℕ) (hd : 24 ≤ d) : pairCharge d=0 := by
  rw [pairCharge,zeta2_eq_tail d hd];simp
theorem tripleCharge_eq_zero (d : ℕ) (hd : 24 ≤ d) : tripleCharge d=0 := by
  rw [tripleCharge,zeta3_eq_tail d hd];simp
theorem coefficient_tail (d : ℕ) (hd : 36 ≤ d) :
    coefficient d=(34707909961392529 : ℝ)/111270881437500000*(d : ℝ)^2-(1931264103 : ℝ)/129814000*(d : ℝ)+(3627869 : ℝ)/25000 := by
  unfold coefficient A
  rw [alpha_eq_tail (d-1) (by omega),alpha_eq_tail d (by omega),
    pairGain_eq_zero (d-1) (by omega),tripleGain_eq_zero (d-2) (by omega),
    pairCharge_eq_zero d (by omega),tripleCharge_eq_zero d (by omega)]
  simp only [young,youngPrefix,show d≠2 by omega,show d≠3 by omega,show ¬(4 ≤ d ∧ d ≤ 24) by omega,
    show ¬d ≤ 19 by omega,show ¬d ≤ 20 by omega,ite_false]
  norm_num [K,C]
  ring

theorem coefficient_lower (d : ℕ) (hd : 4 ≤ d) : c ≤ coefficient d := by
  by_cases hs : d ≤ 35
  · interval_cases d <;> norm_num [coefficient,K,C,c,A,alpha,young,youngPrefix,pairGain,tripleGain,
      pairCharge,tripleCharge,zeta2,zeta3,harmonicBudgetDenom,harmonicRatioDenom,tripleHarmonicRatio,selectedHarmonicDenom,TripleCreation.chargeRatio,
      TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  · have hd36 : 36 ≤ d := by omega
    have hr : (36:ℝ) ≤ d := by exact_mod_cast hd36
    rw [coefficient_tail d hd36]
    have hp : 0 ≤ ((d : ℝ)-36)*((34707909961392529 : ℝ)/111270881437500000*((d : ℝ)+36)-(1931264103 : ℝ)/129814000) := by
      apply mul_nonneg (by linarith)
      linarith
    norm_num [c]
    nlinarith

theorem coefficient_three : coefficient 3=(-6452334428705412006063395269 : ℝ)/287963535858906627562500000 := by
  norm_num [coefficient,K,C,A,alpha,young,youngPrefix,pairGain,tripleGain,pairCharge,tripleCharge,
    zeta2,zeta3,harmonicBudgetDenom,harmonicRatioDenom,tripleHarmonicRatio,selectedHarmonicDenom,TripleCreation.chargeRatio,TripleCreation.affineRest,
    TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
theorem head_value : head=(24771335579546271581653 : ℝ)/1002641278330051610625 := by
  norm_num [head,K,C,alpha,young,pairCharge,tripleCharge,zeta2,zeta3]
theorem c_sub_coefficient_three_nonneg : 0 ≤ c-coefficient 3 := by
  rw [coefficient_three];norm_num [c]
theorem c_add_head_nonneg : 0 ≤ c+head := by rw [head_value];norm_num [c]
def firstCap : ℝ := 2/K^2
def secondCap : ℝ := 24/K^3
def secondLower : ℝ := p^2-firstCap
def thirdLower : ℝ := secondLower*(p-firstCap/p)-secondCap
def residualRatio : ℝ := p-firstCap/p-secondCap/secondLower-(C-firstCap-secondCap)/thirdLower

theorem caps_nonneg : 0 ≤ firstCap ∧ 0 ≤ secondCap := by norm_num [firstCap,secondCap,K]
theorem caps_sum_le_budget : firstCap+secondCap ≤ C := by norm_num [firstCap,secondCap,K,C]
theorem secondLower_ge_p : p ≤ secondLower := by norm_num [secondLower,firstCap,p,K]
theorem thirdLower_ge_second : secondLower ≤ thirdLower := by norm_num [thirdLower,secondLower,firstCap,secondCap,p,K]
theorem residualRatio_gt_one : 1<residualRatio := by
  norm_num [residualRatio,thirdLower,secondLower,firstCap,secondCap,p,K,C]
theorem endpoint_value : 1+K*p=(4523173 : ℝ)/312500 := by norm_num [K,p]
theorem auxiliary_endpoint_lt_fifteen : (4523173 : ℝ)/312500<(15:ℝ) := by norm_num
end KLSBelow25.CoupledEnergy.NumericsJointNoiseSeed239
#print axioms KLSBelow25.CoupledEnergy.NumericsJointNoiseSeed239.coefficient_lower
#print axioms KLSBelow25.CoupledEnergy.NumericsJointNoiseSeed239.zeta3_cap
#print axioms KLSBelow25.CoupledEnergy.NumericsJointNoiseSeed239.residualRatio_gt_one
