import KLSConstantImprovement.QuarticM32FiniteCostGrid20261020
import KLSConstantImprovement.TripleCreationExactCapMemo
import KLSConstantImprovement.TriplePositiveEnergyFirstCostTail
import KLSConstantImprovement.ParameterizedWeightedBudget
import KLSConstantImprovement.RawCubicWeightedBudget
import KLSConstantImprovement.PositiveEnergyWeightTailPrefix

/-! Exact rational generator profile for the raw401.3023465 cubic/quartic head.
This file proves scalar conditions only. Degrees3/4 are paid by the same-test
quartic support in the separate all-rank wrapper. -/
noncomputable section
open Set
open scoped BigOperators
namespace KLSConstantImprovement.QuarticM32Profile20261020Data
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def K : ℝ := 122144150200807/10000000000000
def C : ℝ := 702609291531669/5000000000000000
def c : ℝ := 526963084307017/20000000000000
def p : ℝ := 128409800000000/122144150200807
def tau : ℝ := 1/2
def alphaTail : ℝ := 8347532273131/20000000000000
def youngTail : ℝ := 567235711520317/25000000000000
def tTail : ℝ := 16487388560167/12500000000000
def tail_J : ℝ := -3435837764624070541203725276229147708791744491829027593526996288488475427110830627235017543603778073259538569078159322080577412337766024239220980309358879685131204198970132990089491235652629183053209602669019331826992301550539121769167403812872648070303743970329037335652480278870888047476452008668776176081443221916917987754845007675765706047685288797242414357873762416828946003011063292506580174253369111829197160409/6363080889590404060826795016870616927584069144738727872456637970209675448850828033495383609790287322510229614570003057391785329007185649945160051695440562514578377028319451963689601029121901570263391472132057056135715350476640242094704400130409094427224592710118225110939241602733084268395767260911079522487928294733209223945713647358105769756325855938715947551231287437902090714477642833147571523070900000000000000
def tail_q : ℝ := 29623793312092637060518568679936872624986487716665163/188848452057659087688579927800000000000000000000000000
def tail_b : ℝ := -24378702447823470575602802051038407350418155219484013631390893583809/1334407632026011968955867976528288063975400000000000000000000000000
def tail_a : ℝ := 877114011626773437457798687945696536499961/1646732255123101005677375340000000000000
def tail_z : ℝ := -10252326832706983/20000000000000
def tail_J_upper : ℝ := -5399644958507/10000000000

def alpha (d : ℕ) : ℝ :=
  if d=2 then 1/3 else
  if d=3 then 24724140004971/50000000000000 else
  if d=4 then 23208570349273/50000000000000 else
  if d=5 then 8897796536719/20000000000000 else
  if d=6 then 43445526853969/100000000000000 else
  if d=7 then 21454036847499/50000000000000 else
  if d=8 then 41711757634379/100000000000000 else
  if d=9 then 1276211093843/3125000000000 else
  if d=10 then 20174999447269/50000000000000 else
  if d=11 then 10021927507097/25000000000000 else
  if d=12 then 19980414351471/50000000000000 else
  if d=13 then 19957642282881/50000000000000 else
  if d=14 then 39918352219317/100000000000000 else
  if d=15 then 39950123731977/100000000000000 else
  if d=16 then 39998240094149/100000000000000 else
  if d=17 then 20027655436007/50000000000000 else
  if d=18 then 40120336653817/100000000000000 else
  if d=19 then 20095534968541/50000000000000 else
  if d=20 then 20133437734939/50000000000000 else
  if d=21 then 4034843395603/10000000000000 else
  if d=22 then 10109384148453/25000000000000 else
  if d=23 then 810739799393/2000000000000 else
  if d=24 then 20325220819999/50000000000000 else
  if d=25 then 40783498742711/100000000000000 else
  if d=26 then 40942449853857/100000000000000 else
  if d=27 then 1645368717449/4000000000000 else
  if d=28 then 20618258463193/50000000000000 else
  if d=29 then 8238662236523/20000000000000 else
  if d=30 then 41147561933571/100000000000000 else
  if d=31 then 41101368037837/100000000000000 else
  if d=32 then 43334275391403/100000000000000 else
  if d=33 then 8642495915899/20000000000000 else
  if d=34 then 21551804594659/50000000000000 else
  if d=35 then 8601511366129/20000000000000 else
  if d=36 then 42921061208959/100000000000000 else
  if d=37 then 10710411360813/25000000000000 else
  if d=38 then 85534823171/200000000000 else
  if d=39 then 21348692622077/50000000000000 else
  if d=40 then 213154441107/500000000000 else
  if d=41 then 42567375477447/100000000000000 else
  if d=42 then 8501285832589/20000000000000 else
  if d=43 then 10611936289459/25000000000000 else
  if d=44 then 10597779053483/25000000000000 else
  if d=45 then 42336415215163/100000000000000 else
  if d=46 then 5285447497169/12500000000000 else
  if d=47 then 42232596955241/100000000000000 else
  if d=48 then 42183494588123/100000000000000 else
  if d=49 then 21068166838533/50000000000000 else
  if d=50 then 42091198846833/100000000000000 else
  if d=51 then 42048191434409/100000000000000 else
  if d=52 then 4200742369061/10000000000000 else
  if d=53 then 41969014095011/100000000000000 else
  if d=54 then 10483270872801/25000000000000 else
  if d=55 then 10474938008313/25000000000000 else
  if d=56 then 41869135633079/100000000000000 else
  if d=57 then 41841343687007/100000000000000 else
  if d=58 then 10454119035609/25000000000000 else
  if d=59 then 20897340389713/50000000000000 else
  if d=60 then 20888088415413/50000000000000 else
  if d=61 then 41761184177999/100000000000000 else
  if d=62 then 20874961535823/50000000000000 else
  if d=63 then 8348382435197/20000000000000 else
  alphaTail

def young (d : ℕ) : ℝ :=
  if d=2 then 95193002405431/100000000000000 else
  if d=3 then 60361814752637/10000000000000 else
  if d=4 then 470159457903553/50000000000000 else
  if d=5 then 25554367557219/2500000000000 else
  if d=6 then 1102479731580301/100000000000000 else
  if d=7 then 236553062568137/20000000000000 else
  if d=8 then 1289045379687367/100000000000000 else
  if d=9 then 342542283954801/25000000000000 else
  if d=10 then 1423515181452149/100000000000000 else
  if d=11 then 291069320793913/20000000000000 else
  if d=12 then 294134663816097/20000000000000 else
  if d=13 then 368578410409753/25000000000000 else
  if d=14 then 1469572893548997/100000000000000 else
  if d=15 then 58346416357919/4000000000000 else
  if d=16 then 289522585659173/20000000000000 else
  if d=17 then 358078859792039/25000000000000 else
  if d=18 then 282652980140789/20000000000000 else
  if d=19 then 1391207860065547/100000000000000 else
  if d=20 then 1366859091679337/100000000000000 else
  if d=21 then 1340887630262589/100000000000000 else
  if d=22 then 10511216169161/800000000000 else
  if d=23 then 257290325235787/20000000000000 else
  if d=24 then 629434388586049/50000000000000 else
  if d=25 then 1232730784495239/100000000000000 else
  if d=26 then 241565644342809/20000000000000 else
  if d=27 then 59227088301033/5000000000000 else
  if d=28 then 1868227441031/160000000000 else
  if d=29 then 1154889676470491/100000000000000 else
  if d=30 then 1140451378078667/100000000000000 else
  if d=31 then 561957391821949/50000000000000 else
  youngTail

def t (d : ℕ) : ℝ :=
  if d=2 then 1 else
  if d=3 then 495074302387353/100000000000000 else
  if d=4 then 256475451648929/50000000000000 else
  if d=5 then 431455417410153/100000000000000 else
  if d=6 then 375828697065803/100000000000000 else
  if d=7 then 167508622498929/50000000000000 else
  if d=8 then 62143078345047/20000000000000 else
  if d=9 then 290967381044679/100000000000000 else
  if d=10 then 273378191508407/100000000000000 else
  if d=11 then 4029599321999/1562500000000 else
  if d=12 then 244317269912887/100000000000000 else
  if d=13 then 232405484198257/100000000000000 else
  if d=14 then 110960691530321/50000000000000 else
  if d=15 then 42529996329769/20000000000000 else
  if d=16 then 204404356722221/100000000000000 else
  if d=17 then 2462815971153/1250000000000 else
  if d=18 then 190378247442463/100000000000000 else
  if d=19 then 92174058101813/50000000000000 else
  if d=20 then 35767508206187/20000000000000 else
  if d=21 then 34752780389999/20000000000000 else
  if d=22 then 6762262568989/4000000000000 else
  if d=23 then 82327279289743/50000000000000 else
  if d=24 then 160504653539363/100000000000000 else
  if d=25 then 156559758366081/100000000000000 else
  if d=26 then 19097158953083/12500000000000 else
  if d=27 then 149117946189779/100000000000000 else
  if d=28 then 145991502813431/100000000000000 else
  if d=29 then 143530679528699/100000000000000 else
  if d=30 then 141197070597487/100000000000000 else
  if d=31 then 17372454819443/12500000000000 else
  tTail

def theta (d : ℕ) : ℝ := if 3 ≤ d ∧ d ≤ 32 then 1 else 0
def lambda (d : ℕ) : ℝ := if 2 ≤ d ∧ d ≤ 31 then 1 else 0

def zeta (d : ℕ) : ℝ :=
  if d=3 then 142857/100000 else
  if d=4 then 92256280166883/50000000000000 else
  if d=5 then 208323806383/208000000000 else
  if d=6 then 148419367937533/200000000000000 else
  if d=7 then 143702293408233/237500000000000 else
  if d=8 then 13602854301207/27500000000000 else
  if d=9 then 200642343932019/500000000000000 else
  if d=10 then 44869228225019/140000000000000 else
  if d=11 then 191782300934939/775000000000000 else
  if d=12 then 152362441384517/850000000000000 else
  if d=13 then 535605283941/4625000000000 else
  if d=14 then 1413368152147/25000000000000 else
  if d=15 then 24149122319/21500000000000 else
  if d=16 then 0 else
  if d=17 then 0 else
  if d=18 then 0 else
  if d=19 then 0 else
  if d=20 then 0 else
  if d=21 then 0 else
  if d=22 then 0 else
  if d=23 then 0 else
  if d=24 then 0 else
  if d=25 then 0 else
  if d=26 then 0 else
  if d=27 then 0 else
  if d=28 then 0 else
  if d=29 then 0 else
  if d=30 then 0 else
  if d=31 then 0 else
  0

def profile : Parameters where
  K := K
  C := C
  c := c
  young := young
  t := t
  alpha := alpha
  theta := theta
  lambda := lambda
  zeta := zeta

theorem alpha_eq_tail (d : ℕ) (hd : 64 ≤ d) : alpha d=alphaTail := by
  simp only [alpha,show d≠2 by omega,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,show d≠20 by omega,show d≠21 by omega,show d≠22 by omega,show d≠23 by omega,show d≠24 by omega,show d≠25 by omega,show d≠26 by omega,show d≠27 by omega,show d≠28 by omega,show d≠29 by omega,show d≠30 by omega,show d≠31 by omega,show d≠32 by omega,show d≠33 by omega,show d≠34 by omega,show d≠35 by omega,show d≠36 by omega,show d≠37 by omega,show d≠38 by omega,show d≠39 by omega,show d≠40 by omega,show d≠41 by omega,show d≠42 by omega,show d≠43 by omega,show d≠44 by omega,show d≠45 by omega,show d≠46 by omega,show d≠47 by omega,show d≠48 by omega,show d≠49 by omega,show d≠50 by omega,show d≠51 by omega,show d≠52 by omega,show d≠53 by omega,show d≠54 by omega,show d≠55 by omega,show d≠56 by omega,show d≠57 by omega,show d≠58 by omega,show d≠59 by omega,show d≠60 by omega,show d≠61 by omega,show d≠62 by omega,show d≠63 by omega,ite_false]

theorem young_eq_tail (d : ℕ) (hd : 32 ≤ d) : young d=youngTail := by
  simp only [young,show d≠2 by omega,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,show d≠20 by omega,show d≠21 by omega,show d≠22 by omega,show d≠23 by omega,show d≠24 by omega,show d≠25 by omega,show d≠26 by omega,show d≠27 by omega,show d≠28 by omega,show d≠29 by omega,show d≠30 by omega,show d≠31 by omega,ite_false]

theorem t_eq_tail (d : ℕ) (hd : 32 ≤ d) : t d=tTail := by
  simp only [t,show d≠2 by omega,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,show d≠20 by omega,show d≠21 by omega,show d≠22 by omega,show d≠23 by omega,show d≠24 by omega,show d≠25 by omega,show d≠26 by omega,show d≠27 by omega,show d≠28 by omega,show d≠29 by omega,show d≠30 by omega,show d≠31 by omega,ite_false]

theorem alpha_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ alpha d := by
  by_cases hs:d ≤ 63
  · interval_cases d <;> norm_num [alpha,alphaTail]
  · rw [alpha_eq_tail d (by omega)];norm_num [alphaTail]

theorem alpha_lt_one (d : ℕ) (hd : 2 ≤ d) : alpha d<1 := by
  by_cases hs:d ≤ 63
  · interval_cases d <;> norm_num [alpha,alphaTail]
  · rw [alpha_eq_tail d (by omega)];norm_num [alphaTail]

theorem young_positive (d : ℕ) (hd : 2 ≤ d) : 0<young d := by
  by_cases hs:d ≤ 31
  · interval_cases d <;> norm_num [young,youngTail]
  · rw [young_eq_tail d (by omega)];norm_num [youngTail]

theorem t_positive (d : ℕ) (hd : 2 ≤ d) : 0<t d := by
  by_cases hs:d ≤ 31
  · interval_cases d <;> norm_num [t,tTail]
  · rw [t_eq_tail d (by omega)];norm_num [tTail]

theorem theta_nonneg (d : ℕ) (_hd : 3 ≤ d) : 0 ≤ theta d := by unfold theta;split_ifs <;> norm_num
theorem theta_le_one (d : ℕ) (_hd : 3 ≤ d) : theta d ≤ 1 := by unfold theta;split_ifs <;> norm_num
theorem lambda_nonneg (d : ℕ) (_hd : 2 ≤ d) : 0 ≤ lambda d := by unfold lambda;split_ifs <;> norm_num
theorem lambda_le_one (d : ℕ) (_hd : 2 ≤ d) : lambda d ≤ 1 := by unfold lambda;split_ifs <;> norm_num
theorem theta_eq_zero (d : ℕ) (hd : 33 ≤ d) : theta d=0 := by simp [theta,show ¬(3 ≤ d ∧ d ≤ 32) by omega]
theorem lambda_eq_zero (d : ℕ) (hd : 32 ≤ d) : lambda d=0 := by simp [lambda,show ¬(2 ≤ d ∧ d ≤ 31) by omega]
theorem zeta_eq_zero (d : ℕ) (hd : 32 ≤ d) : zeta d=0 := by
  simp only [zeta,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,show d≠20 by omega,show d≠21 by omega,show d≠22 by omega,show d≠23 by omega,show d≠24 by omega,show d≠25 by omega,show d≠26 by omega,show d≠27 by omega,show d≠28 by omega,show d≠29 by omega,show d≠30 by omega,show d≠31 by omega,ite_false]

theorem zeta_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ zeta d := by
  by_cases hs:d ≤ 31
  · interval_cases d <;> norm_num [zeta]
  · rw [zeta_eq_zero d (by omega)]

theorem zeta_cap (d : ℕ) (hd : 2 ≤ d) : tripleHarmonicRatio (d : ℝ)*zeta d<1 := by
  by_cases hs:d ≤ 31
  · interval_cases d <;> norm_num [tripleHarmonicRatio,TripleCreation.chargeRatio,zeta]
  · rw [zeta_eq_zero d (by omega)];norm_num

theorem lambda_boundary (d : ℕ) (hd : 2 ≤ d) (he : lambda d=1) : theta (d+1)=1 := by
  by_cases hs:d ≤ 31
  · have hh:3 ≤ d+1 ∧ d+1 ≤ 32:=by omega
    simp [theta,hh]
  · rw [lambda_eq_zero d (by omega)] at he
    norm_num at he

theorem t_floor (d : ℕ) (hd : 2 ≤ d) : tau ≤ t d := by
  by_cases hs:d ≤ 31
  · interval_cases d <;> norm_num [tau,t,tTail]
  · rw [t_eq_tail d (by omega)];norm_num [tau,tTail]

theorem terminal_payment (d : ℕ) (hd : 3 ≤ d) :
    ((d : ℝ)+PositiveEnergyWeightedDrift.kappa K young t lambda d)*(1-alpha d) ≤ (d : ℝ) := by
  by_cases hs:d ≤ 31
  · interval_cases d <;> norm_num [PositiveEnergyWeightedDrift.kappa,K,young,t,tTail,lambda,alpha,alphaTail,youngTail]
  · rw [show PositiveEnergyWeightedDrift.kappa K young t lambda d=0 by simp [PositiveEnergyWeightedDrift.kappa,lambda_eq_zero d (by omega)]]
    have ha:=alpha_nonneg d (by omega)
    have hr:0 ≤ (d : ℝ):=Nat.cast_nonneg _
    nlinarith

theorem sum_interval_two (f : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 2 N,f d)=∑ j ∈ Finset.range (N-1),f (j+2) := by
  classical
  apply Finset.sum_bij (fun d _=>d-2)
  · intro d hd
    simp only [Finset.mem_Icc,Finset.mem_range] at hd ⊢
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_Icc] at ha hb
    omega
  · intro j hj
    refine ⟨j+2,?_,by omega⟩
    simp only [Finset.mem_Icc,Finset.mem_range] at hj ⊢
    omega
  · intro d hd
    have hs:d-2+2=d:=by have:=(Finset.mem_Icc.mp hd).1;omega
    rw [hs]


/- Exact table evaluations reused from the independent finite-grid certificate. -/
@[simp] theorem young_grid_eval_2 : young 2=(95193002405431/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_2
@[simp] theorem young_grid_eval_3 : young 3=(60361814752637/10000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_3
@[simp] theorem young_grid_eval_4 : young 4=(470159457903553/50000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_4
@[simp] theorem young_grid_eval_5 : young 5=(25554367557219/2500000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_5
@[simp] theorem young_grid_eval_6 : young 6=(1102479731580301/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_6
@[simp] theorem young_grid_eval_7 : young 7=(236553062568137/20000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_7
@[simp] theorem young_grid_eval_8 : young 8=(1289045379687367/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_8
@[simp] theorem young_grid_eval_9 : young 9=(342542283954801/25000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_9
@[simp] theorem young_grid_eval_10 : young 10=(1423515181452149/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_10
@[simp] theorem young_grid_eval_11 : young 11=(291069320793913/20000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_11
@[simp] theorem young_grid_eval_12 : young 12=(294134663816097/20000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_12
@[simp] theorem young_grid_eval_13 : young 13=(368578410409753/25000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_13
@[simp] theorem young_grid_eval_14 : young 14=(1469572893548997/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_14
@[simp] theorem young_grid_eval_15 : young 15=(58346416357919/4000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_15
@[simp] theorem young_grid_eval_16 : young 16=(289522585659173/20000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_16
@[simp] theorem young_grid_eval_17 : young 17=(358078859792039/25000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_17
@[simp] theorem young_grid_eval_18 : young 18=(282652980140789/20000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_18
@[simp] theorem young_grid_eval_19 : young 19=(1391207860065547/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_19
@[simp] theorem young_grid_eval_20 : young 20=(1366859091679337/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_20
@[simp] theorem young_grid_eval_21 : young 21=(1340887630262589/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_21
@[simp] theorem young_grid_eval_22 : young 22=(10511216169161/800000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_22
@[simp] theorem young_grid_eval_23 : young 23=(257290325235787/20000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_23
@[simp] theorem young_grid_eval_24 : young 24=(629434388586049/50000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_24
@[simp] theorem young_grid_eval_25 : young 25=(1232730784495239/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_25
@[simp] theorem young_grid_eval_26 : young 26=(241565644342809/20000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_26
@[simp] theorem young_grid_eval_27 : young 27=(59227088301033/5000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_27
@[simp] theorem young_grid_eval_28 : young 28=(1868227441031/160000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_28
@[simp] theorem young_grid_eval_29 : young 29=(1154889676470491/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_29
@[simp] theorem young_grid_eval_30 : young 30=(1140451378078667/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_30
@[simp] theorem young_grid_eval_31 : young 31=(561957391821949/50000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.young_eval_31
@[simp] theorem t_grid_eval_2 : t 2=(1 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_2
@[simp] theorem t_grid_eval_3 : t 3=(495074302387353/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_3
@[simp] theorem t_grid_eval_4 : t 4=(256475451648929/50000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_4
@[simp] theorem t_grid_eval_5 : t 5=(431455417410153/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_5
@[simp] theorem t_grid_eval_6 : t 6=(375828697065803/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_6
@[simp] theorem t_grid_eval_7 : t 7=(167508622498929/50000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_7
@[simp] theorem t_grid_eval_8 : t 8=(62143078345047/20000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_8
@[simp] theorem t_grid_eval_9 : t 9=(290967381044679/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_9
@[simp] theorem t_grid_eval_10 : t 10=(273378191508407/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_10
@[simp] theorem t_grid_eval_11 : t 11=(4029599321999/1562500000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_11
@[simp] theorem t_grid_eval_12 : t 12=(244317269912887/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_12
@[simp] theorem t_grid_eval_13 : t 13=(232405484198257/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_13
@[simp] theorem t_grid_eval_14 : t 14=(110960691530321/50000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_14
@[simp] theorem t_grid_eval_15 : t 15=(42529996329769/20000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_15
@[simp] theorem t_grid_eval_16 : t 16=(204404356722221/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_16
@[simp] theorem t_grid_eval_17 : t 17=(2462815971153/1250000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_17
@[simp] theorem t_grid_eval_18 : t 18=(190378247442463/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_18
@[simp] theorem t_grid_eval_19 : t 19=(92174058101813/50000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_19
@[simp] theorem t_grid_eval_20 : t 20=(35767508206187/20000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_20
@[simp] theorem t_grid_eval_21 : t 21=(34752780389999/20000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_21
@[simp] theorem t_grid_eval_22 : t 22=(6762262568989/4000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_22
@[simp] theorem t_grid_eval_23 : t 23=(82327279289743/50000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_23
@[simp] theorem t_grid_eval_24 : t 24=(160504653539363/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_24
@[simp] theorem t_grid_eval_25 : t 25=(156559758366081/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_25
@[simp] theorem t_grid_eval_26 : t 26=(19097158953083/12500000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_26
@[simp] theorem t_grid_eval_27 : t 27=(149117946189779/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_27
@[simp] theorem t_grid_eval_28 : t 28=(145991502813431/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_28
@[simp] theorem t_grid_eval_29 : t 29=(143530679528699/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_29
@[simp] theorem t_grid_eval_30 : t 30=(141197070597487/100000000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_30
@[simp] theorem t_grid_eval_31 : t 31=(17372454819443/12500000000000 : ℝ) := QuarticM32FiniteCostGrid20261020.t_eval_31

def interceptGridOne (b : ℕ) : ℝ :=
  if b=2 then 9519300241 else
  if b=3 then 12192475849 else
  if b=4 then 18331557851 else
  if b=5 then 23691316902 else
  if b=6 then 29334634109 else
  if b=7 then 35304609853 else
  if b=8 then 41486370294 else
  if b=9 then 47090128485 else
  if b=10 then 52071278020 else
  if b=11 then 56431890295 else
  if b=12 then 60195225643 else
  if b=13 then 63437127860 else
  if b=14 then 66220427851 else
  if b=15 then 68594429101 else
  if b=16 then 70821040780 else
  if b=17 then 72697039484 else
  if b=18 then 74234578777 else
  if b=19 then 75466345343 else
  if b=20 then 76430210559 else
  if b=21 then 77167214549 else
  if b=22 then 77719668986 else
  if b=23 then 78130337677 else
  if b=24 then 78431917668 else
  if b=25 then 78738674444 else
  if b=26 then 79058109160 else
  if b=27 then 79436566577 else
  if b=28 then 79980144608 else
  if b=29 then 80462914289 else
  if b=30 then 80770186893 else
  if b=31 then 80869024796 else
  0

def interceptGridTwo (b : ℕ) : ℝ :=
  if b=2 then 226894284609 else
  if b=3 then 45830349811 else
  if b=4 then 44233138718 else
  if b=5 then 52588118136 else
  if b=6 then 60371729562 else
  if b=7 then 67726150817 else
  if b=8 then 73023187989 else
  if b=9 then 77979285443 else
  if b=10 then 82996483135 else
  if b=11 then 87979546196 else
  if b=12 then 92868704979 else
  if b=13 then 97628627565 else
  if b=14 then 102240839292 else
  if b=15 then 106698473637 else
  if b=16 then 111002665622 else
  if b=17 then 115159987219 else
  if b=18 then 119180782289 else
  if b=19 then 123079253144 else
  if b=20 then 126871731350 else
  if b=21 then 130576191063 else
  if b=22 then 134212052427 else
  if b=23 then 137800183953 else
  if b=24 then 141363056837 else
  if b=25 then 144925035001 else
  if b=26 then 148513114677 else
  if b=27 then 152157597664 else
  if b=28 then 155416089455 else
  if b=29 then 158080687247 else
  if b=30 then 160693337085 else
  if b=31 then 163257213047 else
  0

def tail_intercept_expression : ℝ :=
  PositiveEnergyWeightTail.ratioPrefix young t 32+
    (∑ b ∈ Finset.Icc 2 31,youngTail/t b)-62*(youngTail/tTail)

theorem tail_intercept_upper : tail_intercept_expression ≤ tail_J_upper := by
  have h1 (j : ℕ) (hj : j ∈ Finset.Icc 2 31) :
      young j/t j ≤ interceptGridOne j/10000000000 := by
    have hlo : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have hhi : j ≤ 31 := (Finset.mem_Icc.mp hj).2
    interval_cases j <;> norm_num [interceptGridOne]
  have h2 (j : ℕ) (hj : j ∈ Finset.Icc 2 31) :
      youngTail/t j ≤ interceptGridTwo j/10000000000 := by
    have hlo : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have hhi : j ≤ 31 := (Finset.mem_Icc.mp hj).2
    interval_cases j <;> norm_num [interceptGridTwo,youngTail]
  have hs1 := Finset.sum_le_sum h1
  have hs2 := Finset.sum_le_sum h2
  have hn : -62*(youngTail/tTail) ≤ (-10665307603420/10000000000 : ℝ) := by
    norm_num [youngTail,tTail]
  have hg : (∑ j ∈ Finset.Icc 2 31,interceptGridOne j/10000000000)+
      (∑ j ∈ Finset.Icc 2 31,interceptGridTwo j/10000000000)+
        (-10665307603420/10000000000 : ℝ)=tail_J_upper := by
    norm_num [sum_interval_two,Finset.sum_range_succ,interceptGridOne,interceptGridTwo,tail_J_upper]
  unfold tail_intercept_expression PositiveEnergyWeightTail.ratioPrefix
  linarith only [hs1,hs2,hn,hg]

theorem first_cost_tail_upper (d : ℕ) (hd : 65 ≤ d) :
    PositiveEnergyWeightedDrift.firstCost young t theta lambda d ≤
      (youngTail/tTail)*(d : ℝ)+tail_J_upper := by
  have hh:=PositiveEnergyWeightTailPrefix.firstCost_tail young t theta lambda youngTail tTail
    (by norm_num [tTail]) 32 32 (by norm_num) (by norm_num) (by norm_num)
    young_eq_tail (fun j hj=>t_eq_tail j (by omega)) d (by omega)
    (theta_eq_zero d (by omega)) (lambda_eq_zero (d-1) (by omega))
  have he : PositiveEnergyWeightedDrift.firstCost young t theta lambda d=
      (youngTail/tTail)*(d : ℝ)+tail_intercept_expression := by
    convert hh using 1
    norm_num only [tail_intercept_expression,PositiveEnergyWeightTailPrefix.ratioPrefix]
  rw [he]
  exact add_le_add (le_refl _) tail_intercept_upper

theorem raw_first_cost_tail_upper (d : ℕ) (hd : 65 ≤ d) :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta d ≤
      (youngTail/tTail)*(d : ℝ)+tail_J_upper := by
  rw [TriplePositiveEnergyFirstCostTail.rawFirstCost_eq_of_zero young t theta lambda zeta d
    (by omega) (zeta_eq_zero (d-2) (by omega))]
  exact first_cost_tail_upper d hd

theorem tail_noise_loss (d : ℕ) (hd : 65 ≤ d) :
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda d=generalResidualGeneratorLoss alphaTail d := by
  have hd3:3 ≤ d:=by omega
  have hd2:d≠2:=by omega
  have hr:(65:ℝ) ≤ d:=by exact_mod_cast hd
  have hm:0<(d : ℝ)-1:=by linarith
  have hdelta:0<1-alphaTail:=by norm_num [alphaTail]
  have hlo:2 ≤ ((d : ℝ)+1)*(1-alphaTail):=by norm_num [alphaTail];nlinarith [hr]
  have hdiff:
      (SignedRowNoiseHigh.highLeading (d : ℝ)/(1-alphaTail)-SignedRowNoiseHigh.highPositive (d : ℝ))-
      (PairProjection.leadingNoiseCoefficient (d : ℝ)/(1-alphaTail)-PairProjection.positiveNoiseCoefficient (d : ℝ))=
      (4*(d : ℝ)/(3*((d : ℝ)-1)))*(2/(1-alphaTail)-((d : ℝ)+1)) := by
    unfold SignedRowNoiseHigh.highLeading SignedRowNoiseHigh.highPositive PairProjection.leadingNoiseCoefficient PairProjection.positiveNoiseCoefficient
    field_simp
    ring
  have hn:2/(1-alphaTail)-((d : ℝ)+1) ≤ 0 :=
    sub_nonpos.mpr ((div_le_iff₀ hdelta).mpr hlo)
  have hneg:=mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 4*(d : ℝ)/(3*((d : ℝ)-1))) hn
  rw [←hdiff] at hneg
  have hmax: SignedRowNoiseHigh.highLeading (d : ℝ)/(1-alphaTail)-SignedRowNoiseHigh.highPositive (d : ℝ) ≤ 
      PairProjection.leadingNoiseCoefficient (d : ℝ)/(1-alphaTail)-PairProjection.positiveNoiseCoefficient (d : ℝ) := by linarith
  have hg:PositiveEnergyWeightedGenerator.gamma K t theta d=1:=by simp [PositiveEnergyWeightedGenerator.gamma,theta_eq_zero (d+1) (by omega)]
  have hk:PositiveEnergyWeightedDrift.kappa K young t lambda d=0:=by simp [PositiveEnergyWeightedDrift.kappa,lambda_eq_zero d (by omega)]
  rw [PositiveEnergyWeightedGenerator.generatorLoss,alpha_eq_tail d (by omega),hg,hk]
  simp only [PositiveEnergyWeightedGenerator.degreeLoss,hd2,ite_false,SignedRowReservedNoise.reservedNoiseLoss,one_pow,one_mul,zero_mul,mul_zero,sub_zero,max_eq_left hmax]
  rw [generalResidualGeneratorLoss_eq d hd3 (by norm_num [alphaTail])]

theorem coefficient_finite (d : ℕ) (hd : 5 ≤ d) (hD : d<65) : c ≤ coefficient profile d := by
  exact QuarticM32FiniteCostGrid20261020.coefficient_finite_grid d hd hD

theorem coefficient_tail_lower (d : ℕ) (hd : 65 ≤ d) :
    tail_q*(d : ℝ)^3+tail_b*(d : ℝ)^2+tail_a*(d : ℝ)+tail_z ≤
      ((d : ℝ)-1)*(coefficient profile d-c) := by
  have hr : (65 : ℝ) ≤ d := by exact_mod_cast hd
  have hm : (d : ℝ)-1≠0 := by linarith
  let lowerValue : ℝ := K*alphaTail*(d : ℝ)^2-
    generalResidualGeneratorLoss alphaTail d-1-(K*C/youngTail)*(d : ℝ)^2-
      ((youngTail/tTail)*(d : ℝ)+tail_J_upper)
  have hbound : lowerValue ≤ coefficient profile d := by
    have hf := raw_first_cost_tail_upper d hd
    change lowerValue ≤ TriplePositiveEnergyWeightedGenerator.coefficient K C young t alpha theta lambda zeta d
    unfold TriplePositiveEnergyWeightedGenerator.coefficient PositiveEnergyWeightedGenerator.incoming
      TriplePositiveEnergyWeightedGenerator.cost
    rw [t_eq_tail d (by omega),t_eq_tail (d-1) (by omega),
      alpha_eq_tail (d-1) (by omega),tail_noise_loss d hd,young_eq_tail d (by omega),
      ite_eq_left (by omega : 3 ≤ d)]
    rw [show tripleHarmonicNeighborCharge K young zeta d=0 by
      simp [tripleHarmonicNeighborCharge,zeta_eq_zero d (by omega)]]
    have ht : tTail≠0 := by norm_num [tTail]
    simp only [div_self ht,mul_one,mul_zero,add_zero]
    dsimp only [lowerValue]
    linarith only [hf]
  have hid : ((d : ℝ)-1)*(lowerValue-c)=
      tail_q*(d : ℝ)^3+tail_b*(d : ℝ)^2+tail_a*(d : ℝ)+tail_z := by
    dsimp only [lowerValue]
    norm_num [generalResidualGeneratorLoss,generalResidualA,K,C,c,alphaTail,
      youngTail,tTail,tail_J_upper,tail_q,tail_b,tail_a,tail_z]
    field_simp [hm] <;> ring
  rw [←hid]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hbound c) (by linarith)

theorem tail_Taylor_positive :
    0 < tail_q*(65 : ℝ)^3+tail_b*65^2+tail_a*65+tail_z ∧
      0 < 3*tail_q*65^2+2*tail_b*65+tail_a ∧
      0 < 3*tail_q*65+tail_b ∧ 0 < tail_q := by
  norm_num [tail_q,tail_b,tail_a,tail_z]

theorem coefficient_lower (d : ℕ) (hd : 5 ≤ d) : c ≤ coefficient profile d := by
  by_cases hs:d<65
  · exact coefficient_finite d hd hs
  · have hdt : 65 ≤ d := by omega
    have hr : (65 : ℝ) ≤ d := by exact_mod_cast hdt
    have hp:=ParameterizedWeightedBudget.cubic_nonneg_on_tail tail_q tail_b tail_a tail_z 65 d hr
      (by norm_num [tail_q]) (by norm_num [tail_q,tail_b]) (by norm_num [tail_q,tail_b,tail_a])
      (by norm_num [tail_q,tail_b,tail_a,tail_z])
    have hn : 0 ≤ ((d : ℝ)-1)*(coefficient profile d-c) :=
      hp.trans (coefficient_tail_lower d hdt)
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by linarith : 0 < (d : ℝ)-1)).mp hn)

theorem head_value : head profile=(94174174361049790445511055314474915813400312200560767283/3622966367104825134590610436366014697278875000000000000 : ℝ) := by
  norm_num [head,profile,TriplePositiveEnergyWeightedGenerator.head,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]
theorem coefficient_three : coefficient profile 3=(-1445786490967231559404784587101437816741268003461552742690748580421931254680682155198711186822003579783/27894870310636598042116346242066571263546189708637297404582822744742955455468710780965000000000000000 : ℝ) := by
  norm_num [coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]

theorem coefficient_four : coefficient profile 4=(-1164199780918655309220569774698543276122351116181922833544108979148699153285937740887195321762263966970147743235277439335579077/382497339595263790256251520777200288798632586071696338286107162305279249633068292794941668065148317937500000000000000000000000 : ℝ) := by
  norm_num [sum_interval_two,Finset.sum_range_succ,coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]


end KLSConstantImprovement.QuarticM32Profile20261020Data
#print axioms KLSConstantImprovement.QuarticM32Profile20261020Data.coefficient_lower
#print axioms KLSConstantImprovement.QuarticM32Profile20261020Data.head_value
#print axioms KLSConstantImprovement.QuarticM32Profile20261020Data.coefficient_three

#print axioms KLSConstantImprovement.QuarticM32Profile20261020Data.coefficient_four
