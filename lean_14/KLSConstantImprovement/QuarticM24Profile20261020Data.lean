import KLSConstantImprovement.TriplePositiveEnergyFirstCostTail
import KLSConstantImprovement.ParameterizedWeightedBudget
import KLSConstantImprovement.RawCubicWeightedBudget
import KLSConstantImprovement.PositiveEnergyWeightTailAny

/-! Exact rational generator profile for the raw401.3023465 cubic/quartic head.
This file proves scalar conditions only. Degrees3/4 are paid by the same-test
quartic support in the separate all-rank wrapper. -/
noncomputable section
open Set
open scoped BigOperators
namespace KLSConstantImprovement.QuarticM24Profile20261020Data
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def K : ℝ := 1226471241438829/100000000000000
def C : ℝ := 554987167172537/5000000000000000
def c : ℝ := 1309065391689087/50000000000000
def p : ℝ := 1287389000000000/1226471241438829
def tau : ℝ := 1
def alphaTail : ℝ := 41492394038929/100000000000000
def youngTail : ℝ := 1675934404760969/100000000000000
def tTail : ℝ := 62482945355511/50000000000000
def tail_J : ℝ := -1251145008541892372414632878630742404312353665421912970448893410843150700751514880718650221847945392876268521680558565943404017082168288517708848059525771121864082663524020217057529980013765779987439105906609315197916387208227578405850116202102577617566426368934382311207425610456893932086196090223133584549059/3964929824553619730455321360091034747397937667948822868410209141750782998105339736571621255531860072946843196796376415212768840681380765647447422768412749586668796224264650192355061133959665621244491208301404673743372500018736294300726143865886851154915818359008782779323201033951895601038841575000000000000
def tail_q : ℝ := 167649815876790328606885016928942892945961028602846555659/980549097703568479872742377990000000000000000000000000000
def tail_b : ℝ := -886741568505165040830259600781796019237301012736446639420307317603886749/61267595690207685905315502851156896091602890000000000000000000000000000
def tail_a : ℝ := 1466834867210707090715705437777204317461790712875546081584058975103579283396323995959513684719308902399946608089918083746748631222961884718672988820419848116536444039422533225380235748308693504677260621859214472006275406364336357072157880756135641165393735419909641226670249694437279342940606074287912664630023406593695329/4816163705985084206019203050228965672790674822300088049961687973677756335614458113568860275326368423636789894578446949222317260176715276960423188051769723402946868927144655189641568752804882238939835951204201708995925276086687910137388488685916747544581669933011789352824371375854198707155717433501973418550000000000000
def tail_z : ℝ := -2286746060882716416931315513602163210039586720833238029160206304104321877233517456953821976327560901788238130018857987963802247465017429083292171021675631116543831234949704382717415504909404826079567553631110082314830613503958729809295496999092425586143779103790415571776081699808390908128398455832367847122437/7929859649107239460910642720182069494795875335897645736820418283501565996210679473143242511063720145893686393592752830425537681362761531294894845536825499173337592448529300384710122267919331242488982416602809347486745000037472588601452287731773702309831636718017565558646402067903791202077683150000000000000
def alpha (d : ℕ) : ℝ :=
  if d=2 then 1/3 else
  if d=3 then 495946774569/1000000000000 else
  if d=4 then 362197313399/781250000000 else
  if d=5 then 8887136761037/20000000000000 else
  if d=6 then 43388894882639/100000000000000 else
  if d=7 then 42843289227551/100000000000000 else
  if d=8 then 41512243847717/100000000000000 else
  if d=9 then 1016896398311/2500000000000 else
  if d=10 then 8041153287079/20000000000000 else
  if d=11 then 39953131292559/100000000000000 else
  if d=12 then 995828108989/2500000000000 else
  if d=13 then 19898565758879/50000000000000 else
  if d=14 then 19908445745651/50000000000000 else
  if d=15 then 39878125999621/100000000000000 else
  if d=16 then 19989145726297/50000000000000 else
  if d=17 then 20058394263487/50000000000000 else
  if d=18 then 10074465560767/25000000000000 else
  if d=19 then 40529667289627/100000000000000 else
  if d=20 then 31893145001/78125000000 else
  if d=21 then 41175940732797/100000000000000 else
  if d=22 then 20565842345293/50000000000000 else
  if d=23 then 4109237662993/10000000000000 else
  if d=24 then 21935757520669/50000000000000 else
  if d=25 then 21803125778543/50000000000000 else
  if d=26 then 5421826867449/12500000000000 else
  if d=27 then 5396694479687/12500000000000 else
  if d=28 then 21497974584999/50000000000000 else
  if d=29 then 856731615403/2000000000000 else
  if d=30 then 10672896928351/25000000000000 else
  if d=31 then 8511776765459/20000000000000 else
  if d=32 then 42436890213227/100000000000000 else
  if d=33 then 10581094820863/25000000000000 else
  if d=34 then 42220418614597/100000000000000 else
  if d=35 then 42124316352953/100000000000000 else
  if d=36 then 21017784658869/50000000000000 else
  if d=37 then 20976909721923/50000000000000 else
  if d=38 then 20939414519661/50000000000000 else
  if d=39 then 5226306429779/12500000000000 else
  if d=40 then 41748606977969/100000000000000 else
  if d=41 then 4169326348917/10000000000000 else
  if d=42 then 20822210550033/50000000000000 else
  if d=43 then 41602098569641/100000000000000 else
  if d=44 then 41566326013607/100000000000000 else
  if d=45 then 4153743576999/10000000000000 else
  if d=46 then 8303157806713/20000000000000 else
  if d=47 then 41500475693247/100000000000000 else
  alphaTail

def young (d : ℕ) : ℝ :=
  if d=2 then 94885019011459/100000000000000 else
  if d=3 then 29370397981561/6250000000000 else
  if d=4 then 45178747430773/6250000000000 else
  if d=5 then 391357421891171/50000000000000 else
  if d=6 then 419963429113801/50000000000000 else
  if d=7 then 447278101512087/50000000000000 else
  if d=8 then 241925462744901/25000000000000 else
  if d=9 then 253800883812941/25000000000000 else
  if d=10 then 1039606926080737/100000000000000 else
  if d=11 then 1046446020580411/100000000000000 else
  if d=12 then 4065644595213/390625000000 else
  if d=13 then 1028084334303257/100000000000000 else
  if d=14 then 1013018266915861/100000000000000 else
  if d=15 then 496594727589053/50000000000000 else
  if d=16 then 485258901899519/50000000000000 else
  if d=17 then 946499165616203/100000000000000 else
  if d=18 then 461132009571933/50000000000000 else
  if d=19 then 179733434286263/20000000000000 else
  if d=20 then 438056964463177/50000000000000 else
  if d=21 then 429120604393009/50000000000000 else
  if d=22 then 170278364850539/20000000000000 else
  if d=23 then 842525663330727/100000000000000 else
  youngTail

def t (d : ℕ) : ℝ :=
  if d=2 then 1 else
  if d=3 then 193129883539383/50000000000000 else
  if d=4 then 400087431844257/100000000000000 else
  if d=5 then 169051814676907/50000000000000 else
  if d=6 then 147909749916959/50000000000000 else
  if d=7 then 264809979656723/100000000000000 else
  if d=8 then 30911382169187/12500000000000 else
  if d=9 then 46429822862943/20000000000000 else
  if d=10 then 27335505514051/12500000000000 else
  if d=11 then 206827959197411/100000000000000 else
  if d=12 then 196410952618539/100000000000000 else
  if d=13 then 187235127299621/100000000000000 else
  if d=14 then 179107507513257/100000000000000 else
  if d=15 then 85926694419091/50000000000000 else
  if d=16 then 165319086519757/100000000000000 else
  if d=17 then 31873869956679/20000000000000 else
  if d=18 then 30777383027967/20000000000000 else
  if d=19 then 148769285106461/100000000000000 else
  if d=20 then 71962738361969/50000000000000 else
  if d=21 then 69665595649231/50000000000000 else
  if d=22 then 27280439053473/20000000000000 else
  if d=23 then 133718916431659/100000000000000 else
  tTail

def theta (d : ℕ) : ℝ := if 3 ≤ d ∧ d ≤ 24 then 1 else 0
def lambda (d : ℕ) : ℝ := if 2 ≤ d ∧ d ≤ 23 then 1 else 0

def zeta (d : ℕ) : ℝ :=
  if d=3 then 142857/100000 else
  if d=4 then 18157978185223/10000000000000 else
  if d=5 then 5047124658919/5200000000000 else
  if d=6 then 71050858438637/100000000000000 else
  if d=7 then 132008010023127/237500000000000 else
  if d=8 then 4706245087569/11000000000000 else
  if d=9 then 160873975331421/500000000000000 else
  if d=10 then 567826822211/2500000000000 else
  if d=11 then 175417507551/1250000000000 else
  if d=12 then 12725735523319/212500000000000 else
  if d=13 then 0 else
  if d=14 then 0 else
  if d=15 then 0 else
  if d=16 then 0 else
  if d=17 then 0 else
  if d=18 then 0 else
  if d=19 then 0 else
  if d=20 then 0 else
  if d=21 then 0 else
  if d=22 then 0 else
  if d=23 then 0 else
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

theorem alpha_eq_tail (d : ℕ) (hd : 48 ≤ d) : alpha d=alphaTail := by
  simp only [alpha,show d≠2 by omega,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,show d≠20 by omega,show d≠21 by omega,show d≠22 by omega,show d≠23 by omega,show d≠24 by omega,show d≠25 by omega,show d≠26 by omega,show d≠27 by omega,show d≠28 by omega,show d≠29 by omega,show d≠30 by omega,show d≠31 by omega,show d≠32 by omega,show d≠33 by omega,show d≠34 by omega,show d≠35 by omega,show d≠36 by omega,show d≠37 by omega,show d≠38 by omega,show d≠39 by omega,show d≠40 by omega,show d≠41 by omega,show d≠42 by omega,show d≠43 by omega,show d≠44 by omega,show d≠45 by omega,show d≠46 by omega,show d≠47 by omega,ite_false]

theorem young_eq_tail (d : ℕ) (hd : 24 ≤ d) : young d=youngTail := by
  simp only [young,show d≠2 by omega, show d≠3 by omega, show d≠4 by omega, show d≠5 by omega, show d≠6 by omega, show d≠7 by omega, show d≠8 by omega, show d≠9 by omega, show d≠10 by omega, show d≠11 by omega, show d≠12 by omega, show d≠13 by omega, show d≠14 by omega, show d≠15 by omega, show d≠16 by omega, show d≠17 by omega, show d≠18 by omega, show d≠19 by omega, show d≠20 by omega, show d≠21 by omega, show d≠22 by omega, show d≠23 by omega,ite_false]

theorem t_eq_tail (d : ℕ) (hd : 24 ≤ d) : t d=tTail := by
  simp only [t,show d≠2 by omega,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,show d≠20 by omega,show d≠21 by omega,show d≠22 by omega,show d≠23 by omega,ite_false]

theorem alpha_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ alpha d := by
  by_cases hs:d ≤ 47
  · interval_cases d <;> norm_num [alpha,alphaTail]
  · rw [alpha_eq_tail d (by omega)];norm_num [alphaTail]

theorem alpha_lt_one (d : ℕ) (hd : 2 ≤ d) : alpha d<1 := by
  by_cases hs:d ≤ 47
  · interval_cases d <;> norm_num [alpha,alphaTail]
  · rw [alpha_eq_tail d (by omega)];norm_num [alphaTail]

theorem young_positive (d : ℕ) (hd : 2 ≤ d) : 0<young d := by
  by_cases hs:d ≤ 23
  · interval_cases d <;> norm_num [young,youngTail]
  · rw [young_eq_tail d (by omega)];norm_num [youngTail]

theorem t_positive (d : ℕ) (hd : 2 ≤ d) : 0<t d := by
  by_cases hs:d ≤ 23
  · interval_cases d <;> norm_num [t,tTail]
  · rw [t_eq_tail d (by omega)];norm_num [tTail]

theorem theta_nonneg (d : ℕ) (_hd : 3 ≤ d) : 0 ≤ theta d := by unfold theta;split_ifs <;> norm_num
theorem theta_le_one (d : ℕ) (_hd : 3 ≤ d) : theta d ≤ 1 := by unfold theta;split_ifs <;> norm_num
theorem lambda_nonneg (d : ℕ) (_hd : 2 ≤ d) : 0 ≤ lambda d := by unfold lambda;split_ifs <;> norm_num
theorem lambda_le_one (d : ℕ) (_hd : 2 ≤ d) : lambda d ≤ 1 := by unfold lambda;split_ifs <;> norm_num
theorem theta_eq_zero (d : ℕ) (hd : 25 ≤ d) : theta d=0 := by simp [theta,show ¬(3 ≤ d ∧ d ≤ 24) by omega]
theorem lambda_eq_zero (d : ℕ) (hd : 24 ≤ d) : lambda d=0 := by simp [lambda,show ¬(2 ≤ d ∧ d ≤ 23) by omega]
theorem zeta_eq_zero (d : ℕ) (hd : 24 ≤ d) : zeta d=0 := by
  simp only [zeta,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,show d≠20 by omega,show d≠21 by omega,show d≠22 by omega,show d≠23 by omega,ite_false]

theorem zeta_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ zeta d := by
  by_cases hs:d ≤ 23
  · interval_cases d <;> norm_num [zeta]
  · rw [zeta_eq_zero d (by omega)]

theorem zeta_cap (d : ℕ) (hd : 2 ≤ d) : tripleHarmonicRatio (d : ℝ)*zeta d<1 := by
  by_cases hs:d ≤ 23
  · interval_cases d <;> norm_num [tripleHarmonicRatio,TripleCreation.chargeRatio,zeta]
  · rw [zeta_eq_zero d (by omega)];norm_num

theorem lambda_boundary (d : ℕ) (hd : 2 ≤ d) (he : lambda d=1) : theta (d+1)=1 := by
  by_cases hs:d ≤ 23
  · have hh:3 ≤ d+1 ∧ d+1 ≤ 24:=by omega
    simp [theta,hh]
  · rw [lambda_eq_zero d (by omega)] at he
    norm_num at he

theorem t_floor (d : ℕ) (hd : 2 ≤ d) : tau ≤ t d := by
  by_cases hs:d ≤ 23
  · interval_cases d <;> norm_num [tau,t,tTail]
  · rw [t_eq_tail d (by omega)];norm_num [tau,tTail]

theorem terminal_payment (d : ℕ) (hd : 3 ≤ d) :
    ((d : ℝ)+PositiveEnergyWeightedDrift.kappa K young t lambda d)*(1-alpha d) ≤ (d : ℝ) := by
  by_cases hs:d ≤ 23
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

theorem first_cost_tail (d : ℕ) (hd : 49 ≤ d) :
    PositiveEnergyWeightedDrift.firstCost young t theta lambda d=(youngTail/tTail)*(d : ℝ)+tail_J := by
  have hh:=PositiveEnergyWeightTailAny.firstCost_tail young t theta lambda youngTail tTail
    (by norm_num [tTail]) 24 (by norm_num) (by norm_num) young_eq_tail (fun j hj=>t_eq_tail j (by omega)) d (by omega)
    (theta_eq_zero d (by omega)) (lambda_eq_zero (d-1) (by omega))
  convert hh using 1
  norm_num [PositiveEnergyWeightTailAny.ratioPrefix,PositiveEnergyWeightTail.ratioPrefix,sum_interval_two,Finset.sum_range_succ,young,youngTail,t,tTail,tail_J]

theorem raw_first_cost_tail (d : ℕ) (hd : 49 ≤ d) :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta d=
      (youngTail/tTail)*(d : ℝ)+tail_J := by
  rw [TriplePositiveEnergyFirstCostTail.rawFirstCost_eq_of_zero young t theta lambda zeta d
    (by omega) (zeta_eq_zero (d-2) (by omega))]
  exact first_cost_tail d hd

theorem tail_noise_loss (d : ℕ) (hd : 49 ≤ d) :
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda d=generalResidualGeneratorLoss alphaTail d := by
  have hd3:3 ≤ d:=by omega
  have hd2:d≠2:=by omega
  have hr:(49:ℝ) ≤ d:=by exact_mod_cast hd
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

theorem coefficient_finite (d : ℕ) (hd : 5 ≤ d) (hD : d<49) : c ≤ coefficient profile d := by
  interval_cases d <;> norm_num [sum_interval_two,Finset.sum_range_succ,coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]

theorem coefficient_tail_cubic (d : ℕ) (hd : 49 ≤ d) :
    ((d : ℝ)-1)*(coefficient profile d-c)=tail_q*(d : ℝ)^3+tail_b*(d : ℝ)^2+tail_a*(d : ℝ)+tail_z := by
  have hd3:3 ≤ d:=by omega
  have hr:(49:ℝ) ≤ d:=by exact_mod_cast hd
  have hm:(d : ℝ)-1≠0:=by linarith
  change ((d : ℝ)-1)*(TriplePositiveEnergyWeightedGenerator.coefficient K C young t alpha theta lambda zeta d-c)=_
  unfold TriplePositiveEnergyWeightedGenerator.coefficient PositiveEnergyWeightedGenerator.incoming TriplePositiveEnergyWeightedGenerator.cost
  rw [t_eq_tail d (by omega),t_eq_tail (d-1) (by omega),alpha_eq_tail (d-1) (by omega),tail_noise_loss d hd,young_eq_tail d (by omega),ite_eq_left hd3,raw_first_cost_tail d hd]
  rw [show tripleHarmonicNeighborCharge K young zeta d=0 by simp [tripleHarmonicNeighborCharge,zeta_eq_zero d (by omega)]]
  simp only [mul_zero,add_zero]
  norm_num [generalResidualGeneratorLoss,generalResidualA,K,C,c,alphaTail,youngTail,tTail,tail_J,tail_q,tail_b,tail_a,tail_z]
  field_simp
  ring

theorem coefficient_lower (d : ℕ) (hd : 5 ≤ d) : c ≤ coefficient profile d := by
  by_cases hs:d<49
  · exact coefficient_finite d hd hs
  · have hd41:49 ≤ d:=by omega
    have hr:(49:ℝ) ≤ d:=by exact_mod_cast hd41
    have hp:=ParameterizedWeightedBudget.cubic_nonneg_on_tail tail_q tail_b tail_a tail_z 49 d hr
      (by norm_num [tail_q]) (by norm_num [tail_q,tail_b]) (by norm_num [tail_q,tail_b,tail_a])
      (by norm_num [tail_q,tail_b,tail_a,tail_z])
    rw [←coefficient_tail_cubic d hd41] at hp
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by linarith : 0<(d : ℝ)-1)).mp hp)

theorem head_value : head profile=(4192486181070820201610054369448438059693827769134412098783693/178411317535885418343166191484311573404663273750000000000000 : ℝ) := by
  norm_num [head,profile,TriplePositiveEnergyWeightedGenerator.head,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]
theorem coefficient_three : coefficient profile 3=(-52669347405169301677435457843920691886757623286706856275583047104792690282391462731812840622003524941/1054749584053931273751445127164733089095436219593763828624158383323203545490319551440000000000000000 : ℝ) := by
  norm_num [coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]

theorem coefficient_four : coefficient profile 4=(-18515251666402927113193194300083110330114228935801091377772652925434470412649351148742043583934628532625067711700815369975733/8253689494156195619181214767859631882329607569817212732755633082330222111680972660420533919683787478125000000000000000000000 : ℝ) := by
  norm_num [sum_interval_two,Finset.sum_range_succ,coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]


end KLSConstantImprovement.QuarticM24Profile20261020Data
#print axioms KLSConstantImprovement.QuarticM24Profile20261020Data.coefficient_lower
#print axioms KLSConstantImprovement.QuarticM24Profile20261020Data.head_value
#print axioms KLSConstantImprovement.QuarticM24Profile20261020Data.coefficient_three

#print axioms KLSConstantImprovement.QuarticM24Profile20261020Data.coefficient_four
