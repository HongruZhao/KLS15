import KLSConstantImprovement.TriplePositiveEnergyFirstCostTail
import KLSConstantImprovement.ParameterizedWeightedBudget
import KLSConstantImprovement.RawCubicWeightedBudget
import KLSConstantImprovement.PositiveEnergyWeightTailAny

/-! Exact rational generator profile for the raw401.317 cubic/quartic head.
This file proves scalar conditions only. Degrees3/4 are paid by the same-test
quartic support in the separate all-rank wrapper. -/
noncomputable section
open Set
open scoped BigOperators
namespace KLSConstantImprovement.QuarticM20Profile20261020Data
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def K : ℝ := 1228786538762839/100000000000000
def C : ℝ := 1668485576364531/10000000000000000
def c : ℝ := 648157177622287/25000000000000
def p : ℝ := 1289543000000000/1228786538762839
def tau : ℝ := 1
def alphaTail : ℝ := 636071139531/1562500000000
def youngTail : ℝ := 1349376899463777/50000000000000
def tTail : ℝ := 107576376170681/50000000000000
def tail_J : ℝ := -6835152332672975402546053990186422940775044440269193218810264009513576970334464940033588085666742078375648239190378527421790103468276315170881914757085376854188488260470371874951170040266066213982420748035841723150603290523491763109438782757804889796783/26030031186142805093765472677731657839768003600235591220672475383096651680569021549069713146846588039961965600765337416198193668703729803436431699143944419941725859578866743975899318284835846980492413668496606467871059114623621621740079020000000000000
def tail_q : ℝ := 11713695377460213889131789392714539267304751285977739/65109463714240588711079761093750000000000000000000000
def tail_b : ℝ := -4996688372121385688378584698413403440124302668821561422765043708961/368644218989181605360777350905643471223281250000000000000000000000
def tail_a : ℝ := 30248144965024908157264259196099862309082046619106787279930538645398674541206520213825980952324554490265367965881515136965036639915851976784297193101156346351565774763208673801542827265214184972124202777715945801631386215574474862370556976995528597706366810058538323/120574860648754056732601577745840469221312408833466740972520510425178426204594862116034797588368963093113240128092042683813906713766834550838433896587369358842421437374195129279963879190472046404300206337023355272116601779924489164292455817023071301900000000000000
def tail_z : ℝ := -30671301198028076570227943222692813053644072641226738338568585462682695201239281823373902470166314343463344659390669584640168587893861306380675339837407341243329956223494838132005372073055323122050525347188994202049062232083011953213493303991445430360167/130150155930714025468827363388658289198840018001177956103362376915483258402845107745348565734232940199809828003826687080990968343518649017182158495719722099708629297894333719879496591424179234902462068342483032339355295573118108108700395100000000000000
def alpha (d : ℕ) : ℝ :=
  if d=2 then 1/3 else
  if d=3 then 24681039035259/50000000000000 else
  if d=4 then 9255678306537/20000000000000 else
  if d=5 then 44365795157693/100000000000000 else
  if d=6 then 43319978407959/100000000000000 else
  if d=7 then 42850533321219/100000000000000 else
  if d=8 then 1657730162657/4000000000000 else
  if d=9 then 1270778580721/3125000000000 else
  if d=10 then 5032208225913/12500000000000 else
  if d=11 then 40085538506803/100000000000000 else
  if d=12 then 40077102353963/100000000000000 else
  if d=13 then 20098945076867/50000000000000 else
  if d=14 then 2021997235933/5000000000000 else
  if d=15 then 40811175075307/100000000000000 else
  if d=16 then 41325448978029/100000000000000 else
  if d=17 then 2074494931813/5000000000000 else
  if d=18 then 20740359765599/50000000000000 else
  if d=19 then 1296527549739/3125000000000 else
  if d=20 then 22430665874249/50000000000000 else
  if d=21 then 22028546342513/50000000000000 else
  if d=22 then 21714546861469/50000000000000 else
  if d=23 then 8586039195847/20000000000000 else
  if d=24 then 5370945721071/12500000000000 else
  if d=25 then 42687468770241/100000000000000 else
  if d=26 then 42441973756521/100000000000000 else
  if d=27 then 42227328102417/100000000000000 else
  if d=28 then 42037236722749/100000000000000 else
  if d=29 then 20933566859217/50000000000000 else
  if d=30 then 20856808893131/50000000000000 else
  if d=31 then 41574748650599/100000000000000 else
  if d=32 then 41448946465503/100000000000000 else
  if d=33 then 41334955636473/100000000000000 else
  if d=34 then 329854346167/800000000000 else
  if d=35 then 257116845253/625000000000 else
  if d=36 then 41055068740687/100000000000000 else
  if d=37 then 5122562559179/12500000000000 else
  if d=38 then 20457376843327/50000000000000 else
  if d=39 then 2553607044673/6250000000000 else
  if d=40 then 1020235695607/2500000000000 else
  if d=41 then 40770230787677/100000000000000 else
  if d=42 then 20370305808029/50000000000000 else
  if d=43 then 40719643391303/100000000000000 else
  alphaTail

def young (d : ℕ) : ℝ :=
  if d=2 then 94459739140281/100000000000000 else
  if d=3 then 721479186834701/100000000000000 else
  if d=4 then 552191827912089/50000000000000 else
  if d=5 then 238030901728337/20000000000000 else
  if d=6 then 633527206022539/50000000000000 else
  if d=7 then 166714228315071/12500000000000 else
  if d=8 then 2242673263641/156250000000 else
  if d=9 then 744019812715709/50000000000000 else
  if d=10 then 301316819494569/20000000000000 else
  if d=11 then 300549558528823/20000000000000 else
  if d=12 then 1488860818005879/100000000000000 else
  if d=13 then 735022728721761/50000000000000 else
  if d=14 then 90433524290093/6250000000000 else
  if d=15 then 355887229053453/25000000000000 else
  if d=16 then 702003665275333/50000000000000 else
  if d=17 then 1408875206151573/100000000000000 else
  if d=18 then 1424809497486147/100000000000000 else
  if d=19 then 717787522740339/50000000000000 else
  if d=20 then 1338099404656483/100000000000000 else
  if d=21 then 1467489732036423/100000000000000 else
  if d=22 then 79237687709273/5000000000000 else
  if d=23 then 844478998251619/50000000000000 else
  youngTail

def t (d : ℕ) : ℝ :=
  if d=2 then 1 else
  if d=3 then 150902838441589/25000000000000 else
  if d=4 then 629375683667019/100000000000000 else
  if d=5 then 266642446905843/50000000000000 else
  if d=6 then 9353736121311/2000000000000 else
  if d=7 then 418738936763861/100000000000000 else
  if d=8 then 392415191989007/100000000000000 else
  if d=9 then 73687562299043/20000000000000 else
  if d=10 then 34703804273001/10000000000000 else
  if d=11 then 41008130911189/12500000000000 else
  if d=12 then 38901597911891/12500000000000 else
  if d=13 then 296130399916117/100000000000000 else
  if d=14 then 56494137503961/20000000000000 else
  if d=15 then 26990329746297/10000000000000 else
  if d=16 then 25811586109657/10000000000000 else
  if d=17 then 15614623136447/6250000000000 else
  if d=18 then 243570027321959/100000000000000 else
  if d=19 then 119038872138807/50000000000000 else
  tTail

def theta (d : ℕ) : ℝ := if 3 ≤ d ∧ d ≤ 24 then 1 else 0
def lambda (d : ℕ) : ℝ := if 2 ≤ d ∧ d ≤ 23 then 1 else 0

def zeta (d : ℕ) : ℝ :=
  if d=3 then 142857/100000 else
  if d=4 then 17410587660681/10000000000000 else
  if d=5 then 58607703505799/65000000000000 else
  if d=6 then 128536974594959/200000000000000 else
  if d=7 then 225867819000831/475000000000000 else
  if d=8 then 18794338251093/55000000000000 else
  if d=9 then 11440512249969/50000000000000 else
  if d=10 then 9053011346093/70000000000000 else
  if d=11 then 65034794820281/1550000000000000 else
  if d=12 then 91/425000000000000 else
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

theorem alpha_eq_tail (d : ℕ) (hd : 44 ≤ d) : alpha d=alphaTail := by
  simp only [alpha,show d≠2 by omega,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,show d≠20 by omega,show d≠21 by omega,show d≠22 by omega,show d≠23 by omega,show d≠24 by omega,show d≠25 by omega,show d≠26 by omega,show d≠27 by omega,show d≠28 by omega,show d≠29 by omega,show d≠30 by omega,show d≠31 by omega,show d≠32 by omega,show d≠33 by omega,show d≠34 by omega,show d≠35 by omega,show d≠36 by omega,show d≠37 by omega,show d≠38 by omega,show d≠39 by omega,show d≠40 by omega,show d≠41 by omega,show d≠42 by omega,show d≠43 by omega,ite_false]

theorem young_eq_tail (d : ℕ) (hd : 24 ≤ d) : young d=youngTail := by
  simp only [young,show d≠2 by omega, show d≠3 by omega, show d≠4 by omega, show d≠5 by omega, show d≠6 by omega, show d≠7 by omega, show d≠8 by omega, show d≠9 by omega, show d≠10 by omega, show d≠11 by omega, show d≠12 by omega, show d≠13 by omega, show d≠14 by omega, show d≠15 by omega, show d≠16 by omega, show d≠17 by omega, show d≠18 by omega, show d≠19 by omega, show d≠20 by omega, show d≠21 by omega, show d≠22 by omega, show d≠23 by omega,ite_false]

theorem t_eq_tail (d : ℕ) (hd : 20 ≤ d) : t d=tTail := by
  simp only [t,show d≠2 by omega,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,ite_false]

theorem alpha_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ alpha d := by
  by_cases hs:d ≤ 43
  · interval_cases d <;> norm_num [alpha,alphaTail]
  · rw [alpha_eq_tail d (by omega)];norm_num [alphaTail]

theorem alpha_lt_one (d : ℕ) (hd : 2 ≤ d) : alpha d<1 := by
  by_cases hs:d ≤ 43
  · interval_cases d <;> norm_num [alpha,alphaTail]
  · rw [alpha_eq_tail d (by omega)];norm_num [alphaTail]

theorem young_positive (d : ℕ) (hd : 2 ≤ d) : 0<young d := by
  by_cases hs:d ≤ 23
  · interval_cases d <;> norm_num [young,youngTail]
  · rw [young_eq_tail d (by omega)];norm_num [youngTail]

theorem t_positive (d : ℕ) (hd : 2 ≤ d) : 0<t d := by
  by_cases hs:d ≤ 19
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
  by_cases hs:d ≤ 19
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

theorem first_cost_tail (d : ℕ) (hd : 45 ≤ d) :
    PositiveEnergyWeightedDrift.firstCost young t theta lambda d=(youngTail/tTail)*(d : ℝ)+tail_J := by
  have hh:=PositiveEnergyWeightTailAny.firstCost_tail young t theta lambda youngTail tTail
    (by norm_num [tTail]) 20 (by norm_num) (by norm_num) young_eq_tail (fun j hj=>t_eq_tail j (by omega)) d (by omega)
    (theta_eq_zero d (by omega)) (lambda_eq_zero (d-1) (by omega))
  convert hh using 1
  norm_num [PositiveEnergyWeightTailAny.ratioPrefix,PositiveEnergyWeightTail.ratioPrefix,sum_interval_two,Finset.sum_range_succ,young,youngTail,t,tTail,tail_J]

theorem raw_first_cost_tail (d : ℕ) (hd : 45 ≤ d) :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta d=
      (youngTail/tTail)*(d : ℝ)+tail_J := by
  rw [TriplePositiveEnergyFirstCostTail.rawFirstCost_eq_of_zero young t theta lambda zeta d
    (by omega) (zeta_eq_zero (d-2) (by omega))]
  exact first_cost_tail d hd

theorem tail_noise_loss (d : ℕ) (hd : 45 ≤ d) :
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda d=generalResidualGeneratorLoss alphaTail d := by
  have hd3:3 ≤ d:=by omega
  have hd2:d≠2:=by omega
  have hr:(45:ℝ) ≤ d:=by exact_mod_cast hd
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

theorem coefficient_finite (d : ℕ) (hd : 5 ≤ d) (hD : d<45) : c ≤ coefficient profile d := by
  interval_cases d <;> norm_num [sum_interval_two,Finset.sum_range_succ,coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]

theorem coefficient_tail_cubic (d : ℕ) (hd : 45 ≤ d) :
    ((d : ℝ)-1)*(coefficient profile d-c)=tail_q*(d : ℝ)^3+tail_b*(d : ℝ)^2+tail_a*(d : ℝ)+tail_z := by
  have hd3:3 ≤ d:=by omega
  have hr:(45:ℝ) ≤ d:=by exact_mod_cast hd
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
  by_cases hs:d<45
  · exact coefficient_finite d hd hs
  · have hd41:45 ≤ d:=by omega
    have hr:(45:ℝ) ≤ d:=by exact_mod_cast hd41
    have hp:=ParameterizedWeightedBudget.cubic_nonneg_on_tail tail_q tail_b tail_a tail_z 45 d hr
      (by norm_num [tail_q]) (by norm_num [tail_q,tail_b]) (by norm_num [tail_q,tail_b,tail_a])
      (by norm_num [tail_q,tail_b,tail_a,tail_z])
    rw [←coefficient_tail_cubic d hd41] at hp
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by linarith : 0<(d : ℝ)-1)).mp hp)

theorem head_value : head profile=(30429511645487342589771193333017025839553686213249303978328367/1069697289642442671333561271014568390128433507500000000000000 : ℝ) := by
  norm_num [head,profile,TriplePositiveEnergyWeightedGenerator.head,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]
theorem coefficient_three : coefficient profile 3=(-332966779029102179231447972739655360098662578011401395475624605449485680955312649416056647913473285061561/6280835138984809079747500760554636359761953103889752631138177814104382357098668992942810000000000000000 : ℝ) := by
  norm_num [coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]

theorem coefficient_four : coefficient profile 4=(-124069334439504212734516791305424755439643687952777418454382813624050296850772682940135924097741492299736474640190694579846598247/41833984064754832678689407640043531308314499753675237640287000548092921774864736817057998571017783512734375000000000000000000000 : ℝ) := by
  norm_num [sum_interval_two,Finset.sum_range_succ,coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]


end KLSConstantImprovement.QuarticM20Profile20261020Data
#print axioms KLSConstantImprovement.QuarticM20Profile20261020Data.coefficient_lower
#print axioms KLSConstantImprovement.QuarticM20Profile20261020Data.head_value
#print axioms KLSConstantImprovement.QuarticM20Profile20261020Data.coefficient_three

#print axioms KLSConstantImprovement.QuarticM20Profile20261020Data.coefficient_four
