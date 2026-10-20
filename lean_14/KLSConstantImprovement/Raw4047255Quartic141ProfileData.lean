import KLSConstantImprovement.TriplePositiveEnergyFirstCostTail
import KLSConstantImprovement.ParameterizedWeightedBudget
import KLSConstantImprovement.RawCubicWeightedBudget

/-! Exact rational generator profile for the raw404.7255 cubic/quartic head.
This file proves scalar conditions only. Degrees3/4 are paid by the same-test
quartic support in the separate all-rank wrapper. -/
noncomputable section
open Set
open scoped BigOperators
namespace KLSConstantImprovement.Raw4047255Quartic141ProfileData
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def K : ℝ := 250155444070949/20000000000000
def C : ℝ := 57660624675709/500000000000000
def c : ℝ := 2285358954256989/100000000000000
def p : ℝ := 262000000000000/250155444070949
def tau : ℝ := 1
def alphaTail : ℝ := 7438148674889/20000000000000
def youngTail : ℝ := 2490378731934557/100000000000000
def tTail : ℝ := 224840285659879/100000000000000
def tail_J : ℝ := -3087702882437280012206057851137772606471880474717426389281567552780650575292975587261021787572075219/20840994636219484391372224282302053307179551207841400022299730649145769394935275563175000000000000
def tail_q : ℝ := 2819618920058279223424534421402234028965158174772979647/12513506949512146681193104330800000000000000000000000000
def tail_b : ℝ := -100279059020092568609865772015468778423403789223656608496025095294448139/8440621431405576369295162672832492312111919600000000000000000000000000
def tail_a : ℝ := 4364495967121267172745327006516433587218325290091110952492974129283128990657417467311743803135937772083377602991/31733512253045451320872285689245519913012073366087851084127429867223050120480887275799734611440900000000000000
def tail_z : ℝ := -10362281402903999001912616020033499100489498805402314987508653582080247142883048591199611132262109673/83363978544877937565488897129208213228718204831365600089198922596583077579741102252700000000000000
def alpha (d : ℕ) : ℝ :=
  if d=2 then 1/3 else
  if d=3 then 48138050159537/100000000000000 else
  if d=4 then 11121232472277/25000000000000 else
  if d=5 then 1068873524163/2500000000000 else
  if d=6 then 41878757021243/100000000000000 else
  if d=7 then 20739633990479/50000000000000 else
  if d=8 then 50385527001283/100000000000000 else
  if d=9 then 942342256867/2000000000000 else
  if d=10 then 45001124110767/100000000000000 else
  if d=11 then 43499283139821/100000000000000 else
  if d=12 then 42350505817587/100000000000000 else
  if d=13 then 10375151258917/25000000000000 else
  if d=14 then 163440045231/400000000000 else
  if d=15 then 4037231670349/10000000000000 else
  if d=16 then 4999677033671/12500000000000 else
  if d=17 then 9926970303011/25000000000000 else
  if d=18 then 39484641525767/100000000000000 else
  if d=19 then 19657250780241/50000000000000 else
  if d=20 then 3918939908449/10000000000000 else
  if d=21 then 39105338988459/100000000000000 else
  if d=22 then 19530467779807/50000000000000 else
  if d=23 then 1562255755693/4000000000000 else
  if d=24 then 39215953233581/100000000000000 else
  if d=25 then 7808257928087/20000000000000 else
  if d=26 then 3885130511549/10000000000000 else
  if d=27 then 38670329833717/100000000000000 else
  if d=28 then 2406082545133/6250000000000 else
  if d=29 then 7666300605411/20000000000000 else
  if d=30 then 7634456910153/20000000000000 else
  if d=31 then 2376327225481/6250000000000 else
  if d=32 then 9469757820631/25000000000000 else
  if d=33 then 37746406542899/100000000000000 else
  if d=34 then 18812108868211/50000000000000 else
  if d=35 then 18756752957761/50000000000000 else
  if d=36 then 9353891269139/25000000000000 else
  if d=37 then 9333004459699/25000000000000 else
  if d=38 then 37264900341017/100000000000000 else
  if d=39 then 930418923651/2500000000000 else
  alphaTail

def young (d : ℕ) : ℝ :=
  if d=2 then 20075830319971/20000000000000 else
  if d=3 then 117600599607497/25000000000000 else
  if d=4 then 646036379615679/100000000000000 else
  if d=5 then 83264140084139/12500000000000 else
  if d=6 then 33854179607751/5000000000000 else
  if d=7 then 679653471675583/100000000000000 else
  if d=8 then 553707373951713/100000000000000 else
  if d=9 then 725801652999859/100000000000000 else
  if d=10 then 444383042719087/50000000000000 else
  if d=11 then 130526646169351/12500000000000 else
  if d=12 then 1193971014275687/100000000000000 else
  if d=13 then 1334584214423583/100000000000000 else
  if d=14 then 733704441491489/50000000000000 else
  if d=15 then 199510156531169/12500000000000 else
  if d=16 then 68941066915157/4000000000000 else
  if d=17 then 369374426317873/20000000000000 else
  if d=18 then 1964296639420721/100000000000000 else
  if d=19 then 259604862783449/12500000000000 else
  if d=20 then 2189306575782913/100000000000000 else
  if d=21 then 1153390191859227/50000000000000 else
  if d=22 then 1217013818307113/50000000000000 else
  if d=23 then 1287406755640433/50000000000000 else
  youngTail

def t (d : ℕ) : ℝ :=
  if d=2 then 1 else
  if d=3 then 421779037813849/100000000000000 else
  if d=4 then 425864678663637/100000000000000 else
  if d=5 then 3704504810413/1000000000000 else
  if d=6 then 331355231465769/100000000000000 else
  if d=7 then 151344347975297/50000000000000 else
  tTail

def theta (d : ℕ) : ℝ := if 3 ≤ d ∧ d ≤ 24 then 1 else 0
def lambda (d : ℕ) : ℝ := if 2 ≤ d ∧ d ≤ 23 then 1 else 0

def zeta (d : ℕ) : ℝ :=
  if d=3 then 142857/100000 else
  if d=4 then 25284475744517/25000000000000 else
  if d=5 then 41715993121677/130000000000000 else
  if d=6 then 373401/200000000000000 else
  if d=7 then 51528477/475000000000000 else
  if d=8 then 0 else
  if d=9 then 44407851689487/500000000000000 else
  if d=10 then 6097730687257/35000000000000 else
  if d=11 then 363237923357309/1550000000000000 else
  if d=12 then 59019899284437/212500000000000 else
  if d=13 then 115451180299637/370000000000000 else
  if d=14 then 847992647593/2500000000000 else
  if d=15 then 1955363549607/5375000000000 else
  if d=16 then 111767571623067/287500000000000 else
  if d=17 then 403220903511771/980000000000000 else
  if d=18 then 111489660996393/260000000000000 else
  if d=19 then 48989161152953/110000000000000 else
  if d=20 then 134365883563219/290000000000000 else
  if d=21 then 1476623134414967/3050000000000000 else
  if d=22 then 409742736765109/800000000000000 else
  if d=23 then 18431516997727/33500000000000 else
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

theorem alpha_eq_tail (d : ℕ) (hd : 40 ≤ d) : alpha d=alphaTail := by
  simp only [alpha,show d≠2 by omega, show d≠3 by omega, show d≠4 by omega, show d≠5 by omega, show d≠6 by omega, show d≠7 by omega, show d≠8 by omega, show d≠9 by omega, show d≠10 by omega, show d≠11 by omega, show d≠12 by omega, show d≠13 by omega, show d≠14 by omega, show d≠15 by omega, show d≠16 by omega, show d≠17 by omega, show d≠18 by omega, show d≠19 by omega, show d≠20 by omega, show d≠21 by omega, show d≠22 by omega, show d≠23 by omega, show d≠24 by omega, show d≠25 by omega, show d≠26 by omega, show d≠27 by omega, show d≠28 by omega, show d≠29 by omega, show d≠30 by omega, show d≠31 by omega, show d≠32 by omega, show d≠33 by omega, show d≠34 by omega, show d≠35 by omega, show d≠36 by omega, show d≠37 by omega, show d≠38 by omega, show d≠39 by omega,ite_false]

theorem young_eq_tail (d : ℕ) (hd : 24 ≤ d) : young d=youngTail := by
  simp only [young,show d≠2 by omega, show d≠3 by omega, show d≠4 by omega, show d≠5 by omega, show d≠6 by omega, show d≠7 by omega, show d≠8 by omega, show d≠9 by omega, show d≠10 by omega, show d≠11 by omega, show d≠12 by omega, show d≠13 by omega, show d≠14 by omega, show d≠15 by omega, show d≠16 by omega, show d≠17 by omega, show d≠18 by omega, show d≠19 by omega, show d≠20 by omega, show d≠21 by omega, show d≠22 by omega, show d≠23 by omega,ite_false]

theorem t_eq_tail (d : ℕ) (hd : 8 ≤ d) : t d=tTail := by
  simp only [t,show d≠2 by omega, show d≠3 by omega, show d≠4 by omega, show d≠5 by omega, show d≠6 by omega, show d≠7 by omega,ite_false]

theorem alpha_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ alpha d := by
  by_cases hs:d ≤ 39
  · interval_cases d <;> norm_num [alpha,alphaTail]
  · rw [alpha_eq_tail d (by omega)];norm_num [alphaTail]

theorem alpha_lt_one (d : ℕ) (hd : 2 ≤ d) : alpha d<1 := by
  by_cases hs:d ≤ 39
  · interval_cases d <;> norm_num [alpha,alphaTail]
  · rw [alpha_eq_tail d (by omega)];norm_num [alphaTail]

theorem young_positive (d : ℕ) (hd : 2 ≤ d) : 0<young d := by
  by_cases hs:d ≤ 23
  · interval_cases d <;> norm_num [young,youngTail]
  · rw [young_eq_tail d (by omega)];norm_num [youngTail]

theorem t_positive (d : ℕ) (hd : 2 ≤ d) : 0<t d := by
  by_cases hs:d ≤ 7
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
  by_cases hs:d ≤ 7
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

theorem first_cost_tail (d : ℕ) (hd : 41 ≤ d) :
    PositiveEnergyWeightedDrift.firstCost young t theta lambda d=(youngTail/tTail)*(d : ℝ)+tail_J := by
  have hh:=PositiveEnergyWeightTail.firstCost_tail young t theta lambda youngTail tTail
    (by norm_num [tTail]) young_eq_tail (fun j hj=>t_eq_tail j (by omega)) d hd
    (theta_eq_zero d (by omega)) (lambda_eq_zero (d-1) (by omega))
  convert hh using 1
  norm_num [PositiveEnergyWeightTail.ratioPrefix,sum_interval_two,Finset.sum_range_succ,young,youngTail,t,tTail,tail_J]

theorem raw_first_cost_tail (d : ℕ) (hd : 41 ≤ d) :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta d=
      (youngTail/tTail)*(d : ℝ)+tail_J := by
  rw [TriplePositiveEnergyFirstCostTail.rawFirstCost_eq_of_zero young t theta lambda zeta d
    (by omega) (zeta_eq_zero (d-2) (by omega))]
  exact first_cost_tail d hd

theorem tail_noise_loss (d : ℕ) (hd : 41 ≤ d) :
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda d=generalResidualGeneratorLoss alphaTail d := by
  have hd3:3 ≤ d:=by omega
  have hd2:d≠2:=by omega
  have hr:(41:ℝ) ≤ d:=by exact_mod_cast hd
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

theorem coefficient_finite (d : ℕ) (hd : 5 ≤ d) (hD : d<41) : c ≤ coefficient profile d := by
  interval_cases d <;> norm_num [sum_interval_two,Finset.sum_range_succ,coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]

theorem coefficient_tail_cubic (d : ℕ) (hd : 41 ≤ d) :
    ((d : ℝ)-1)*(coefficient profile d-c)=tail_q*(d : ℝ)^3+tail_b*(d : ℝ)^2+tail_a*(d : ℝ)+tail_z := by
  have hd3:3 ≤ d:=by omega
  have hr:(41:ℝ) ≤ d:=by exact_mod_cast hd
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
  by_cases hs:d<41
  · exact coefficient_finite d hd hs
  · have hd41:41 ≤ d:=by omega
    have hr:(41:ℝ) ≤ d:=by exact_mod_cast hd41
    have hp:=ParameterizedWeightedBudget.cubic_nonneg_on_tail tail_q tail_b tail_a tail_z 41 d hr
      (by norm_num [tail_q]) (by norm_num [tail_q,tail_b]) (by norm_num [tail_q,tail_b,tail_a])
      (by norm_num [tail_q,tail_b,tail_a,tail_z])
    rw [←coefficient_tail_cubic d hd41] at hp
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by linarith : 0<(d : ℝ)-1)).mp hp)

theorem head_value : head profile=(33649721580781716859993844189534919239967442062760093681969/1413337741294452228829271721625067919670392375000000000000 : ℝ) := by
  norm_num [head,profile,TriplePositiveEnergyWeightedGenerator.head,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]
theorem coefficient_three : coefficient profile 3=(-1313762952252305168047586236488159703468836215999170146498637910974373967842643071834153053458510547247/27158655687392729125993302515181697135019848645339669029216815485415178507760957152204400000000000000 : ℝ) := by
  norm_num [coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]

theorem coefficient_four : coefficient profile 4=(51991890792555232186178103677655990587981056100410133794864145903390078825721229362584606653892202314329205208784074552769213631/16094863400254972463758437869338896115808606447282764162408820369942925955155190102387497078076989778875000000000000000000000000 : ℝ) := by
  norm_num [sum_interval_two,Finset.sum_range_succ,coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]


end KLSConstantImprovement.Raw4047255Quartic141ProfileData
#print axioms KLSConstantImprovement.Raw4047255Quartic141ProfileData.coefficient_lower
#print axioms KLSConstantImprovement.Raw4047255Quartic141ProfileData.head_value
#print axioms KLSConstantImprovement.Raw4047255Quartic141ProfileData.coefficient_three

#print axioms KLSConstantImprovement.Raw4047255Quartic141ProfileData.coefficient_four
