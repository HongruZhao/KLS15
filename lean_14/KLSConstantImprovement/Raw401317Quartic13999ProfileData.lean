import KLSConstantImprovement.TriplePositiveEnergyFirstCostTail
import KLSConstantImprovement.ParameterizedWeightedBudget
import KLSConstantImprovement.RawCubicWeightedBudget
import KLSConstantImprovement.PositiveEnergyWeightTail12

/-! Exact rational generator profile for the raw401.317 cubic/quartic head.
This file proves scalar conditions only. Degrees3/4 are paid by the same-test
quartic support in the separate all-rank wrapper. -/
noncomputable section
open Set
open scoped BigOperators
namespace KLSConstantImprovement.Raw401317Quartic13999ProfileData
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def K : ℝ := 1240583350435357/100000000000000
def C : ℝ := 1221312768140013/10000000000000000
def c : ℝ := 603316168816891/25000000000000
def p : ℝ := 1299900000000000/1240583350435357
def tau : ℝ := 1
def alphaTail : ℝ := 38169249659879/100000000000000
def youngTail : ℝ := 608064018442403/25000000000000
def tTail : ℝ := 53941205189817/25000000000000
def tail_J : ℝ := -913347528989256799801724376828104630372059299102593856229538323695816724070498655310010579794245815865674767759694652838199892021185564451082146682571759/5379236100091889494520746878824416450797195607254262618114429659870528368189273516593078583747756466562342589402357959904061413041472996475000000000000
def tail_q : ℝ := 76565275909907440374369708796732060295490872905279245689/375970545151229513088985507630000000000000000000000000000
def tail_b : ℝ := -245848950546956308916020886430504002357895343240121804396217105823948913/20280304321329828136554082995110856251803710000000000000000000000000000
def tail_a : ℝ := 173664366555612688679026758914632707457461522028093111118251532726103399051395057976058729790490894332747485467230428524655606963919674503009578635982759408068159312627/1097587274273647601276884315584420330904634564850937236182689231171534087412601578589871591551413044621641796037023215322209541753312983528188962837442467500000000000
def tail_z : ℝ := -77815308828640679931704852176932602526042686438240972796214441674503639128180772635528452446198605670471637749557203028897192758507067765182168966803339/537923610009188949452074687882441645079719560725426261811442965987052836818927351659307858374775646656234258940235795990406141304147299647500000000000
def alpha (d : ℕ) : ℝ :=
  if d=2 then 1/3 else
  if d=3 then 6190070403251/12500000000000 else
  if d=4 then 22759413926017/50000000000000 else
  if d=5 then 21941340279039/50000000000000 else
  if d=6 then 10718144087313/25000000000000 else
  if d=7 then 21196184622917/50000000000000 else
  if d=8 then 1723479746867/4000000000000 else
  if d=9 then 45978395408209/100000000000000 else
  if d=10 then 41817061453581/100000000000000 else
  if d=11 then 2621630589773/6250000000000 else
  if d=12 then 9043049640919/20000000000000 else
  if d=13 then 8771601177929/20000000000000 else
  if d=14 then 42773124887179/100000000000000 else
  if d=15 then 42076626734041/100000000000000 else
  if d=16 then 41515092581213/100000000000000 else
  if d=17 then 40909145087803/100000000000000 else
  if d=18 then 40522454258991/100000000000000 else
  if d=19 then 20172317473569/50000000000000 else
  if d=20 then 40260820430181/100000000000000 else
  if d=21 then 2513323262203/6250000000000 else
  if d=22 then 40115004519421/100000000000000 else
  if d=23 then 19963627646639/50000000000000 else
  if d=24 then 40069611033219/100000000000000 else
  if d=25 then 39882136629921/100000000000000 else
  if d=26 then 3969888206243/10000000000000 else
  if d=27 then 9881266566429/25000000000000 else
  if d=28 then 39361998095391/100000000000000 else
  if d=29 then 2450530143687/6250000000000 else
  if d=30 then 19531531780533/50000000000000 else
  if d=31 then 38925264864971/100000000000000 else
  if d=32 then 19396829168833/50000000000000 else
  if d=33 then 19335866750151/50000000000000 else
  if d=34 then 7712194156089/20000000000000 else
  if d=35 then 7692081208923/20000000000000 else
  if d=36 then 38371481967541/100000000000000 else
  if d=37 then 38295837813197/100000000000000 else
  if d=38 then 38235372651647/100000000000000 else
  if d=39 then 38192308217569/100000000000000 else
  alphaTail

def young (d : ℕ) : ℝ :=
  if d=2 then 2931138697937/3125000000000 else
  if d=3 then 62819409138903/12500000000000 else
  if d=4 then 371302226068261/50000000000000 else
  if d=5 then 793162776484211/100000000000000 else
  if d=6 then 25496175022627/3125000000000 else
  if d=7 then 416947068666913/50000000000000 else
  if d=8 then 823232781842097/100000000000000 else
  if d=9 then 421145825542163/50000000000000 else
  if d=10 then 123469827460267/12500000000000 else
  if d=11 then 237559156978479/25000000000000 else
  if d=12 then 100656328810279/10000000000000 else
  if d=13 then 277349849389113/25000000000000 else
  if d=14 then 1139792732108647/100000000000000 else
  if d=15 then 301789190613173/20000000000000 else
  if d=16 then 768236223541513/50000000000000 else
  if d=17 then 263054405407303/20000000000000 else
  if d=18 then 331987576158703/20000000000000 else
  if d=19 then 2206306581036721/100000000000000 else
  if d=20 then 605445901213851/25000000000000 else
  if d=21 then 590970040236509/25000000000000 else
  if d=22 then 106318498440139/5000000000000 else
  if d=23 then 455793596659863/25000000000000 else
  youngTail

def t (d : ℕ) : ℝ :=
  if d=2 then 1 else
  if d=3 then 86864022427773/20000000000000 else
  if d=4 then 112519555390813/25000000000000 else
  if d=5 then 96541482001277/25000000000000 else
  if d=6 then 343308683229087/100000000000000 else
  if d=7 then 155686322186421/50000000000000 else
  if d=8 then 280932777977861/100000000000000 else
  if d=9 then 48882573792579/20000000000000 else
  if d=10 then 127175409453041/50000000000000 else
  if d=11 then 121054833706819/50000000000000 else
  tTail

def theta (d : ℕ) : ℝ := if 3 ≤ d ∧ d ≤ 24 then 1 else 0
def lambda (d : ℕ) : ℝ := if 2 ≤ d ∧ d ≤ 23 then 1 else 0

def zeta (d : ℕ) : ℝ :=
  if d=3 then 142857/100000 else
  if d=4 then 70555892488163/50000000000000 else
  if d=5 then 90006533813/162500000000 else
  if d=6 then 80018128029819/200000000000000 else
  if d=7 then 3792388541571/475000000000000 else
  if d=8 then 4441347344679/13750000000000 else
  if d=9 then 5283536249013/25000000000000 else
  if d=10 then 339009/10000000000000 else
  if d=11 then 1005261257/96875000000000 else
  if d=12 then 138055562203741/850000000000000 else
  if d=13 then 59290598022747/740000000000000 else
  if d=14 then 4804712499237/25000000000000 else
  if d=15 then 30647683125223/107500000000000 else
  if d=16 then 86354906630697/287500000000000 else
  if d=17 then 96475294715757/980000000000000 else
  if d=18 then 39083963022543/130000000000000 else
  if d=19 then 330110794447707/550000000000000 else
  if d=20 then 7693862912197/10000000000000 else
  if d=21 then 1991179380715987/6100000000000000 else
  if d=22 then 537643206619519/800000000000000 else
  if d=23 then 205194247437/2680000000000 else
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

theorem t_eq_tail (d : ℕ) (hd : 12 ≤ d) : t d=tTail := by
  simp only [t,show d≠2 by omega,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,ite_false]

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
  by_cases hs:d ≤ 11
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
  by_cases hs:d ≤ 11
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
  have hh:=PositiveEnergyWeightTail12.firstCost_tail young t theta lambda youngTail tTail
    (by norm_num [tTail]) young_eq_tail (fun j hj=>t_eq_tail j (by omega)) d hd
    (theta_eq_zero d (by omega)) (lambda_eq_zero (d-1) (by omega))
  convert hh using 1
  norm_num [PositiveEnergyWeightTail12.ratioPrefix,sum_interval_two,Finset.sum_range_succ,young,youngTail,t,tTail,tail_J]

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

theorem head_value : head profile=(8884159149848737611776933449240443212960237353557644513795809/360892829150072021497283115978277383296217040000000000000000 : ℝ) := by
  norm_num [head,profile,TriplePositiveEnergyWeightedGenerator.head,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]
theorem coefficient_three : coefficient profile 3=(-2081705680669553847788830081154482251925360991680977143455869279065663509032909325778590273162475392789/40916418114765108774775351698837539033228860365777556914915788742717828436761477811440000000000000000 : ℝ) := by
  norm_num [coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]

theorem coefficient_four : coefficient profile 4=(536665406394366651047106015637989249458115513159754553246328835121413114827566554240660929933715666627567172419569732556641593/1069970651051299507743901770332497729309042991560844239299346878439349848462693165039547053980169569937500000000000000000000000 : ℝ) := by
  norm_num [sum_interval_two,Finset.sum_range_succ,coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]


end KLSConstantImprovement.Raw401317Quartic13999ProfileData
#print axioms KLSConstantImprovement.Raw401317Quartic13999ProfileData.coefficient_lower
#print axioms KLSConstantImprovement.Raw401317Quartic13999ProfileData.head_value
#print axioms KLSConstantImprovement.Raw401317Quartic13999ProfileData.coefficient_three

#print axioms KLSConstantImprovement.Raw401317Quartic13999ProfileData.coefficient_four
