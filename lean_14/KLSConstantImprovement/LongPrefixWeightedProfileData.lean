import KLSConstantImprovement.TriplePositiveEnergyFirstCostTail
import KLSConstantImprovement.ParameterizedWeightedBudget

/-! Exact rational scalar profile for the unconditional long-prefix harmonic triple profile.
No floating-point or undischarged analytic certificate is used. -/
noncomputable section
open Set
open scoped BigOperators
namespace KLSConstantImprovement.LongPrefixWeightedProfileData
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def K : ℝ := 12453922967/976562500
def C : ℝ := 5074295116709/100000000000000
def c : ℝ := 1744742289919/125000000000
def p : ℝ := 20961352974117/20000000000000
def tau : ℝ := 916599283453/1000000000000
def alphaTail : ℝ := 349585463997/1000000000000
def youngTail : ℝ := 81329787247/6250000000
def tTail : ℝ := 916599283453/1000000000000
def tail_J : ℝ := -11076313097207744448420002531300236387118659786892262907877797260363165658076229773/62690658321822805707309900399014705012514705390398326181500449127694250000000000
def tail_q : ℝ := 13356048595911024469562261127373161538099359/51658277183086144290762695312500000000000000
def tail_b : ℝ := -704975125336035410326633129360937824228402591818918606627/47349939850433219148085653410300461914062500000000000000
def tail_a : ℝ := 7249268261585741658617042523415078388895830796078499520523798284940200781055831879820421738941/40774915444110990823303589093353293919088670414710170294688461381725361711001082750000000000
def tail_z : ℝ := -10138590096830347757273258246104767856227031524417822753716650532624429553792315647/62690658321822805707309900399014705012514705390398326181500449127694250000000000
def alpha (d : ℕ) : ℝ :=
  if d=2 then 56213565953/125000000000 else
  if d=3 then 579448540843/1000000000000 else
  if d=4 then 214177952959/500000000000 else
  if d=5 then 42057856207/100000000000 else
  if d=6 then 418038351077/1000000000000 else
  if d=7 then 209027346171/500000000000 else
  if d=8 then 40620025039/100000000000 else
  if d=9 then 396587333087/1000000000000 else
  if d=10 then 389546526139/1000000000000 else
  if d=11 then 192115026009/500000000000 else
  if d=12 then 380119625467/1000000000000 else
  if d=13 then 376874012879/1000000000000 else
  if d=14 then 187133504273/500000000000 else
  if d=15 then 372149248139/1000000000000 else
  if d=16 then 370415781077/1000000000000 else
  if d=17 then 368993283123/1000000000000 else
  if d=18 then 367838574251/1000000000000 else
  if d=19 then 366920769779/1000000000000 else
  if d=20 then 366226616687/1000000000000 else
  if d=21 then 73151108921/200000000000 else
  if d=22 then 45690591351/125000000000 else
  if d=23 then 73113975081/200000000000 else
  if d=24 then 36701169041/100000000000 else
  if d=25 then 183400867213/500000000000 else
  if d=26 then 365370150459/1000000000000 else
  if d=27 then 18195897931/50000000000 else
  if d=28 then 181228454739/500000000000 else
  if d=29 then 2256238621/6250000000 else
  if d=30 then 35955248631/100000000000 else
  if d=31 then 71625497701/200000000000 else
  if d=32 then 22295549151/62500000000 else
  if d=33 then 17768023693/50000000000 else
  if d=34 then 14161020771/40000000000 else
  if d=35 then 352726073121/1000000000000 else
  if d=36 then 70292744787/200000000000 else
  if d=37 then 350239722097/1000000000000 else
  if d=38 then 87263797149/250000000000 else
  if d=39 then 173955662997/500000000000 else
  if d=40 then 173404825139/500000000000 else
  if d=41 then 345752265771/1000000000000 else
  if d=42 then 86185552747/250000000000 else
  if d=43 then 171891956031/500000000000 else
  if d=44 then 342883792847/1000000000000 else
  if d=45 then 42756388527/125000000000 else
  if d=46 then 341299090533/1000000000000 else
  if d=47 then 42580816217/125000000000 else
  if d=48 then 340119944823/1000000000000 else
  if d=49 then 16987827291/50000000000 else
  if d=50 then 67921644219/200000000000 else
  if d=51 then 339746792367/1000000000000 else
  if d=52 then 68054142147/200000000000 else
  if d=53 then 34131312899/100000000000 else
  if d=54 then 85762679687/250000000000 else
  if d=55 then 6914229357/20000000000 else
  if d=56 then 349577732521/1000000000000 else
  if d=57 then 349585463997/1000000000000 else
  if d=58 then 349585463997/1000000000000 else
  if d=59 then 349585463997/1000000000000 else
  if d=60 then 349585463997/1000000000000 else
  alphaTail
def young (d : ℕ) : ℝ :=
  if d=2 then 203680097971/250000000000 else
  if d=3 then 120484230889/100000000000 else
  if d=4 then 335809017307/125000000000 else
  if d=5 then 309173241621/100000000000 else
  if d=6 then 3426877352273/1000000000000 else
  if d=7 then 1916385106197/500000000000 else
  if d=8 then 4462814043213/1000000000000 else
  if d=9 then 1021366558901/200000000000 else
  if d=10 then 2866778586759/500000000000 else
  if d=11 then 6343042833311/1000000000000 else
  if d=12 then 347452717493/50000000000 else
  if d=13 then 94265378619/12500000000 else
  if d=14 then 8123484762267/1000000000000 else
  if d=15 then 1087604311127/125000000000 else
  if d=16 then 289605578869/31250000000 else
  if d=17 then 9826126923607/1000000000000 else
  if d=18 then 2594563869377/250000000000 else
  if d=19 then 10923518587633/1000000000000 else
  if d=20 then 5733003588017/500000000000 else
  if d=21 then 2401606632079/200000000000 else
  if d=22 then 12568491228141/1000000000000 else
  if d=23 then 13173477466367/1000000000000 else
  youngTail
def t (d : ℕ) : ℝ :=
  if d=2 then 1 else
  if d=3 then 482469878667/500000000000 else
  if d=4 then 1115409358379/1000000000000 else
  if d=5 then 64146216149/62500000000 else
  if d=6 then 964358305943/1000000000000 else
  if d=7 then 57526425713/62500000000 else
  tTail
def theta (d : ℕ) : ℝ := if 3 ≤ d ∧ d ≤ 24 then 1 else 0
def lambda (d : ℕ) : ℝ := if 2 ≤ d ∧ d ≤ 23 then 1 else 0

def zeta (d : ℕ) : ℝ :=
  if d=3 then 142857/100000 else
  if d=4 then 999999/500000 else
  if d=5 then 538461/200000 else
  if d=6 then 2346846675187/1000000000000 else
  if d=7 then 5205976455183/2375000000000 else
  if d=8 then 105811329513/50000000000 else
  if d=9 then 5218286886879/2500000000000 else
  if d=10 then 2909239597297/1400000000000 else
  if d=11 then 32241062220367/15500000000000 else
  if d=12 then 17794841966811/8500000000000 else
  if d=13 then 311626077581/148000000000 else
  if d=14 then 53244389541/25000000000 else
  if d=15 then 2303548950973/1075000000000 else
  if d=16 then 1560567628617/718750000000 else
  if d=17 then 107457729256701/49000000000000 else
  if d=18 then 359987439441/162500000000 else
  if d=19 then 1538392683373/687500000000 else
  if d=20 then 6556393566261/2900000000000 else
  if d=21 then 69769646085601/30500000000000 else
  if d=22 then 18560437916317/8000000000000 else
  if d=23 then 1586582563731/670000000000 else
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

theorem alpha_eq_tail (d : ℕ) (hd : 61 ≤ d) : alpha d=alphaTail := by
  simp only [alpha,show d≠2 by omega,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,show d≠20 by omega,show d≠21 by omega,show d≠22 by omega,show d≠23 by omega,show d≠24 by omega,show d≠25 by omega,show d≠26 by omega,show d≠27 by omega,show d≠28 by omega,show d≠29 by omega,show d≠30 by omega,show d≠31 by omega,show d≠32 by omega,show d≠33 by omega,show d≠34 by omega,show d≠35 by omega,show d≠36 by omega,show d≠37 by omega,show d≠38 by omega,show d≠39 by omega,show d≠40 by omega,show d≠41 by omega,show d≠42 by omega,show d≠43 by omega,show d≠44 by omega,show d≠45 by omega,show d≠46 by omega,show d≠47 by omega,show d≠48 by omega,show d≠49 by omega,show d≠50 by omega,show d≠51 by omega,show d≠52 by omega,show d≠53 by omega,show d≠54 by omega,show d≠55 by omega,show d≠56 by omega,show d≠57 by omega,show d≠58 by omega,show d≠59 by omega,show d≠60 by omega,ite_false]

theorem young_eq_tail (d : ℕ) (hd : 24 ≤ d) : young d=youngTail := by
  simp only [young,show d≠2 by omega, show d≠3 by omega, show d≠4 by omega, show d≠5 by omega, show d≠6 by omega, show d≠7 by omega, show d≠8 by omega, show d≠9 by omega, show d≠10 by omega, show d≠11 by omega, show d≠12 by omega, show d≠13 by omega, show d≠14 by omega, show d≠15 by omega, show d≠16 by omega, show d≠17 by omega, show d≠18 by omega, show d≠19 by omega, show d≠20 by omega, show d≠21 by omega, show d≠22 by omega, show d≠23 by omega,ite_false]

theorem t_eq_tail (d : ℕ) (hd : 8 ≤ d) : t d=tTail := by
  simp only [t,show d≠2 by omega, show d≠3 by omega, show d≠4 by omega, show d≠5 by omega, show d≠6 by omega, show d≠7 by omega,ite_false]

theorem alpha_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ alpha d := by
  by_cases hs:d ≤ 60
  · interval_cases d <;> norm_num [alpha,alphaTail]
  · rw [alpha_eq_tail d (by omega)];norm_num [alphaTail]

theorem alpha_lt_one (d : ℕ) (hd : 2 ≤ d) : alpha d<1 := by
  by_cases hs:d ≤ 60
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

theorem first_cost_tail (d : ℕ) (hd : 62 ≤ d) :
    PositiveEnergyWeightedDrift.firstCost young t theta lambda d=(youngTail/tTail)*(d : ℝ)+tail_J := by
  have hh:=PositiveEnergyWeightTail.firstCost_tail young t theta lambda youngTail tTail
    (by norm_num [tTail]) young_eq_tail (fun j hj=>t_eq_tail j (by omega)) d (by omega)
    (theta_eq_zero d (by omega)) (lambda_eq_zero (d-1) (by omega))
  convert hh using 1
  norm_num [PositiveEnergyWeightTail.ratioPrefix,sum_interval_two,Finset.sum_range_succ,young,youngTail,t,tTail,tail_J]

theorem raw_first_cost_tail (d : ℕ) (hd : 62 ≤ d) :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta d=
      (youngTail/tTail)*(d : ℝ)+tail_J := by
  rw [TriplePositiveEnergyFirstCostTail.rawFirstCost_eq_of_zero young t theta lambda zeta d
    (by omega) (zeta_eq_zero (d-2) (by omega))]
  exact first_cost_tail d hd

theorem tail_noise_loss (d : ℕ) (hd : 62 ≤ d) :
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda d=generalResidualGeneratorLoss alphaTail d := by
  have hd3:3 ≤ d:=by omega
  have hd2:d≠2:=by omega
  have hr:(62:ℝ) ≤ d:=by exact_mod_cast hd
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

theorem coefficient_finite (d : ℕ) (hd : 4 ≤ d) (hD : d<62) : c ≤ coefficient profile d := by
  interval_cases d <;> norm_num [sum_interval_two,Finset.sum_range_succ,coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]

theorem coefficient_tail_cubic (d : ℕ) (hd : 62 ≤ d) :
    ((d : ℝ)-1)*(coefficient profile d-c)=tail_q*(d : ℝ)^3+tail_b*(d : ℝ)^2+tail_a*(d : ℝ)+tail_z := by
  have hd3:3 ≤ d:=by omega
  have hr:(62:ℝ) ≤ d:=by exact_mod_cast hd
  have hm:(d : ℝ)-1≠0:=by linarith
  change ((d : ℝ)-1)*(TriplePositiveEnergyWeightedGenerator.coefficient K C young t alpha theta lambda zeta d-c)=_
  unfold TriplePositiveEnergyWeightedGenerator.coefficient PositiveEnergyWeightedGenerator.incoming TriplePositiveEnergyWeightedGenerator.cost
  rw [t_eq_tail d (by omega),t_eq_tail (d-1) (by omega),alpha_eq_tail (d-1) (by omega),tail_noise_loss d hd,young_eq_tail d (by omega),ite_eq_left hd3,raw_first_cost_tail d hd]
  rw [show tripleHarmonicNeighborCharge K young zeta d=0 by simp [tripleHarmonicNeighborCharge,zeta_eq_zero d (by omega)]]
  simp only [mul_zero,add_zero]
  norm_num [generalResidualGeneratorLoss,generalResidualA,K,C,c,alphaTail,youngTail,tTail,tail_J,tail_q,tail_b,tail_a,tail_z]
  field_simp
  ring

theorem coefficient_lower (d : ℕ) (hd : 4 ≤ d) : c ≤ coefficient profile d := by
  by_cases hs:d<62
  · exact coefficient_finite d hd hs
  · have hd41:62 ≤ d:=by omega
    have hr:(62:ℝ) ≤ d:=by exact_mod_cast hd41
    have hp:=ParameterizedWeightedBudget.cubic_nonneg_on_tail tail_q tail_b tail_a tail_z 62 d hr
      (by norm_num [tail_q]) (by norm_num [tail_q,tail_b]) (by norm_num [tail_q,tail_b,tail_a])
      (by norm_num [tail_q,tail_b,tail_a,tail_z])
    rw [←coefficient_tail_cubic d hd41] at hp
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by linarith : 0<(d : ℝ)-1)).mp hp)

theorem head_value : head profile=(3559228462490064815174122556547593463699549250544667441/141472662015972757377095653208192828680318554687500000 : ℝ) := by
  norm_num [head,profile,TriplePositiveEnergyWeightedGenerator.head,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]
theorem coefficient_three : coefficient profile 3=(-45018484437917555944193491234296408543949726637633779928499592270630686093315719/1786496448160426445897963664368243024665374214309385523423503417317382812500000 : ℝ) := by
  norm_num [coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]

end KLSConstantImprovement.LongPrefixWeightedProfileData
#print axioms KLSConstantImprovement.LongPrefixWeightedProfileData.coefficient_lower
#print axioms KLSConstantImprovement.LongPrefixWeightedProfileData.head_value
#print axioms KLSConstantImprovement.LongPrefixWeightedProfileData.coefficient_three
