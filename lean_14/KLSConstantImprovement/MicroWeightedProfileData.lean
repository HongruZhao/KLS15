import KLSConstantImprovement.ParameterizedWeightedBudget

/-! Exact rational data and scalar checks for the rounded independent profile.
This module certifies the weighted coefficient sequence. It does not itself
claim a Poincare endpoint. -/
noncomputable section
open Set
open scoped BigOperators
namespace KLSConstantImprovement.MicroWeightedProfileData
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.ParameterizedWeightedBudget
open KLSConstantImprovement.AllRankResidualWeightedGenerator
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def K : ℝ := 6437/500
def C : ℝ := 2477/50000
def c : ℝ := 6809/500
def alphaTail : ℝ := 16904217/50000000
def youngTail : ℝ := 1373848033/100000000
def prefix24 : ℝ := 9017662129/50000000
def alpha (d : ℕ) : ℝ :=
  if d=2 then 22262207/50000000 else
  if d=3 then 1414327/2500000 else
  if d=4 then 48513059/100000000 else
  if d=5 then 44285071/100000000 else
  if d=6 then 20909839/50000000 else
  if d=7 then 40271721/100000000 else
  if d=8 then 39219813/100000000 else
  if d=9 then 19229337/50000000 else
  if d=10 then 37887237/100000000 else
  if d=11 then 18724149/50000000 else
  if d=12 then 9275397/25000000 else
  if d=13 then 3682271/10000000 else
  if d=14 then 9147757/25000000 else
  if d=15 then 18199087/50000000 else
  if d=16 then 3623941/10000000 else
  if d=17 then 18053943/50000000 else
  if d=18 then 35999021/100000000 else
  if d=19 then 17955553/50000000 else
  if d=20 then 35842727/100000000 else
  if d=21 then 7157951/20000000 else
  if d=22 then 1429919/4000000 else
  if d=23 then 35713189/100000000 else
  if d=24 then 357347/1000000 else
  if d=25 then 17842937/50000000 else
  if d=26 then 35513587/100000000 else
  if d=27 then 7068911/20000000 else
  if d=28 then 17589833/50000000 else
  if d=29 then 35019591/100000000 else
  if d=30 then 4358109/12500000 else
  if d=31 then 6943199/20000000 else
  if d=32 then 2160841/6250000 else
  if d=33 then 17218923/50000000 else
  if d=34 then 8577483/25000000 else
  if d=35 then 17095389/50000000 else
  if d=36 then 34081887/100000000 else
  if d=37 then 16992707/50000000 else
  if d=38 then 33904441/100000000 else
  if d=39 then 33843367/100000000 else
  if d=40 then 16904217/50000000 else
  alphaTail
def young (d : ℕ) : ℝ :=
  if d=2 then 41189303/50000000 else
  if d=3 then 1561391/1250000 else
  if d=4 then 108916361/50000000 else
  if d=5 then 38235793/12500000 else
  if d=6 then 386631029/100000000 else
  if d=7 then 230234777/50000000 else
  if d=8 then 106426981/20000000 else
  if d=9 then 602210483/100000000 else
  if d=10 then 335738557/50000000 else
  if d=11 then 14858743/2000000 else
  if d=12 then 101325091/12500000 else
  if d=13 then 877041463/100000000 else
  if d=14 then 37553873/4000000 else
  if d=15 then 1005536651/100000000 else
  if d=16 then 215523729/20000000 else
  if d=17 then 1142172911/100000000 else
  if d=18 then 1204047497/100000000 else
  if d=19 then 1272911019/100000000 else
  if d=20 then 669509023/50000000 else
  if d=21 then 346810983/25000000 else
  if d=22 then 1418246413/100000000 else
  if d=23 then 1435170941/100000000 else
  youngTail
def zeta2 (d : ℕ) : ℝ :=
  if d=2 then 12626301/100000000 else
  if d=3 then 4046067/6250000 else
  if d=4 then 4007013/5000000 else
  if d=5 then 18306567/20000000 else
  if d=6 then 48213921/50000000 else
  if d=7 then 24455739/25000000 else
  if d=8 then 24651603/25000000 else
  if d=9 then 19800207/20000000 else
  if d=10 then 2482117/2500000 else
  if d=11 then 25066041/25000000 else
  if d=12 then 10023819/10000000 else
  if d=13 then 100012913/100000000 else
  if d=14 then 1977591/2000000 else
  if d=15 then 9891/10000 else
  if d=16 then 12498179/12500000 else
  if d=17 then 99651807/100000000 else
  if d=18 then 98944191/100000000 else
  if d=19 then 9944391/10000000 else
  if d=20 then 4976013/5000000 else
  if d=21 then 12134661/12500000 else
  if d=22 then 92531967/100000000 else
  if d=23 then 10819131/12500000 else
  0
def zeta3 (d : ℕ) : ℝ :=
  if d=2 then 0 else
  if d=3 then 142857/100000 else
  if d=4 then 999999/500000 else
  if d=5 then 538461/200000 else
  if d=6 then 137173561/50000000 else
  if d=7 then 37623033/14843750 else
  if d=8 then 33331731/13750000 else
  if d=9 then 74252277/31250000 else
  if d=10 then 8233093/3500000 else
  if d=11 then 3671517421/1550000000 else
  if d=12 then 1009109829/425000000 else
  if d=13 then 1762410377/740000000 else
  if d=14 then 119585949/50000000 else
  if d=15 then 259807243/107500000 else
  if d=16 then 35453721/14375000 else
  if d=17 then 6090972177/2450000000 else
  if d=18 then 651219813/260000000 else
  if d=19 then 1399547163/550000000 else
  if d=20 then 747612789/290000000 else
  if d=21 then 7840112511/3050000000 else
  if d=22 then 99160567/40000000 else
  if d=23 then 81933797/33500000 else
  0

def profile : Parameters where
  K := K
  C := C
  c := c
  alpha := alpha
  young := young
  zeta2 := zeta2
  zeta3 := zeta3

theorem alpha_eq_tail (d : ℕ) (hd : 41 ≤ d) : alpha d=alphaTail := by
  simp only [alpha,show d≠2 by omega, show d≠3 by omega, show d≠4 by omega, show d≠5 by omega, show d≠6 by omega, show d≠7 by omega, show d≠8 by omega, show d≠9 by omega, show d≠10 by omega, show d≠11 by omega, show d≠12 by omega, show d≠13 by omega, show d≠14 by omega, show d≠15 by omega, show d≠16 by omega, show d≠17 by omega, show d≠18 by omega, show d≠19 by omega, show d≠20 by omega, show d≠21 by omega, show d≠22 by omega, show d≠23 by omega, show d≠24 by omega, show d≠25 by omega, show d≠26 by omega, show d≠27 by omega, show d≠28 by omega, show d≠29 by omega, show d≠30 by omega, show d≠31 by omega, show d≠32 by omega, show d≠33 by omega, show d≠34 by omega, show d≠35 by omega, show d≠36 by omega, show d≠37 by omega, show d≠38 by omega, show d≠39 by omega, show d≠40 by omega,ite_false]

theorem young_eq_tail (d : ℕ) (hd : 24 ≤ d) : young d=youngTail := by
  simp only [young,show d≠2 by omega, show d≠3 by omega, show d≠4 by omega, show d≠5 by omega, show d≠6 by omega, show d≠7 by omega, show d≠8 by omega, show d≠9 by omega, show d≠10 by omega, show d≠11 by omega, show d≠12 by omega, show d≠13 by omega, show d≠14 by omega, show d≠15 by omega, show d≠16 by omega, show d≠17 by omega, show d≠18 by omega, show d≠19 by omega, show d≠20 by omega, show d≠21 by omega, show d≠22 by omega, show d≠23 by omega,ite_false]

theorem zeta2_eq_tail (d : ℕ) (hd : 24 ≤ d) : zeta2 d=0 := by
  simp only [zeta2,show d≠2 by omega, show d≠3 by omega, show d≠4 by omega, show d≠5 by omega, show d≠6 by omega, show d≠7 by omega, show d≠8 by omega, show d≠9 by omega, show d≠10 by omega, show d≠11 by omega, show d≠12 by omega, show d≠13 by omega, show d≠14 by omega, show d≠15 by omega, show d≠16 by omega, show d≠17 by omega, show d≠18 by omega, show d≠19 by omega, show d≠20 by omega, show d≠21 by omega, show d≠22 by omega, show d≠23 by omega,ite_false]

theorem zeta3_eq_tail (d : ℕ) (hd : 24 ≤ d) : zeta3 d=0 := by
  simp only [zeta3,show d≠2 by omega, show d≠3 by omega, show d≠4 by omega, show d≠5 by omega, show d≠6 by omega, show d≠7 by omega, show d≠8 by omega, show d≠9 by omega, show d≠10 by omega, show d≠11 by omega, show d≠12 by omega, show d≠13 by omega, show d≠14 by omega, show d≠15 by omega, show d≠16 by omega, show d≠17 by omega, show d≠18 by omega, show d≠19 by omega, show d≠20 by omega, show d≠21 by omega, show d≠22 by omega, show d≠23 by omega,ite_false]

theorem alpha_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ alpha d := by
  by_cases hs : d ≤ 40
  · interval_cases d <;> norm_num [alpha,alphaTail]
  · rw [alpha_eq_tail d (by omega)]; norm_num [alphaTail]
theorem alpha_lt_one (d : ℕ) (hd : 2 ≤ d) : alpha d < 1 := by
  by_cases hs : d ≤ 40
  · interval_cases d <;> norm_num [alpha,alphaTail]
  · rw [alpha_eq_tail d (by omega)]; norm_num [alphaTail]
theorem alpha_low (d : ℕ) (hd : 4 ≤ d) : alpha d ≤ ((d : ℝ)-1)/((d : ℝ)+1) := by
  have ha : alpha d ≤ (3 : ℝ)/5 := by
    by_cases hs : d ≤ 40
    · interval_cases d <;> norm_num [alpha,alphaTail]
    · rw [alpha_eq_tail d (by omega)]; norm_num [alphaTail]
  have hr : (4 : ℝ) ≤ d := by exact_mod_cast hd
  apply ha.trans
  apply (le_div_iff₀ (by linarith : 0 < (d : ℝ)+1)).mpr
  nlinarith
theorem young_positive (d : ℕ) (hd : 2 ≤ d) : 0 < young d := by
  by_cases hs : d ≤ 23
  · interval_cases d <;> norm_num [young,youngTail]
  · rw [young_eq_tail d (by omega)]; norm_num [youngTail]
theorem zeta2_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ zeta2 d := by
  by_cases hs : d ≤ 23
  · interval_cases d <;> norm_num [zeta2]
  · rw [zeta2_eq_tail d (by omega)] <;> norm_num
theorem zeta3_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ zeta3 d := by
  by_cases hs : d ≤ 23
  · interval_cases d <;> norm_num [zeta3]
  · rw [zeta3_eq_tail d (by omega)] <;> norm_num
theorem zeta2_cap (d : ℕ) (hd : 2 ≤ d) : 2*zeta2 d < (d : ℝ)*((d : ℝ)+1) := by
  by_cases hs : d ≤ 23
  · interval_cases d <;> norm_num [zeta2]
  · rw [zeta2_eq_tail d (by omega)]
    have hr : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
theorem zeta3_cap (d : ℕ) (hd : 2 ≤ d) : tripleHarmonicRatio (d : ℝ)*zeta3 d < 1 := by
  by_cases hs : d ≤ 23
  · interval_cases d <;> norm_num [zeta3,tripleHarmonicRatio,TripleCreation.chargeRatio]
  · rw [zeta3_eq_tail d (by omega)] <;> norm_num

theorem proper_prefix_succ (d : ℕ) (hd : 2 ≤ d) :
    properYoungPrefix young (d+1)=young d+properYoungPrefix young d := by
  classical
  have hs : Finset.Icc 2 d = insert d (Finset.Icc 2 (d-1)) := by
    ext b; simp only [Finset.mem_Icc,Finset.mem_insert]; omega
  have hn : d ∉ Finset.Icc 2 (d-1) := by simp only [Finset.mem_Icc]; omega
  unfold properYoungPrefix
  rw [Nat.add_sub_cancel,hs,Finset.sum_insert hn]

def prefixExact (d : ℕ) : ℝ := if d ≤ 24 then
  if d=2 then 0 else
  if d=3 then 41189303/50000000 else
  if d=4 then 103644943/50000000 else
  if d=5 then 26570163/6250000 else
  if d=6 then 91376119/12500000 else
  if d=7 then 1117639981/100000000 else
  if d=8 then 315621907/20000000 else
  if d=9 then 52756111/2500000 else
  if d=10 then 2712454923/100000000 else
  if d=11 then 3383932037/100000000 else
  if d=12 then 4126869187/100000000 else
  if d=13 then 987493983/20000000 else
  if d=14 then 2907255689/50000000 else
  if d=15 then 6753358203/100000000 else
  if d=16 then 3879447427/50000000 else
  if d=17 then 8836513499/100000000 else
  if d=18 then 997868641/10000000 else
  if d=19 then 11182733907/100000000 else
  if d=20 then 6227822463/50000000 else
  if d=21 then 3448665743/25000000 else
  if d=22 then 1897738363/12500000 else
  if d=23 then 16600153317/100000000 else
  if d=24 then 9017662129/50000000 else
  0 else prefix24+((d : ℝ)-24)*youngTail

theorem proper_prefix_eq (d : ℕ) (hd : 2 ≤ d) : properYoungPrefix young d=prefixExact d := by
  induction d,hd using Nat.le_induction with
  | base => norm_num [properYoungPrefix,prefixExact]
  | succ d hd ih =>
    rw [proper_prefix_succ d hd,ih]
    by_cases hs : d ≤ 23
    · interval_cases d <;> norm_num [prefixExact,young]
    · by_cases he : d=24
      · subst d; norm_num [prefixExact,young,youngTail,prefix24]
      · have hd25 : 25 ≤ d := by omega
        simp only [prefixExact,show ¬d ≤ 24 by omega,show ¬d+1 ≤ 24 by omega,ite_false]
        rw [young_eq_tail d (by omega)]
        push_cast
        ring

theorem proper_prefix_tail (d : ℕ) (hd : 24 ≤ d) :
    properYoungPrefix young d=prefix24+((d : ℝ)-24)*youngTail := by
  rw [proper_prefix_eq d (by omega)]
  by_cases he : d=24
  · subst d; norm_num [prefixExact,prefix24]
  · simp only [prefixExact,show ¬d ≤ 24 by omega,ite_false]

theorem coefficient_finite (d : ℕ) (hd : 4 ≤ d) (hD : d < 41) : c ≤ coefficient profile d := by
  interval_cases d <;> norm_num [coefficient,cost,profile,allRankJointCubicTailCoefficient,allRankResidualGeneratorLoss,appellGeneralResidualGeneratorLoss,appellSymmetricCubicGeneratorLoss,appellSymmetricQuadraticGeneratorLoss,appellGeneratorLoss,generalResidualGeneratorLoss,generalResidualA,cubicExcludedHarmonicCost,twoRowsHarmonicFirstCost,proper_prefix_eq,prefixExact,harmonicBudgetDenom,harmonicRatioDenom,selectedHarmonicDenom,harmonicNeighborCharge,tripleHarmonicNeighborCharge,tripleHarmonicRatio,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,K,C,c,alpha,alphaTail,young,youngTail,prefix24,zeta2,zeta3]
def tail_q : ℝ := 298966209615005850571587531/1136714409378620975000000000
def tail_b : ℝ := -16327235372635814063134509281/1136714409378620975000000000
def tail_a : ℝ := 497147819911816961/3309578300000000
def tail_z : ℝ := -6737614267/50000000

theorem coefficient_tail_cubic (d : ℕ) (hd : 41 ≤ d) :
    ((d : ℝ)-1)*(coefficient profile d-c)=
      tail_q*(d : ℝ)^3+tail_b*(d : ℝ)^2+tail_a*(d : ℝ)+tail_z := by
  have hd4 : 4 ≤ d := by omega
  have hd3 : 3 ≤ d := by omega
  have hda : alpha (d-1)=alphaTail := by
    by_cases he : d=41
    · subst d; norm_num [alpha,alphaTail]
    · exact alpha_eq_tail (d-1) (by omega)
  have hr : (41 : ℝ) ≤ d := by exact_mod_cast hd
  have hm : (d : ℝ)-1 ≠ 0 := by linarith
  simp only [coefficient,cost,profile,allRankJointCubicTailCoefficient,
    allRankResidualGeneratorLoss,ite_eq_left hd4]
  unfold cubicExcludedHarmonicCost twoRowsHarmonicFirstCost harmonicNeighborCharge tripleHarmonicNeighborCharge
  rw [hda,alpha_eq_tail d hd,young_eq_tail d (by omega),zeta2_eq_tail d (by omega),
    zeta3_eq_tail d (by omega),zeta2_eq_tail (d-1) (by omega),zeta3_eq_tail (d-2) (by omega),
    proper_prefix_tail d (by omega)]
  simp only [ite_eq_left hd4,ite_eq_left hd3,zero_mul,mul_zero,zero_div,
    harmonicBudgetDenom,harmonicRatioDenom,selectedHarmonicDenom,add_zero,div_one,sub_self,sub_zero]
  norm_num [generalResidualGeneratorLoss,generalResidualA,K,C,c,alphaTail,youngTail,prefix24,
    tail_q,tail_b,tail_a,tail_z]
  field_simp
  ring

theorem coefficient_lower (d : ℕ) (hd : 4 ≤ d) : c ≤ coefficient profile d := by
  apply coefficient_lower_of_finite_and_cubic_tail profile 41 (by omega)
    tail_q tail_b tail_a tail_z
  · exact coefficient_finite
  · exact coefficient_tail_cubic
  · norm_num [tail_q]
  · norm_num [tail_q,tail_b]
  · norm_num [tail_q,tail_b,tail_a]
  · norm_num [tail_q,tail_b,tail_a,tail_z]
  · exact hd

theorem head_value : head profile=(31698465357203463048529219/1278165609454533311385477 : ℝ) := by
  norm_num [head,profile,jointCubicHeadCoefficient,cost,cubicExcludedHarmonicCost,tripleHarmonicNeighborCharge,zeta3,alpha,young,K,C,alphaTail,youngTail]
theorem coefficient_three : coefficient profile 3=(-39802511644460010262944438490723/1755972604228715489175000000000 : ℝ) := by
  norm_num [coefficient,cost,profile,allRankJointCubicTailCoefficient,allRankResidualGeneratorLoss,appellGeneralResidualGeneratorLoss,appellSymmetricCubicGeneratorLoss,appellSymmetricQuadraticGeneratorLoss,appellGeneratorLoss,generalResidualGeneratorLoss,generalResidualA,cubicExcludedHarmonicCost,twoRowsHarmonicFirstCost,proper_prefix_eq,prefixExact,harmonicBudgetDenom,harmonicRatioDenom,selectedHarmonicDenom,harmonicNeighborCharge,tripleHarmonicNeighborCharge,tripleHarmonicRatio,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.exactCap,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,K,C,c,alpha,alphaTail,young,youngTail,prefix24,zeta2,zeta3]
end KLSConstantImprovement.MicroWeightedProfileData
#print axioms KLSConstantImprovement.MicroWeightedProfileData.coefficient_lower
#print axioms KLSConstantImprovement.MicroWeightedProfileData.head_value
#print axioms KLSConstantImprovement.MicroWeightedProfileData.coefficient_three
