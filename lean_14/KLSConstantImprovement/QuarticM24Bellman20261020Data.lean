import KLSConstantImprovement.RoundedAffineBellman
import KLSConstantImprovement.QuarticM24Profile20261020

/-! 23 exact rational Bellman stages with proved downward-rounded affine lines.
The stages and their strict scalar budget comparison are unconditional
arithmetic; the law input is isolated in QuarticM24Profile20261020. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.QuarticM24Bellman20261020Data
open KLSConstantImprovement.PositiveFiniteHeadBellman
open KLSConstantImprovement.QuadraticCapBellmanCertificates
open KLSConstantImprovement.QuarticM24Profile20261020Data
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def ratioUpper : ℝ := (1289543/100000)/K
def A : ℝ := 2/K^2
def chord (r : ℝ) : ℝ := capChord A ratioUpper r
def w (i : ℕ) : ℝ := t (i+2)
def line (i : ℕ) : Affine :=
  if i=0 then ⟨3646853696297/1000000000000,-1861119366523/500000000000⟩ else
  if i=1 then ⟨1699148557541/500000000000,-858569224017/250000000000⟩ else
  if i=2 then ⟨1596790538523/500000000000,-806297222027/250000000000⟩ else
  if i=3 then ⟨1499573638741/500000000000,-30266492959/10000000000⟩ else
  if i=4 then ⟨140726129703/50000000000,-567634313713/200000000000⟩ else
  if i=5 then ⟨131962728823/50000000000,-2659290446631/1000000000000⟩ else
  if i=6 then ⟨1236455286767/500000000000,-1244780531047/500000000000⟩ else
  if i=7 then ⟨2321491143147/1000000000000,-7297515773/3125000000⟩ else
  if i=8 then ⟨546710110281/250000000000,-6869124467/3125000000⟩ else
  if i=9 then ⟨1034139795987/500000000000,-3246223117/1562500000⟩ else
  if i=10 then ⟨392821905237/200000000000,-492954873839/250000000000⟩ else
  if i=11 then ⟨468087818249/250000000000,-1878774152641/1000000000000⟩ else
  if i=12 then ⟨447768768783/250000000000,-1796449924451/1000000000000⟩ else
  if i=13 then ⟨1718533888381/1000000000000,-861522527983/500000000000⟩ else
  if i=14 then ⟨1653190865197/1000000000000,-828489657587/500000000000⟩ else
  if i=15 then ⟨1593693497833/1000000000000,-319373169709/200000000000⟩ else
  if i=16 then ⟨769434575699/500000000000,-308301023991/200000000000⟩ else
  if i=17 then ⟨185961606383/125000000000,-297970161431/200000000000⟩ else
  if i=18 then ⟨1439254767239/1000000000000,-180121963027/125000000000⟩ else
  if i=19 then ⟨1740913777/1250000000,-697020619461/500000000000⟩ else
  if i=20 then ⟨673683974397/500000000000,-674140412069/500000000000⟩ else
  if i=21 then ⟨325784904653/250000000000,-1303668195017/1000000000000⟩ else
  if i=22 then ⟨630010322789/500000000000,-1260177638931/1000000000000⟩ else
  ⟨tTail,-tTail⟩

def exactLine (i : ℕ) : Affine :=
  if i=0 then ⟨2797062133013780991715990226675425120241204528543197118452576122156363/766979529739178581278992843494570524080240043955401411465250000000000,-14005717350346676737836435637538486123730896650496680656108904612378000000/3762713343989518483831118870539935351794365115197933504087366567468536769⟩ else
  if i=1 then ⟨849574278770713018851211/250000000000000000000000,-1717138448033568632346289452086296827/500000000000000000000000000000000000⟩ else
  if i=2 then ⟨798395269261722996280037/250000000000000000000000,-1612594444053741728699407650125294709/500000000000000000000000000000000000⟩ else
  if i=3 then ⟨74978681937058816912471/25000000000000000000000,-151332464794974396050526096936736647/50000000000000000000000000000000000⟩ else
  if i=4 then ⟨70363064851514141638311/25000000000000000000000,-141908578428201275146410664849741527/50000000000000000000000000000000000⟩ else
  if i=5 then ⟨659813644115114275932319/250000000000000000000000,-1329645223315184110112923293724258383/500000000000000000000000000000000000⟩ else
  if i=6 then ⟨30911382169187/12500000000000,-328380338407587027149877179/131902905860625000000000000⟩ else
  if i=7 then ⟨46429822862943/20000000000000,-8170753337412065579505738049/3498944705798400000000000000⟩ else
  if i=8 then ⟨27335505514051/12500000000000,-947151329988099447375300867/430891581661250000000000000⟩ else
  if i=9 then ⟨206827959197411/100000000000000,-163224006354455877883281126121/78564381047400000000000000000⟩ else
  if i=10 then ⟨196410952618539/100000000000000,-147677549689902489700077604321/74894050919840000000000000000⟩ else
  if i=11 then ⟨187235127299621/100000000000000,-134601022263900819758207367841/71643003005280000000000000000⟩ else
  if i=12 then ⟨179107507513257/100000000000000,-123490402957922308036350560449/68741355535240000000000000000⟩ else
  if i=13 then ⟨85926694419091/50000000000000,-28485223468449186765729639681/16531908651970000000000000000⟩ else
  if i=14 then ⟨165319086519757/100000000000000,-105628686425431535962962302049/63747739913320000000000000000⟩ else
  if i=15 then ⟨31873869956679/20000000000000,-3931788149194297034954696841/2462190642236800000000000000⟩ else
  if i=16 then ⟨30777383027967/20000000000000,-3669257834935762456729918489/2380308561702400000000000000⟩ else
  if i=17 then ⟨148769285106461/100000000000000,-85770995066894153915158419721/57570190689560000000000000000⟩ else
  if i=18 then ⟨71962738361969/50000000000000,-20068915646325066637306508761/13927310216000000000000000000⟩ else
  if i=19 then ⟨348182755400064472319741/250000000000000000000000,-697020619460547710858888499250181373/500000000000000000000000000000000000⟩ else
  if i=20 then ⟨168420993599337661224909/125000000000000000000000,-337070206034488005323440667674800077/250000000000000000000000000000000000⟩ else
  if i=21 then ⟨325784904653017018255717/250000000000000000000000,-651834097508381966732246688489081701/500000000000000000000000000000000000⟩ else
  if i=22 then ⟨96641004220720412374072292630291294640558080585566220352613907841154224157316656563/76697952973917858127899284349457052408024004395540141146525000000000000000000000000,-237084360890078279415162975223277172227399203974185551086313802771300798689260346543395705212475981147112530231/188135667199475924191555943526996767589718255759896675204368328373426838450000000000000000000000000000000000000⟩ else
  ⟨tTail,-tTail⟩

def contact (i : ℕ) : ℝ :=
  if i=0 then 2011545721746511484919731183000000000/1939771466949011105551156919657592863 else
  if i=1 then 1036999819857/1000000000000 else
  if i=2 then 1036999819857/1000000000000 else
  if i=3 then 1036999819857/1000000000000 else
  if i=4 then 1036999819857/1000000000000 else
  if i=5 then 1036999819857/1000000000000 else
  if i=6 then 5463767751017/5276116234425 else
  if i=7 then 90392219451743/87473617644960 else
  if i=8 then 17768430150017/17235663266450 else
  if i=9 then 404009908733011/392821905237000 else
  if i=10 then 384288367882639/374470254599200 else
  if i=11 then 366880119744721/358215015026400 else
  if i=12 then 351412013109857/343706777676200 else
  if i=13 then 168775660177791/165319086519700 else
  if i=14 then 325005671374257/318738699566600 else
  if i=15 then 62703972355779/61554766055920 else
  if i=16 then 60574399171067/59507714042560 else
  if i=17 then 292866855528061/287850953447800 else
  if i=18 then 141664800308069/139273102160000 else
  if i=19 then 1017172721153/1000000000000 else
  if i=20 then 1017172721153/1000000000000 else
  if i=21 then 1017172721153/1000000000000 else
  if i=22 then 1947712998424100283914364184555419129475501931039/1939771466949011105551156919657592863000000000000 else
  0

def multiplier (i : ℕ) : ℝ :=
  if i=0 then 1267544061647371741063789906242509767524972609329/484942866737252776387789229914398215750000000000 else
  if i=1 then 116075138926201981148789/250000000000000000000000 else
  if i=2 then 201823310348919503719963/250000000000000000000000 else
  if i=3 then 9547225401394683087529/25000000000000000000000 else
  if i=4 then 3591810106965358361689/25000000000000000000000 else
  if i=5 then 2211305026693224067681/250000000000000000000000 else
  if i=6 then 0 else
  if i=7 then 0 else
  if i=8 then 0 else
  if i=9 then 0 else
  if i=10 then 0 else
  if i=11 then 0 else
  if i=12 then 0 else
  if i=13 then 0 else
  if i=14 then 0 else
  if i=15 then 0 else
  if i=16 then 0 else
  if i=17 then 0 else
  if i=18 then 0 else
  if i=19 then 145222846090527680259/250000000000000000000000 else
  if i=20 then 2081750484868588775091/125000000000000000000000 else
  if i=21 then 8512386426130481744283/250000000000000000000000 else
  if i=22 then 496210277197067798003898445293487178835244825475796860605929/48494286673725277638778922991439821575000000000000000000000000 else
  0

def domainTerm (i : ℕ) (r s : ℝ) : ℝ :=
  if i=0 then s-chord r else
  if i=1 then r-s else
  if i=2 then r-s else
  if i=3 then r-s else
  if i=4 then r-s else
  if i=5 then r-s else
  if i=6 then 0 else
  if i=7 then 0 else
  if i=8 then 0 else
  if i=9 then 0 else
  if i=10 then 0 else
  if i=11 then 0 else
  if i=12 then 0 else
  if i=13 then 0 else
  if i=14 then 0 else
  if i=15 then 0 else
  if i=16 then 0 else
  if i=17 then 0 else
  if i=18 then 0 else
  if i=19 then r-s else
  if i=20 then r-s else
  if i=21 then r-s else
  if i=22 then s-chord r else
  0

theorem A_nonneg : 0 ≤ A := by norm_num [A,K]
theorem ratioUpper_positive : 0<ratioUpper := by norm_num [ratioUpper,K]
theorem p_positive : 0<p := by norm_num [p]
theorem p_interval : 1 ≤ p ∧ p ≤ ratioUpper := by norm_num [p,ratioUpper,K]

theorem line_slope_nonneg (i : ℕ) (hi : i<24) : 0 ≤ (line i).slope := by
  interval_cases i <;> norm_num [line,tTail]

theorem line_at_one (i : ℕ) (hi : i<24) : (line i).eval 1 ≤ 0 := by
  interval_cases i <;> norm_num [line,Affine.eval,tTail]

theorem exactLine_slope_nonneg (i : ℕ) (hi : i<23) : 0 ≤ (exactLine i).slope := by
  interval_cases i <;> norm_num [exactLine]

theorem exactLine_at_one (i : ℕ) (hi : i<23) : (exactLine i).eval 1 ≤ 0 := by
  interval_cases i <;> norm_num [exactLine,Affine.eval]

theorem slope_rounding (i : ℕ) (hi : i<23) : (line i).slope ≤ (exactLine i).slope := by
  interval_cases i <;> norm_num [line,exactLine]

theorem intercept_rounding (i : ℕ) (hi : i<23) : (line i).intercept ≤ (exactLine i).intercept := by
  interval_cases i <;> norm_num [line,exactLine]

theorem multiplier_nonneg (i : ℕ) (hi : i<23) : 0 ≤ multiplier i := by
  interval_cases i <;> norm_num [multiplier]

theorem square_identity (i : ℕ) (hi : i<23) (r s : ℝ) :
    w i*(r-s)+s*(line (i+1)).eval s-(exactLine i).eval r=
      (line (i+1)).slope*(s-contact i)^2+multiplier i*domainTerm i r s := by
  interval_cases i <;>
    norm_num [w,t,tTail,line,exactLine,Affine.eval,contact,multiplier,domainTerm,chord,capChord,A,ratioUpper,K] <;> ring

theorem domainTerm_nonneg (i : ℕ) (r s : ℝ)
    (hs : 1 ≤ s) (hl : capChord A ratioUpper r ≤ s) (hr : s ≤ r) : 0 ≤ domainTerm i r s := by
  have hchord : 0 ≤ s-chord r := sub_nonneg.mpr hl
  have hdrop : 0 ≤ r-s := sub_nonneg.mpr hr
  have hfloor : 0 ≤ s-1 := sub_nonneg.mpr hs
  have hzero : 0 ≤ (0 : ℝ) := le_rfl
  have hIf (P : Prop) [Decidable P] {a b : ℝ}
      (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ (if P then a else b) := by
    by_cases hp : P
    · simpa only [if_pos hp] using ha
    · simpa only [if_neg hp] using hb
  unfold domainTerm
  repeat' (apply hIf <;> try assumption)

theorem stage_certificate (i : ℕ) (hi : i<23) :
    StageCertificate (w i) ratioUpper (capChord A ratioUpper) (line i) (line (i+1)) := by
  have he : StageCertificate (w i) ratioUpper (capChord A ratioUpper) (exactLine i) (line (i+1)) := by
    apply stage_certificate_of_square_identity (domainTerm i)
      (show 0 ≤ w i from (t_positive (i+2) (by omega)).le)
      (exactLine_slope_nonneg i hi) (line_slope_nonneg (i+1) (by omega))
      (exactLine_at_one i hi) (line_at_one (i+1) (by omega))
      (multiplier_nonneg i hi) (square_identity i hi)
    intro r hr hrR s hs hl hsr
    exact domainTerm_nonneg i r s hs hl hsr
  exact RoundedAffineBellman.stage_of_coeff_minorant he
    (line_slope_nonneg i (by omega)) (slope_rounding i hi) (intercept_rounding i hi)

theorem terminal_line (r : ℝ) : (line 23).eval r=tTail*(r-1) := by
  norm_num [line,Affine.eval] <;> ring

theorem strict_budget : C < p*(line 0).positive p := by
  have hh : C < p*(line 0).eval p := by
    norm_num [C,p,line,Affine.eval]
  exact hh.trans_le (mul_le_mul_of_nonneg_left (le_max_right 0 ((line 0).eval p)) p_positive.le)

end KLSConstantImprovement.QuarticM24Bellman20261020Data
#print axioms KLSConstantImprovement.QuarticM24Bellman20261020Data.square_identity
#print axioms KLSConstantImprovement.QuarticM24Bellman20261020Data.stage_certificate
#print axioms KLSConstantImprovement.QuarticM24Bellman20261020Data.strict_budget
