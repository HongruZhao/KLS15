import KLSConstantImprovement.QuadraticCapBellmanCertificates
import KLSConstantImprovement.RefinedTripleWeightedProfile
import CorrelatedCubicRationalTangents239
import KLSConstantImprovement.WeightedOrbitBellmanTail

/-! Six exact rational stages for an unconditional universal Bellman reduction.
The analytic inputs are the retained universal weighted budget, quadratic cap,
power envelope, and old norm bound. The correlated branch adds a proved
cubic tangent with a nonnegative multiplier. -/
noncomputable section
open scoped BigOperators
open Set
namespace KLSConstantImprovement.Cubic239BellmanData
open KLSConstantImprovement.PositiveFiniteHeadBellman
open KLSConstantImprovement.QuadraticCapBellmanCertificates
open KLSConstantImprovement.WeightedOrbitBellmanTail
open KLSBelow25
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def K : ℝ := 127529/10000
def C : ℝ := 1088419043397529663/20000000000000000000
def tau : ℝ := 916608505093/1000000000000
def p : ℝ := 10464583/10000000
def originalC : ℝ := 2537001927307/50000000000000
def t (d : ℕ) : ℝ := RefinedTripleWeightedProfileData.t d
def ratioUpper : ℝ := (13365931903/1000000000)/K
def A : ℝ := 2/K^2
def chord (r : ℝ) : ℝ := capChord A ratioUpper r
def baseW (i : ℕ) : ℝ := if i<6 then t (i+2) else tau
theorem t_positive (d : ℕ) (hd : 2 ≤ d) : 0<t d :=
  RefinedTripleWeightedProfileData.t_positive d hd
theorem t_floor (d : ℕ) (hd : 2 ≤ d) : tau ≤ t d :=
  RefinedTripleWeightedProfileData.t_floor d hd
def w (i : ℕ) : ℝ :=
  if i=0 then 60834687086988807/50000000000000000 else
  if i=1 then 8899556023/7812500000 else
  if i=2 then 223076854643/200000000000 else
  if i=3 then 1026325359413/1000000000000 else
  if i=4 then 482167454109/500000000000 else
  if i=5 then 14381259201/15625000000 else
  tau
def line (i : ℕ) : Affine :=
  if i=0 then ⟨60834687086988807/50000000000000000,-15317463552872058060544865914995949479946750150865151118960573736767719453987615307008921039264757942270415916405816165899497789169455680504564796990766142013825803916750117564892830760447051436029054595264296968269747513411470447258907832072216301208184464741185662764528222247912482252200429395928667110447326836590987977605283028775230091221967138287368624164485415248581681419009349037344545133509914989348161258687789986706856032397849308187838192644170806339514302655690129891367701367725344554576899014977836526446122642207536326172224949655412899937860362387379781194554280456867706984961/12542815537455415075852159643771274924908707530361322913286264879241924709250953815579871876310548366178890894741690978156405839200107587541450255031601171851252362182190017552444658790009792621729608368879583231063274130607475893460103523000733501898305976600091355581182003523037421394757731038787839921835744133883078705153900632597714883903702180729121678270657848682097660692315525999613567107548159650258517535326265351643310266251872212170276864000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩ else
  if i=1 then ⟨8899556023/7812500000,-1895109568205640041901726373007195301813170047305408528171055062779522269218464948821885012584488267868783099008299141620836209620090472192091397376321323549907330974602918123912790337916849516257062551957643699456842446049045319419345487562034903554155617969984022161423865391079439625651501313281/1659122169616005128129956733860038605160155449947790321654451028110814654022002821969055129699217627077195135487146558435860003679917754458720121979405638318755646420023203029179195756011275296047261314119897597750262792000000000000000000000000000000000000000000000000000000000000000000000000000000⟩ else
  if i=2 then ⟨10574603221044429955415244552914116052339453149461968435655185362386021750204171747530301724379265387804526151761923287811068941457043227/9806054509415303001227332400634089794688703455510398197130056284245677959762901193500000000000000000000000000000000000000000000000000000,-21191856135071586515819313882925886223744239834113694402346561763775625577383797576619727354883227820215902001658120750500926580817685955866403916159/19612109018830606002454664801268179589377406911020796394260112568491355919525802387000000000000000000000000000000000000000000000000000000000000000000⟩ else
  if i=3 then ⟨20007038919014627550429642215342260339751465863839089613379329346350355731227692304450482455457725213483517985421059969451431/19612109018830606002454664801268179589377406911020796394260112568491355919525802387000000000000000000000000000000000000000000,-510721419688971650841528176553068901/500000000000000000000000000000000000⟩ else
  if i=4 then ⟨482167454109/500000000000,-18922142578913577863574129509278029011938257909592674517177131974149440089923008482242052886211046897263726014578940030548569/19612109018830606002454664801268179589377406911020796394260112568491355919525802387000000000000000000000000000000000000000000⟩ else
  if i=5 then ⟨6750064176857173834121804009787032770332370029469923/7263675020332174518742495474922500000000000000000000,-67511625215768572079957776971342824590757959264446786196252837/72636750203321745187424954749225000000000000000000000000000000⟩ else
  ⟨tau,-tau⟩
def contact (i : ℕ) : ℝ :=
  if i=0 then 3913753128759152849148301321603691853671888145420287669870741919155853708572966215603804407278844370626565121370284244576896126663648322539506364570360455770700951491939348036096942029032024099072090468025958262731468208239592283670728367562034903554155617969984022161423865391079439625651501313281/3779955378559730185023447853453699739536788560434977892510970104827428573603373155527091532578231913329310682616559665462164314863210039254460868206877217397719400182419426385429390422196782980313219205307041180211605114976357431296000000000000000000000000000000000000000000000000000000000000000000 else
  if i=1 then 43532856191681703644252640592247143913714079001486104466832227995785257141806524992572831598211227820215902001658120750500926580817685955866403916159/42298412884177719821660978211656464209357812597847873742620741449544087000816686990121206897517061551218104607047693151244275765828172908000000000000 else
  if i=2 then 1029184151917/1000000000000 else
  if i=3 then 1029184151917/1000000000000 else
  if i=4 then 137557779056342640063996803917199518172389009264446786196252837/135001283537143476682436080195740655406647400589398460000000000 else
  if i=5 then 8581199570944871065172753/8522719648288435000000000 else
  0
def multiplier (i : ℕ) : ℝ :=
  if i=0 then 0 else
  if i=1 then 0 else
  if i=2 then 362915761046431157207711849760359398462454921433156144325968765049387215450915813901551857723234612195473848238076712188931058542956773/9806054509415303001227332400634089794688703455510398197130056284245677959762901193500000000000000000000000000000000000000000000000000000 else
  if i=3 then 121365918583632940004236797057744295516532041016279356677175135716373712063331934914505863373274786516482014578940030548569/19612109018830606002454664801268179589377406911020796394260112568491355919525802387000000000000000000000000000000000000000000 else
  if i=4 then 0 else
  if i=5 then 37443761052541421987884055625331029/4261359824144217500000000000000000000 else
  0
def domainTerm (i : ℕ) (r s : ℝ) : ℝ :=
  if i=0 then 0 else
  if i=1 then 0 else
  if i=2 then r-s else
  if i=3 then r-s else
  if i=4 then 0 else
  if i=5 then s-chord r else
  0

theorem A_nonneg : 0 ≤ A := by norm_num [A,K]
theorem ratioUpper_positive : 0<ratioUpper := by norm_num [ratioUpper,K]
theorem p_positive : 0<p := by norm_num [p]
theorem p_interval : 1 ≤ p ∧ p ≤ ratioUpper := by norm_num [p,ratioUpper,K]
theorem w_tail (i : ℕ) (hi : 6 ≤ i) : w i=tau := by
  simp only [w,show i≠0 by omega,show i≠1 by omega,show i≠2 by omega,
    show i≠3 by omega,show i≠4 by omega,show i≠5 by omega,ite_false]
theorem w_nonneg (i : ℕ) : 0 ≤ w i := by
  by_cases hi:i<6
  · interval_cases i <;> norm_num [w]
  · rw [w_tail i (by omega)];norm_num [tau]
theorem baseW_le_t (i : ℕ) : baseW i ≤ t (i+2) := by
  unfold baseW
  split_ifs with hi
  · exact le_refl _
  · exact RefinedTripleWeightedProfileData.t_floor (i+2) (by omega)

theorem line_slope_nonneg (i : ℕ) (hi : i<7) : 0 ≤ (line i).slope := by
  interval_cases i <;> norm_num [line,tau]
theorem line_at_one (i : ℕ) (hi : i<7) : (line i).eval 1 ≤ 0 := by
  interval_cases i <;> norm_num [line,Affine.eval,tau]
theorem multiplier_nonneg (i : ℕ) (hi : i<6) : 0 ≤ multiplier i := by
  interval_cases i <;> norm_num [multiplier]
theorem square_identity (i : ℕ) (hi : i<6) (r s : ℝ) :
    w i*(r-s)+s*(line (i+1)).eval s-(line i).eval r=
      (line (i+1)).slope*(s-contact i)^2+multiplier i*domainTerm i r s := by
  interval_cases i <;>
    norm_num [w,line,Affine.eval,contact,multiplier,domainTerm,chord,capChord,A,ratioUpper,K,tau] <;> ring
theorem domainTerm_nonneg (i : ℕ) (r s : ℝ)
    (hs : 1 ≤ s) (hl : capChord A ratioUpper r ≤ s) (hr : s ≤ r) :
    0 ≤ domainTerm i r s := by
  unfold domainTerm
  split_ifs <;> (try dsimp only [chord]) <;> linarith
theorem stage_certificate (i : ℕ) (hi : i<6) :
    StageCertificate (w i) ratioUpper (capChord A ratioUpper) (line i) (line (i+1)) := by
  apply stage_certificate_of_square_identity (domainTerm i)
    (w_nonneg i)
    (line_slope_nonneg i (by omega)) (line_slope_nonneg (i+1) (by omega))
    (line_at_one i (by omega)) (line_at_one (i+1) (by omega))
    (multiplier_nonneg i hi) (square_identity i hi)
  intro r hr hrR s hs hl hsr
  exact domainTerm_nonneg i r s hs hl hsr
theorem terminal_line (r : ℝ) : (line 6).eval r=tau*(r-1) := by
  norm_num [line,Affine.eval] <;> ring
theorem strict_budget : C < p*(line 0).positive p := by
  have hh : C < p*(line 0).eval p := by norm_num [C,p,line,Affine.eval]
  exact hh.trans_le (mul_le_mul_of_nonneg_left (le_max_right 0 ((line 0).eval p)) p_positive.le)
def dualT : ℝ := 322419/500000
def dualWeight : ℝ := 310975204127/250000000000
def dualHeight : ℝ := 2112978171543/100000000000000
def dualMultiplier : ℝ := 34841/200000
def dualPoint : ℝ := dualT^2*(CreationSeed239.seedV dualT)^2
theorem dualPoint_mem : dualPoint ∈ Icc (0 : ℝ) 1 := by
  norm_num [dualPoint,dualT,CreationSeed239.seedV]
theorem dual_weight_le : dualWeight ≤ CreationSeed239.supportWeight dualPoint/K := by
  unfold dualPoint
  rw [CreationSeed239.supportWeight_polynomial_parameter
    (by norm_num [dualT] : 0 ≤ dualT)
    (by norm_num [dualT,CreationSeed239.seedT] : dualT < CreationSeed239.seedT)
    dualPoint_mem.2]
  norm_num [dualWeight,K,dualT,CreationSeed239.B,CreationSeed239.seedV,
    CreationSeed239.seedSlope,CreationSeed239.seedVp]
theorem dual_height_le : CreationSeed239.supportIntercept dualPoint/K^3 ≤ dualHeight := by
  unfold dualPoint
  rw [CreationSeed239.supportIntercept_polynomial_parameter
    (by norm_num [dualT] : 0 ≤ dualT)
    (by norm_num [dualT,CreationSeed239.seedT] : dualT < CreationSeed239.seedT)
    dualPoint_mem.2]
  norm_num [dualHeight,K,dualT,CreationSeed239.B,CreationSeed239.seedV,
    CreationSeed239.seedSlope,CreationSeed239.seedVp]
theorem augmentation_identity (c : ℕ → ℝ) (N : ℕ) :
    spend w c (N+2)=spend baseW c (N+2)+dualMultiplier*(dualWeight*c 0+c 1) := by
  induction N with
  | zero =>
    norm_num [spend,Finset.sum_range_succ,w,baseW,t,RefinedTripleWeightedProfileData.t,
      dualMultiplier,dualWeight]
    ring
  | succ N ih =>
    have hw:w (N+2)=baseW (N+2) := by
      by_cases hi:N+2<6
      · have hn:N ≤ 3 := by omega
        interval_cases N <;> norm_num [w,baseW,t,RefinedTripleWeightedProfileData.t]
      · rw [w_tail (N+2) (by omega)]
        simp [baseW,hi]
    rw [show N+1+2=N+2+1 by omega,spend_succ w c (N+2),spend_succ baseW c (N+2),ih,hw]
    ring
theorem augmented_budget (c : ℕ → ℝ) (hc : ∀ i,0 ≤ c i)
    (hbudget : ∀ N,spend (fun i=>t (i+2)) c N ≤ originalC)
    (hdual : dualWeight*c 0+c 1 ≤ dualHeight) : ∀ N,spend w c N ≤ C := by
  intro N
  have hm:spend w c N ≤ spend w c (N+2) := by
    unfold spend
    rw [Finset.sum_range_add]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=>mul_nonneg (w_nonneg _) (hc _)))
  have hb:spend baseW c (N+2) ≤ originalC := by
    apply (Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (baseW_le_t i) (hc i))).trans
    exact hbudget (N+2)
  have hd:=mul_le_mul_of_nonneg_left hdual
    (by norm_num [dualMultiplier] : 0 ≤ dualMultiplier)
  calc
    spend w c N ≤ spend w c (N+2) := hm
    _ = spend baseW c (N+2)+dualMultiplier*(dualWeight*c 0+c 1) := augmentation_identity c N
    _ ≤ originalC+dualMultiplier*dualHeight := add_le_add hb hd
    _ = C := by norm_num [originalC,dualMultiplier,dualHeight,C]

end KLSConstantImprovement.Cubic239BellmanData
#print axioms KLSConstantImprovement.Cubic239BellmanData.square_identity
#print axioms KLSConstantImprovement.Cubic239BellmanData.stage_certificate
#print axioms KLSConstantImprovement.Cubic239BellmanData.strict_budget
#print axioms KLSConstantImprovement.Cubic239BellmanData.augmented_budget
#print axioms KLSConstantImprovement.Cubic239BellmanData.dual_weight_le
#print axioms KLSConstantImprovement.Cubic239BellmanData.dual_height_le
