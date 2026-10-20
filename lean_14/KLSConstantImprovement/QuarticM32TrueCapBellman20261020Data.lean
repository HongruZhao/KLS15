import KLSConstantImprovement.ExactQuadraticCapBellmanCertificates
import KLSConstantImprovement.QuarticM32Profile20261020

/-! Exact true quadratic-cap improvement with rigorously rounded affine lines. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.QuarticM32TrueCapBellman20261020Data
open PositiveFiniteHeadBellman QuadraticCapBellmanCertificates ExactQuadraticCapBellmanCertificates
open KLSConstantImprovement.QuarticM32Profile20261020Data
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def q : ℝ := 128409500000000/122144150200807
def ratioUpper : ℝ := (1289543/100000)/K
def A : ℝ := 2/K^2
def w (i : ℕ) : ℝ := t (i+2)
def line (i : ℕ) : Affine :=
  if i=0 then ⟨4640845498649/1000000000000,-949044792077/200000000000⟩ else
  if i=1 then ⟨4314486271719/1000000000000,-4364347379599/1000000000000⟩ else
  if i=2 then ⟨404641232949/100000000000,-4090262159253/1000000000000⟩ else
  if i=3 then ⟨3792293736611/1000000000000,-1915254901157/500000000000⟩ else
  if i=4 then ⟨221966492699/62500000000,-358440395737/100000000000⟩ else
  if i=5 then ⟨1661643208647/500000000000,-418911184543/125000000000⟩ else
  if i=6 then ⟨776788479313/250000000000,-39131763047/12500000000⟩ else
  if i=7 then ⟨1454836905223/500000000000,-2929021457123/1000000000000⟩ else
  if i=8 then ⟨683445478771/250000000000,-1374881435597/500000000000⟩ else
  if i=9 then ⟨2578943566079/1000000000000,-2592185889891/1000000000000⟩ else
  if i=10 then ⟨305396587391/125000000000,-613552409829/250000000000⟩ else
  if i=11 then ⟨1162027420991/500000000000,-2333318814729/1000000000000⟩ else
  if i=12 then ⟨1109606915303/500000000000,-278380951401/125000000000⟩ else
  if i=13 then ⟨265812477061/125000000000,-1066586168167/500000000000⟩ else
  if i=14 then ⟨1022021783611/500000000000,-2049765113737/1000000000000⟩ else
  if i=15 then ⟨985126388461/500000000000,-79007516211/40000000000⟩ else
  if i=16 then ⟨237972809303/125000000000,-477015079783/250000000000⟩ else
  if i=17 then ⟨460870290509/250000000000,-369440626341/200000000000⟩ else
  if i=18 then ⟨1788375410309/1000000000000,-17916213997/10000000000⟩ else
  if i=19 then ⟨1737639019499/1000000000000,-69618885463/40000000000⟩ else
  if i=20 then ⟨1690565642247/1000000000000,-1693035780233/1000000000000⟩ else
  if i=21 then ⟨823272792897/500000000000,-1648692113921/1000000000000⟩ else
  if i=22 then ⟨1605046535393/1000000000000,-321380063987/200000000000⟩ else
  if i=23 then ⟨78279879183/50000000000,-48974453023/31250000000⟩ else
  if i=24 then ⟨763886358123/500000000000,-764553352929/500000000000⟩ else
  if i=25 then ⟨1491179461897/1000000000000,-746137653217/500000000000⟩ else
  if i=26 then ⟨45482763819/31250000000,-91019639551/62500000000⟩ else
  if i=27 then ⟨284074965579/200000000000,-1421016108449/1000000000000⟩ else
  if i=28 then ⟨1385947802331/1000000000000,-693185007251/500000000000⟩ else
  if i=29 then ⟨338039179041/250000000000,-270473040221/200000000000⟩ else
  if i=30 then ⟨1318991084813/1000000000000,-659495542407/500000000000⟩ else
  ⟨tTail,-tTail⟩

def exactLine (i : ℕ) : Affine :=
  if i=0 then ⟨72193748704269974244727192767920762660761/15556162928776061299528296361000000000000,-667049895477855373891743752176379450000/140572900467225283889948797890341128927⟩ else
  if i=1 then ⟨215724313585973876238867/50000000000000000000000,-436434737959821258839007980840556261/100000000000000000000000000000000000⟩ else
  if i=2 then ⟨2023206164745456668838613/500000000000000000000000,-4090262159252308759621941775980606579/1000000000000000000000000000000000000⟩ else
  if i=3 then ⟨118509179269101294073117/31250000000000000000000,-239406862644564928953511926384124011/62500000000000000000000000000000000⟩ else
  if i=4 then ⟨887865970796078756850001/250000000000000000000000,-1792201978684590326999043219026800983/500000000000000000000000000000000000⟩ else
  if i=5 then ⟨415410802161863862414679/125000000000000000000000,-837822369085915998506815753120379457/250000000000000000000000000000000000⟩ else
  if i=6 then ⟨62143078345047/20000000000000,-14574165260086158691761075049/4655478096713600000000000000⟩ else
  if i=7 then ⟨290967381044679/100000000000000,-320292235535013166230465918241/109351276603360000000000000000⟩ else
  if i=8 then ⟨273378191508407/100000000000000,-283659330596309652702433215049/103157742643160000000000000000⟩ else
  if i=9 then ⟨4029599321999/1562500000000,-989555905819593239352105841/381745734238750000000000000⟩ else
  if i=10 then ⟨244317269912887/100000000000000,-228148711819562467182505609369/92962193679280000000000000000⟩ else
  if i=11 then ⟨232405484198257/100000000000000,-207125335394372243979727369249/88768553224240000000000000000⟩ else
  if i=12 then ⟨110960691530321/50000000000000,-47358163365435803883359574441/21264998164880000000000000000⟩ else
  if i=13 then ⟨42529996329769/20000000000000,-6976475506972393102795131081/3270469707555200000000000000⟩ else
  if i=14 then ⟨204404356722221/100000000000000,-161542216295120909446334577841/78810111076880000000000000000⟩ else
  if i=15 then ⟨2462815971153/1250000000000,-1468878170998736882895289/743665029071875000000000⟩ else
  if i=16 then ⟨190378247442463/100000000000000,-140698930173916677642283639369/73739246481440000000000000000⟩ else
  if i=17 then ⟨92174058101813/50000000000000,-33034926585853799861664496969/17883754103090000000000000000⟩ else
  if i=18 then ⟨35767508206187/20000000000000,-4981106003660677908556909969/2780222431198400000000000000⟩ else
  if i=19 then ⟨34752780389999/20000000000000,-1569270610869695545252175427/901635009198400000000000000⟩ else
  if i=20 then ⟨6762262568989/4000000000000,-59470092598025684111585643/35126305830272000000000000⟩ else
  if i=21 then ⟨82327279289743/50000000000000,-26462275653775972704948239049/16050465353930000000000000000⟩ else
  if i=22 then ⟨160504653539363/100000000000000,-9148215483896444657139203579/5693082122400000000000000000⟩ else
  if i=23 then ⟨156559758366081/100000000000000,-31923982131887075285404479387/20370302883280000000000000000⟩ else
  if i=24 then ⟨19097158953083/12500000000000,-2873201253558859455598359/1879006378398437500000000⟩ else
  if i=25 then ⟨149117946189779/100000000000000,-28959063601258495613966720547/19405979229440000000000000000⟩ else
  if i=26 then ⟨18193105527600223742609/12500000000000000000000,-4550981977549020971649221232716739/3125000000000000000000000000000000⟩ else
  if i=27 then ⟨88773426743494861864001/62500000000000000000000,-22203376694515473728399153847887571/15625000000000000000000000000000000⟩ else
  if i=28 then ⟨21655434411427376495411/15625000000000000000000,-5415507869148126750109181543052681/3906250000000000000000000000000000⟩ else
  if i=29 then ⟨84509794760294185887223/62500000000000000000000,-21130706267259827889227244236693333/15625000000000000000000000000000000⟩ else
  if i=30 then ⟨16487388560167/12500000000000,-16487388560167/12500000000000⟩ else
  ⟨tTail,-tTail⟩

def contact (i : ℕ) : ℝ :=
  if i=0 then 4653999911500000000/4481276930060150419 else
  if i=1 then 1038543250983/1000000000000 else
  if i=2 then 1038543250983/1000000000000 else
  if i=3 then 1038543250983/1000000000000 else
  if i=4 then 1038543250983/1000000000000 else
  if i=5 then 1038543250983/1000000000000 else
  if i=6 then 120723507487507/116386952417840 else
  if i=7 then 565943668164079/546756383016800 else
  if i=8 then 532596780497507/515788713215800 else
  if i=9 then 31457207533721/30539658739100 else
  if i=10 then 477649151385787/464810968396400 else
  if i=11 then 455110245319057/443842766121200 else
  if i=12 then 217619308347021/212649981648800 else
  if i=13 then 83525298604509/81761742688880 else
  if i=14 then 401923147249721/394050555384400 else
  if i=15 then 1211972842517/1189864046515 else
  if i=16 then 375098560612963/368696232407200 else
  if i=17 then 181755128086813/178837541030900 else
  if i=18 then 70576950937687/69505560779960 else
  if i=19 then 22871165331553/22540875229960 else
  if i=20 then 4452343674891/4390788228784 else
  if i=21 then 162672295286493/160504653539300 else
  if i=22 then 28838445746633/28465410612000 else
  if i=23 then 103156809650627/101851514416400 else
  if i=24 then 1217761299468/1202564082175 else
  if i=25 then 98249789823793/97029896147200 else
  if i=26 then 126571543571/125000000000 else
  if i=27 then 126571543571/125000000000 else
  if i=28 then 126571543571/125000000000 else
  if i=29 then 126571543571/125000000000 else
  if i=30 then 1 else
  0

def multiplier (i : ℕ) : ℝ :=
  if i=0 then 112840779075295339684857976686133/32977999380500000000000000000000 else
  if i=1 then 31812837607702623761133/50000000000000000000000 else
  if i=2 then 541548351743833331161387/500000000000000000000000 else
  if i=3 then 16320638671571518426883/31250000000000000000000 else
  if i=4 then 51705771868428743149999/250000000000000000000000 else
  if i=5 then 3360754085458637585321/125000000000000000000000 else
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
  if i=19 then 0 else
  if i=20 then 0 else
  if i=21 then 0 else
  if i=22 then 0 else
  if i=23 then 0 else
  if i=24 then 0 else
  if i=25 then 0 else
  if i=26 then 55832324078651257391/12500000000000000000000 else
  if i=27 then 933247961942013135999/62500000000000000000000 else
  if i=28 then 406607869429967254589/15625000000000000000000 else
  if i=29 then 2352479336920814112777/62500000000000000000000 else
  if i=30 then 0 else
  0

def contactR : ℝ := 128409500000000/122144150200807

def domainTerm (i : ℕ) (r s : ℝ) : ℝ :=
  if i=0 then 0 else
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
  if i=19 then 0 else
  if i=20 then 0 else
  if i=21 then 0 else
  if i=22 then 0 else
  if i=23 then 0 else
  if i=24 then 0 else
  if i=25 then 0 else
  if i=26 then r-s else
  if i=27 then r-s else
  if i=28 then r-s else
  if i=29 then r-s else
  if i=30 then 0 else
  0

theorem A_nonneg : 0 ≤ A := by norm_num [A,K]
theorem ratioUpper_positive : 0<ratioUpper := by norm_num [ratioUpper,K]
theorem q_positive : 0<q := by norm_num [q]
theorem q_interval : 1 ≤ q ∧ q ≤ ratioUpper := by norm_num [q,ratioUpper,K]

theorem line_slope_nonneg (i : ℕ) (hi : i<32) : 0 ≤ (line i).slope := by
  interval_cases i <;> norm_num [line,tTail]

theorem line_at_one (i : ℕ) (hi : i<32) : (line i).eval 1 ≤ 0 := by
  interval_cases i <;> norm_num [line,Affine.eval,tTail]

theorem exactLine_slope_nonneg (i : ℕ) (hi : i<31) : 0 ≤ (exactLine i).slope := by
  interval_cases i <;> norm_num [exactLine]

theorem exactLine_at_one (i : ℕ) (hi : i<31) : (exactLine i).eval 1 ≤ 0 := by
  interval_cases i <;> norm_num [exactLine,Affine.eval]

theorem slope_rounding (i : ℕ) (hi : i<31) : (line i).slope ≤ (exactLine i).slope := by
  interval_cases i <;> norm_num [line,exactLine]

theorem intercept_rounding (i : ℕ) (hi : i<31) : (line i).intercept ≤ (exactLine i).intercept := by
  interval_cases i <;> norm_num [line,exactLine]

theorem multiplier_nonneg (i : ℕ) (hi : i<31) : 0 ≤ multiplier i := by
  interval_cases i <;> norm_num [multiplier]

theorem square_identity (i : ℕ) (hi : i<31) (hne : i≠0) (r s : ℝ) :
    w i*(r-s)+s*(line (i+1)).eval s-(exactLine i).eval r=
      (line (i+1)).slope*(s-contact i)^2+multiplier i*domainTerm i r s := by
  have hi0 : 1 ≤ i := by omega
  interval_cases i <;> (norm_num [w,t,tTail,line,exactLine,Affine.eval,contact,multiplier,domainTerm] <;> ring)

theorem cap_square_identity (r s : ℝ) :
    w 0*(r-s)+s*(line 1).eval s-(exactLine 0).eval r=
      ((line 1).slope-multiplier 0/4)*(s-contact 0)^2+
        multiplier 0*(r-contactR-(s-contact 0)/2)^2+
        multiplier 0*(r*s-r^2+A) := by
  norm_num [w,t,tTail,line,exactLine,Affine.eval,contact,contactR,multiplier,A,K] <;> ring

theorem domainTerm_nonneg (i : ℕ) (r s : ℝ)
    (hs : 1 ≤ s) (hr : s ≤ r) : 0 ≤ domainTerm i r s := by
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

theorem stage_certificate (i : ℕ) (hi : i<31) :
    StageCertificate (w i) ratioUpper (cap A) (line i) (line (i+1)) := by
  have he : StageCertificate (w i) ratioUpper (cap A) (exactLine i) (line (i+1)) := by
    by_cases hzero : i=0
    · subst i
      apply stage_certificate_of_quadratic_identity
        (show 0 ≤ w 0 from (t_positive 2 (by omega)).le)
        (exactLine_slope_nonneg 0 (by omega)) (line_slope_nonneg 1 (by omega))
        (exactLine_at_one 0 (by omega)) (line_at_one 1 (by omega))
        (multiplier_nonneg 0 (by omega))
        (show multiplier 0 ≤ 4*(line 1).slope by norm_num [multiplier,line])
        cap_square_identity
    · apply stage_certificate_of_square_identity (domainTerm i)
        (show 0 ≤ w i from (t_positive (i+2) (by omega)).le)
        (exactLine_slope_nonneg i hi) (line_slope_nonneg (i+1) (by omega))
        (exactLine_at_one i hi) (line_at_one (i+1) (by omega))
        (multiplier_nonneg i hi) (square_identity i hi hzero)
      intro r hr hrR s hs hl hsr
      exact domainTerm_nonneg i r s hs hsr
  exact RoundedAffineBellman.stage_of_coeff_minorant he
    (line_slope_nonneg i (by omega)) (slope_rounding i hi) (intercept_rounding i hi)

theorem terminal_line : line 31=⟨tTail,-tTail⟩ := by norm_num [line]
theorem strict_budget : C<q*(line 0).positive q := by
  norm_num [C,q,line,Affine.positive,Affine.eval]
theorem exact_endpoint : 1+K*q=(276819/20000:ℝ) := by norm_num [K,q]
end KLSConstantImprovement.QuarticM32TrueCapBellman20261020Data
#print axioms KLSConstantImprovement.QuarticM32TrueCapBellman20261020Data.stage_certificate
#print axioms KLSConstantImprovement.QuarticM32TrueCapBellman20261020Data.strict_budget
#print axioms KLSConstantImprovement.QuarticM32TrueCapBellman20261020Data.exact_endpoint
