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
namespace KLSConstantImprovement.QuarticM48FiniteCostGrid20261020
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def K : ℝ := 1216280801173157/100000000000000

def C : ℝ := 889110106060429/5000000000000000

def c : ℝ := 2639477099272473/100000000000000

def alphaTail : ℝ := 42031259312359/100000000000000

def youngTail : ℝ := 154231370380099/5000000000000

def tTail : ℝ := 126653986822869/100000000000000

def alpha (d : ℕ) : ℝ :=
  if d=2 then 1/3 else
  if d=3 then 24667942873271/50000000000000 else
  if d=4 then 23214319963783/50000000000000 else
  if d=5 then 22254715348677/50000000000000 else
  if d=6 then 5433998817903/12500000000000 else
  if d=7 then 1341988741127/3125000000000 else
  if d=8 then 41865312116059/100000000000000 else
  if d=9 then 40960392868203/100000000000000 else
  if d=10 then 40461427576591/100000000000000 else
  if d=11 then 20100269690067/50000000000000 else
  if d=12 then 8016175105789/20000000000000 else
  if d=13 then 40045212141243/100000000000000 else
  if d=14 then 5007415752217/12500000000000 else
  if d=15 then 401010981697/1000000000000 else
  if d=16 then 40158776199501/100000000000000 else
  if d=17 then 5027868128483/12500000000000 else
  if d=18 then 40289357710329/100000000000000 else
  if d=19 then 10088841165019/25000000000000 else
  if d=20 then 40419392919203/100000000000000 else
  if d=21 then 5060414842787/12500000000000 else
  if d=22 then 40545925444201/100000000000000 else
  if d=23 then 10151637790589/25000000000000 else
  if d=24 then 40667836779963/100000000000000 else
  if d=25 then 159092762463/390625000000 else
  if d=26 then 40785720930391/100000000000000 else
  if d=27 then 8168868538771/20000000000000 else
  if d=28 then 20449669162451/50000000000000 else
  if d=29 then 20474313269151/50000000000000 else
  if d=30 then 8198575843671/20000000000000 else
  if d=31 then 10257674483461/25000000000000 else
  if d=32 then 8207770737171/20000000000000 else
  if d=33 then 41046411545621/100000000000000 else
  if d=34 then 1282990984379/3125000000000 else
  if d=35 then 1642657290011/4000000000000 else
  if d=36 then 41080060465113/100000000000000 else
  if d=37 then 5137503464997/12500000000000 else
  if d=38 then 20561286444437/50000000000000 else
  if d=39 then 20576603708583/50000000000000 else
  if d=40 then 41187755030327/100000000000000 else
  if d=41 then 41245100287127/100000000000000 else
  if d=42 then 4121630813223/10000000000000 else
  if d=43 then 10189992634887/25000000000000 else
  if d=44 then 8284547982911/20000000000000 else
  if d=45 then 20428334549269/50000000000000 else
  if d=46 then 2065441401687/5000000000000 else
  if d=47 then 20419467509503/50000000000000 else
  if d=48 then 21227721668561/50000000000000 else
  if d=49 then 1326844092413/3125000000000 else
  if d=50 then 21232118543749/50000000000000 else
  if d=51 then 42471637611977/100000000000000 else
  if d=52 then 42480031184057/100000000000000 else
  if d=53 then 4248847239827/10000000000000 else
  if d=54 then 42496198454557/100000000000000 else
  if d=55 then 8500564701261/20000000000000 else
  if d=56 then 42508116498749/100000000000000 else
  if d=57 then 42511886308179/100000000000000 else
  if d=58 then 21256994027119/50000000000000 else
  if d=59 then 10628580775391/25000000000000 else
  if d=60 then 42512836035861/100000000000000 else
  if d=61 then 1700380386421/4000000000000 else
  if d=62 then 170017442251/400000000000 else
  if d=63 then 21248716995699/50000000000000 else
  if d=64 then 21244399709431/50000000000000 else
  if d=65 then 42478545772071/100000000000000 else
  if d=66 then 21233388905233/50000000000000 else
  if d=67 then 8490722663791/20000000000000 else
  if d=68 then 42439179630867/100000000000000 else
  if d=69 then 21211805512901/50000000000000 else
  if d=70 then 8481409275017/20000000000000 else
  if d=71 then 10597406731089/25000000000000 else
  if d=72 then 8474299049239/20000000000000 else
  if d=73 then 10588198214017/25000000000000 else
  if d=74 then 4233365547739/10000000000000 else
  if d=75 then 8462845655791/20000000000000 else
  if d=76 then 8458927947811/20000000000000 else
  if d=77 then 42275023561579/100000000000000 else
  if d=78 then 42255498177053/100000000000000 else
  if d=79 then 8249255947/19531250000 else
  if d=80 then 10554301069489/25000000000000 else
  if d=81 then 42198640219029/100000000000000 else
  if d=82 then 21090297426033/50000000000000 else
  if d=83 then 21081581122743/50000000000000 else
  if d=84 then 21073215261529/50000000000000 else
  if d=85 then 42130485469889/100000000000000 else
  if d=86 then 10528853192231/25000000000000 else
  if d=87 then 42101286275913/100000000000000 else
  if d=88 then 42088186476357/100000000000000 else
  if d=89 then 10519049963573/25000000000000 else
  if d=90 then 10516385734843/25000000000000 else
  if d=91 then 42056104799731/100000000000000 else
  if d=92 then 21024064302689/50000000000000 else
  if d=93 then 2102078361871/5000000000000 else
  if d=94 then 2627289298093/6250000000000 else
  if d=95 then 42033120836567/100000000000000 else
  alphaTail


def young (d : ℕ) : ℝ :=
  if d=2 then 47737248705847/50000000000000 else
  if d=3 then 96249719816831/12500000000000 else
  if d=4 then 1216171846541689/100000000000000 else
  if d=5 then 16338381295407/1250000000000 else
  if d=6 then 279841807881177/20000000000000 else
  if d=7 then 1504891460389121/100000000000000 else
  if d=8 then 830771196175613/50000000000000 else
  if d=9 then 112357273956177/6250000000000 else
  if d=10 then 1890203315662349/100000000000000 else
  if d=11 then 194959265566391/10000000000000 else
  if d=12 then 496446654664141/25000000000000 else
  if d=13 then 2007227544228853/100000000000000 else
  if d=14 then 1009860886017099/50000000000000 else
  if d=15 then 2026859260159927/100000000000000 else
  if d=16 then 2031118298854151/100000000000000 else
  if d=17 then 127089468869131/6250000000000 else
  if d=18 then 2036610956108543/100000000000000 else
  if d=19 then 31885224159629/1562500000000 else
  if d=20 then 408750666979887/20000000000000 else
  if d=21 then 511470239643023/25000000000000 else
  if d=22 then 2046835459413187/100000000000000 else
  if d=23 then 2046266836386981/100000000000000 else
  if d=24 then 1021872406592839/50000000000000 else
  if d=25 then 2038040383073763/100000000000000 else
  if d=26 then 507140548610257/25000000000000 else
  if d=27 then 251838708359177/12500000000000 else
  if d=28 then 996336838490147/50000000000000 else
  if d=29 then 1963824308746343/100000000000000 else
  if d=30 then 965824517646929/50000000000000 else
  if d=31 then 474106204961681/25000000000000 else
  if d=32 then 907457973106727/50000000000000 else
  if d=33 then 449168942240509/25000000000000 else
  if d=34 then 178003138020571/10000000000000 else
  if d=35 then 440839726333011/25000000000000 else
  if d=36 then 174423461531569/10000000000000 else
  if d=37 then 345378360046151/20000000000000 else
  if d=38 then 1709012577972521/100000000000000 else
  if d=39 then 16932254694907/1000000000000 else
  if d=40 then 838290722874359/50000000000000 else
  if d=41 then 332287981907409/20000000000000 else
  if d=42 then 1646463774965093/100000000000000 else
  if d=43 then 816290421765723/50000000000000 else
  if d=44 then 16210494892167/1000000000000 else
  if d=45 then 1608541182563541/100000000000000 else
  if d=46 then 199528007702663/12500000000000 else
  if d=47 then 791312554790569/50000000000000 else
  youngTail


def t (d : ℕ) : ℝ :=
  if d=2 then 1 else
  if d=3 then 314771609294857/50000000000000 else
  if d=4 then 81484614789271/12500000000000 else
  if d=5 then 136431053220889/25000000000000 else
  if d=6 then 236577995555449/50000000000000 else
  if d=7 then 41982563030853/10000000000000 else
  if d=8 then 96680376706541/25000000000000 else
  if d=9 then 45138000943411/12500000000000 else
  if d=10 then 5284765624029/1562500000000 else
  if d=11 then 19877542622767/6250000000000 else
  if d=12 then 1876947156631/625000000000 else
  if d=13 then 142368284802563/50000000000000 else
  if d=14 then 271019589882751/100000000000000 else
  if d=15 then 258898515108441/100000000000000 else
  if d=16 then 248137141709843/100000000000000 else
  if d=17 then 14908762259003/6250000000000 else
  if d=18 then 229936330547581/100000000000000 else
  if d=19 then 13886739417639/6250000000000 else
  if d=20 then 53794714703629/25000000000000 else
  if d=21 then 208801112228601/100000000000000 else
  if d=22 then 25371824532013/12500000000000 else
  if d=23 then 197630177172593/100000000000000 else
  if d=24 then 19269499038047/10000000000000 else
  if d=25 then 47031422353803/25000000000000 else
  if d=26 then 183878099564141/100000000000000 else
  if d=27 then 35980066688253/20000000000000 else
  if d=28 then 176168411794857/100000000000000 else
  if d=29 then 10790868361169/6250000000000 else
  if d=30 then 21165804903837/12500000000000 else
  if d=31 then 83083644321913/50000000000000 else
  if d=32 then 81579036770849/50000000000000 else
  if d=33 then 40072358730117/25000000000000 else
  if d=34 then 157546965056723/100000000000000 else
  if d=35 then 154921710790449/100000000000000 else
  if d=36 then 19049373455707/12500000000000 else
  if d=37 then 149951297285469/100000000000000 else
  if d=38 then 36899205004317/25000000000000 else
  if d=39 then 145310986001539/100000000000000 else
  if d=40 then 35775450792419/25000000000000 else
  if d=41 then 140905592810501/100000000000000 else
  if d=42 then 139065244631929/100000000000000 else
  if d=43 then 138626849864259/100000000000000 else
  if d=44 then 134656905636521/100000000000000 else
  if d=45 then 67344739635293/50000000000000 else
  if d=46 then 65777559130353/50000000000000 else
  if d=47 then 131346497814977/100000000000000 else
  tTail


def theta (d : ℕ) : ℝ := if 3 ≤ d ∧ d ≤ 48 then 1 else 0

def lambda (d : ℕ) : ℝ := if 2 ≤ d ∧ d ≤ 47 then 1 else 0


def zeta (d : ℕ) : ℝ :=
  if d=3 then 142857/100000 else
  if d=4 then 48284294672479/25000000000000 else
  if d=5 then 265907121594359/260000000000000 else
  if d=6 then 142989446540591/200000000000000 else
  if d=7 then 280541435211849/475000000000000 else
  if d=8 then 28279508366811/55000000000000 else
  if d=9 then 111307472436699/250000000000000 else
  if d=10 then 53609776272503/140000000000000 else
  if d=11 then 122381490707047/387500000000000 else
  if d=12 then 218061814019413/850000000000000 else
  if d=13 then 73289679283821/370000000000000 else
  if d=14 then 7386420920753/50000000000000 else
  if d=15 then 2701049439907/26875000000000 else
  if d=16 then 1469473731471/28750000000000 else
  if d=17 then 96180831613947/4900000000000000 else
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
  if d=32 then 0 else
  if d=33 then 0 else
  if d=34 then 0 else
  if d=35 then 0 else
  if d=36 then 0 else
  if d=37 then 0 else
  if d=38 then 29207009/140000000000000 else
  if d=39 then 311884417/143750000000000 else
  if d=40 then 58148209/11800000000000 else
  if d=41 then 26400743411/12100000000000000 else
  if d=42 then 36065170141/3100000000000000 else
  if d=43 then 0 else
  if d=44 then 0 else
  if d=45 then 0 else
  if d=46 then 0 else
  if d=47 then 0 else
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

/- Concrete table evaluation lemmas keep repeated row proofs from unfolding long tables. -/
@[simp] theorem alpha_eval_2 : alpha 2=(1/3 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_3 : alpha 3=(24667942873271/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_4 : alpha 4=(23214319963783/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_5 : alpha 5=(22254715348677/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_6 : alpha 6=(5433998817903/12500000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_7 : alpha 7=(1341988741127/3125000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_8 : alpha 8=(41865312116059/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_9 : alpha 9=(40960392868203/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_10 : alpha 10=(40461427576591/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_11 : alpha 11=(20100269690067/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_12 : alpha 12=(8016175105789/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_13 : alpha 13=(40045212141243/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_14 : alpha 14=(5007415752217/12500000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_15 : alpha 15=(401010981697/1000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_16 : alpha 16=(40158776199501/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_17 : alpha 17=(5027868128483/12500000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_18 : alpha 18=(40289357710329/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_19 : alpha 19=(10088841165019/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_20 : alpha 20=(40419392919203/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_21 : alpha 21=(5060414842787/12500000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_22 : alpha 22=(40545925444201/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_23 : alpha 23=(10151637790589/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_24 : alpha 24=(40667836779963/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_25 : alpha 25=(159092762463/390625000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_26 : alpha 26=(40785720930391/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_27 : alpha 27=(8168868538771/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_28 : alpha 28=(20449669162451/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_29 : alpha 29=(20474313269151/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_30 : alpha 30=(8198575843671/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_31 : alpha 31=(10257674483461/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_32 : alpha 32=(8207770737171/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_33 : alpha 33=(41046411545621/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_34 : alpha 34=(1282990984379/3125000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_35 : alpha 35=(1642657290011/4000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_36 : alpha 36=(41080060465113/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_37 : alpha 37=(5137503464997/12500000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_38 : alpha 38=(20561286444437/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_39 : alpha 39=(20576603708583/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_40 : alpha 40=(41187755030327/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_41 : alpha 41=(41245100287127/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_42 : alpha 42=(4121630813223/10000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_43 : alpha 43=(10189992634887/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_44 : alpha 44=(8284547982911/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_45 : alpha 45=(20428334549269/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_46 : alpha 46=(2065441401687/5000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_47 : alpha 47=(20419467509503/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_48 : alpha 48=(21227721668561/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_49 : alpha 49=(1326844092413/3125000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_50 : alpha 50=(21232118543749/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_51 : alpha 51=(42471637611977/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_52 : alpha 52=(42480031184057/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_53 : alpha 53=(4248847239827/10000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_54 : alpha 54=(42496198454557/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_55 : alpha 55=(8500564701261/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_56 : alpha 56=(42508116498749/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_57 : alpha 57=(42511886308179/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_58 : alpha 58=(21256994027119/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_59 : alpha 59=(10628580775391/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_60 : alpha 60=(42512836035861/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_61 : alpha 61=(1700380386421/4000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_62 : alpha 62=(170017442251/400000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_63 : alpha 63=(21248716995699/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_64 : alpha 64=(21244399709431/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_65 : alpha 65=(42478545772071/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_66 : alpha 66=(21233388905233/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_67 : alpha 67=(8490722663791/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_68 : alpha 68=(42439179630867/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_69 : alpha 69=(21211805512901/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_70 : alpha 70=(8481409275017/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_71 : alpha 71=(10597406731089/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_72 : alpha 72=(8474299049239/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_73 : alpha 73=(10588198214017/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_74 : alpha 74=(4233365547739/10000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_75 : alpha 75=(8462845655791/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_76 : alpha 76=(8458927947811/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_77 : alpha 77=(42275023561579/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_78 : alpha 78=(42255498177053/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_79 : alpha 79=(8249255947/19531250000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_80 : alpha 80=(10554301069489/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_81 : alpha 81=(42198640219029/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_82 : alpha 82=(21090297426033/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_83 : alpha 83=(21081581122743/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_84 : alpha 84=(21073215261529/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_85 : alpha 85=(42130485469889/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_86 : alpha 86=(10528853192231/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_87 : alpha 87=(42101286275913/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_88 : alpha 88=(42088186476357/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_89 : alpha 89=(10519049963573/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_90 : alpha 90=(10516385734843/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_91 : alpha 91=(42056104799731/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_92 : alpha 92=(21024064302689/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_93 : alpha 93=(2102078361871/5000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_94 : alpha 94=(2627289298093/6250000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_95 : alpha 95=(42033120836567/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_96 : alpha 96=(42031259312359/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_97 : alpha 97=(42031259312359/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_98 : alpha 98=(42031259312359/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem young_eval_2 : young 2=(47737248705847/50000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_3 : young 3=(96249719816831/12500000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_4 : young 4=(1216171846541689/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_5 : young 5=(16338381295407/1250000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_6 : young 6=(279841807881177/20000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_7 : young 7=(1504891460389121/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_8 : young 8=(830771196175613/50000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_9 : young 9=(112357273956177/6250000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_10 : young 10=(1890203315662349/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_11 : young 11=(194959265566391/10000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_12 : young 12=(496446654664141/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_13 : young 13=(2007227544228853/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_14 : young 14=(1009860886017099/50000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_15 : young 15=(2026859260159927/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_16 : young 16=(2031118298854151/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_17 : young 17=(127089468869131/6250000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_18 : young 18=(2036610956108543/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_19 : young 19=(31885224159629/1562500000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_20 : young 20=(408750666979887/20000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_21 : young 21=(511470239643023/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_22 : young 22=(2046835459413187/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_23 : young 23=(2046266836386981/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_24 : young 24=(1021872406592839/50000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_25 : young 25=(2038040383073763/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_26 : young 26=(507140548610257/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_27 : young 27=(251838708359177/12500000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_28 : young 28=(996336838490147/50000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_29 : young 29=(1963824308746343/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_30 : young 30=(965824517646929/50000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_31 : young 31=(474106204961681/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_32 : young 32=(907457973106727/50000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_33 : young 33=(449168942240509/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_34 : young 34=(178003138020571/10000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_35 : young 35=(440839726333011/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_36 : young 36=(174423461531569/10000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_37 : young 37=(345378360046151/20000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_38 : young 38=(1709012577972521/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_39 : young 39=(16932254694907/1000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_40 : young 40=(838290722874359/50000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_41 : young 41=(332287981907409/20000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_42 : young 42=(1646463774965093/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_43 : young 43=(816290421765723/50000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_44 : young 44=(16210494892167/1000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_45 : young 45=(1608541182563541/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_46 : young 46=(199528007702663/12500000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_47 : young 47=(791312554790569/50000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_48 : young 48=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_49 : young 49=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_50 : young 50=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_51 : young 51=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_52 : young 52=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_53 : young 53=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_54 : young 54=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_55 : young 55=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_56 : young 56=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_57 : young 57=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_58 : young 58=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_59 : young 59=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_60 : young 60=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_61 : young 61=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_62 : young 62=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_63 : young 63=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_64 : young 64=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_65 : young 65=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_66 : young 66=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_67 : young 67=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_68 : young 68=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_69 : young 69=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_70 : young 70=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_71 : young 71=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_72 : young 72=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_73 : young 73=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_74 : young 74=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_75 : young 75=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_76 : young 76=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_77 : young 77=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_78 : young 78=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_79 : young 79=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_80 : young 80=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_81 : young 81=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_82 : young 82=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_83 : young 83=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_84 : young 84=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_85 : young 85=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_86 : young 86=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_87 : young 87=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_88 : young 88=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_89 : young 89=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_90 : young 90=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_91 : young 91=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_92 : young 92=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_93 : young 93=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_94 : young 94=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_95 : young 95=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_96 : young 96=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_97 : young 97=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_98 : young 98=(154231370380099/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem t_eval_2 : t 2=(1 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_3 : t 3=(314771609294857/50000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_4 : t 4=(81484614789271/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_5 : t 5=(136431053220889/25000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_6 : t 6=(236577995555449/50000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_7 : t 7=(41982563030853/10000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_8 : t 8=(96680376706541/25000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_9 : t 9=(45138000943411/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_10 : t 10=(5284765624029/1562500000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_11 : t 11=(19877542622767/6250000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_12 : t 12=(1876947156631/625000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_13 : t 13=(142368284802563/50000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_14 : t 14=(271019589882751/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_15 : t 15=(258898515108441/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_16 : t 16=(248137141709843/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_17 : t 17=(14908762259003/6250000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_18 : t 18=(229936330547581/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_19 : t 19=(13886739417639/6250000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_20 : t 20=(53794714703629/25000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_21 : t 21=(208801112228601/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_22 : t 22=(25371824532013/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_23 : t 23=(197630177172593/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_24 : t 24=(19269499038047/10000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_25 : t 25=(47031422353803/25000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_26 : t 26=(183878099564141/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_27 : t 27=(35980066688253/20000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_28 : t 28=(176168411794857/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_29 : t 29=(10790868361169/6250000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_30 : t 30=(21165804903837/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_31 : t 31=(83083644321913/50000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_32 : t 32=(81579036770849/50000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_33 : t 33=(40072358730117/25000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_34 : t 34=(157546965056723/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_35 : t 35=(154921710790449/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_36 : t 36=(19049373455707/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_37 : t 37=(149951297285469/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_38 : t 38=(36899205004317/25000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_39 : t 39=(145310986001539/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_40 : t 40=(35775450792419/25000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_41 : t 41=(140905592810501/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_42 : t 42=(139065244631929/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_43 : t 43=(138626849864259/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_44 : t 44=(134656905636521/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_45 : t 45=(67344739635293/50000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_46 : t 46=(65777559130353/50000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_47 : t 47=(131346497814977/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_48 : t 48=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_49 : t 49=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_50 : t 50=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_51 : t 51=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_52 : t 52=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_53 : t 53=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_54 : t 54=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_55 : t 55=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_56 : t 56=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_57 : t 57=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_58 : t 58=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_59 : t 59=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_60 : t 60=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_61 : t 61=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_62 : t 62=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_63 : t 63=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_64 : t 64=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_65 : t 65=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_66 : t 66=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_67 : t 67=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_68 : t 68=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_69 : t 69=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_70 : t 70=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_71 : t 71=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_72 : t 72=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_73 : t 73=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_74 : t 74=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_75 : t 75=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_76 : t 76=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_77 : t 77=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_78 : t 78=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_79 : t 79=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_80 : t 80=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_81 : t 81=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_82 : t 82=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_83 : t 83=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_84 : t 84=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_85 : t 85=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_86 : t 86=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_87 : t 87=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_88 : t 88=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_89 : t 89=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_90 : t 90=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_91 : t 91=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_92 : t 92=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_93 : t 93=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_94 : t 94=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_95 : t 95=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_96 : t 96=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_97 : t 97=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_98 : t 98=(126653986822869/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem zeta_eval_2 : zeta 2=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_3 : zeta 3=(142857/100000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_4 : zeta 4=(48284294672479/25000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_5 : zeta 5=(265907121594359/260000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_6 : zeta 6=(142989446540591/200000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_7 : zeta 7=(280541435211849/475000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_8 : zeta 8=(28279508366811/55000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_9 : zeta 9=(111307472436699/250000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_10 : zeta 10=(53609776272503/140000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_11 : zeta 11=(122381490707047/387500000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_12 : zeta 12=(218061814019413/850000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_13 : zeta 13=(73289679283821/370000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_14 : zeta 14=(7386420920753/50000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_15 : zeta 15=(2701049439907/26875000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_16 : zeta 16=(1469473731471/28750000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_17 : zeta 17=(96180831613947/4900000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_18 : zeta 18=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_19 : zeta 19=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_20 : zeta 20=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_21 : zeta 21=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_22 : zeta 22=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_23 : zeta 23=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_24 : zeta 24=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_25 : zeta 25=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_26 : zeta 26=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_27 : zeta 27=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_28 : zeta 28=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_29 : zeta 29=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_30 : zeta 30=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_31 : zeta 31=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_32 : zeta 32=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_33 : zeta 33=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_34 : zeta 34=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_35 : zeta 35=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_36 : zeta 36=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_37 : zeta 37=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_38 : zeta 38=(29207009/140000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_39 : zeta 39=(311884417/143750000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_40 : zeta 40=(58148209/11800000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_41 : zeta 41=(26400743411/12100000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_42 : zeta 42=(36065170141/3100000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_43 : zeta 43=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_44 : zeta 44=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_45 : zeta 45=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_46 : zeta 46=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_47 : zeta 47=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_48 : zeta 48=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_49 : zeta 49=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_50 : zeta 50=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_51 : zeta 51=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_52 : zeta 52=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_53 : zeta 53=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_54 : zeta 54=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_55 : zeta 55=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_56 : zeta 56=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_57 : zeta 57=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_58 : zeta 58=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_59 : zeta 59=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_60 : zeta 60=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_61 : zeta 61=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_62 : zeta 62=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_63 : zeta 63=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_64 : zeta 64=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_65 : zeta 65=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_66 : zeta 66=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_67 : zeta 67=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_68 : zeta 68=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_69 : zeta 69=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_70 : zeta 70=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_71 : zeta 71=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_72 : zeta 72=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_73 : zeta 73=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_74 : zeta 74=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_75 : zeta 75=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_76 : zeta 76=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_77 : zeta 77=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_78 : zeta 78=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_79 : zeta 79=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_80 : zeta 80=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_81 : zeta 81=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_82 : zeta 82=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_83 : zeta 83=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_84 : zeta 84=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_85 : zeta 85=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_86 : zeta 86=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_87 : zeta 87=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_88 : zeta 88=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_89 : zeta 89=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_90 : zeta 90=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_91 : zeta 91=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_92 : zeta 92=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_93 : zeta 93=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_94 : zeta 94=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_95 : zeta 95=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_96 : zeta 96=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_97 : zeta 97=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_98 : zeta 98=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem theta_eval_2 : theta 2=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_3 : theta 3=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_4 : theta 4=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_5 : theta 5=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_6 : theta 6=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_7 : theta 7=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_8 : theta 8=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_9 : theta 9=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_10 : theta 10=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_11 : theta 11=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_12 : theta 12=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_13 : theta 13=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_14 : theta 14=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_15 : theta 15=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_16 : theta 16=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_17 : theta 17=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_18 : theta 18=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_19 : theta 19=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_20 : theta 20=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_21 : theta 21=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_22 : theta 22=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_23 : theta 23=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_24 : theta 24=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_25 : theta 25=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_26 : theta 26=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_27 : theta 27=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_28 : theta 28=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_29 : theta 29=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_30 : theta 30=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_31 : theta 31=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_32 : theta 32=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_33 : theta 33=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_34 : theta 34=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_35 : theta 35=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_36 : theta 36=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_37 : theta 37=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_38 : theta 38=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_39 : theta 39=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_40 : theta 40=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_41 : theta 41=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_42 : theta 42=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_43 : theta 43=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_44 : theta 44=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_45 : theta 45=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_46 : theta 46=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_47 : theta 47=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_48 : theta 48=(1 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_49 : theta 49=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_50 : theta 50=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_51 : theta 51=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_52 : theta 52=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_53 : theta 53=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_54 : theta 54=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_55 : theta 55=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_56 : theta 56=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_57 : theta 57=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_58 : theta 58=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_59 : theta 59=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_60 : theta 60=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_61 : theta 61=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_62 : theta 62=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_63 : theta 63=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_64 : theta 64=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_65 : theta 65=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_66 : theta 66=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_67 : theta 67=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_68 : theta 68=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_69 : theta 69=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_70 : theta 70=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_71 : theta 71=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_72 : theta 72=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_73 : theta 73=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_74 : theta 74=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_75 : theta 75=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_76 : theta 76=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_77 : theta 77=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_78 : theta 78=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_79 : theta 79=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_80 : theta 80=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_81 : theta 81=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_82 : theta 82=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_83 : theta 83=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_84 : theta 84=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_85 : theta 85=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_86 : theta 86=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_87 : theta 87=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_88 : theta 88=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_89 : theta 89=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_90 : theta 90=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_91 : theta 91=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_92 : theta 92=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_93 : theta 93=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_94 : theta 94=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_95 : theta 95=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_96 : theta 96=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_97 : theta 97=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_98 : theta 98=(0 : ℝ) := by norm_num [theta]
@[simp] theorem lambda_eval_2 : lambda 2=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_3 : lambda 3=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_4 : lambda 4=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_5 : lambda 5=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_6 : lambda 6=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_7 : lambda 7=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_8 : lambda 8=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_9 : lambda 9=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_10 : lambda 10=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_11 : lambda 11=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_12 : lambda 12=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_13 : lambda 13=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_14 : lambda 14=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_15 : lambda 15=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_16 : lambda 16=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_17 : lambda 17=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_18 : lambda 18=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_19 : lambda 19=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_20 : lambda 20=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_21 : lambda 21=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_22 : lambda 22=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_23 : lambda 23=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_24 : lambda 24=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_25 : lambda 25=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_26 : lambda 26=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_27 : lambda 27=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_28 : lambda 28=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_29 : lambda 29=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_30 : lambda 30=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_31 : lambda 31=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_32 : lambda 32=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_33 : lambda 33=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_34 : lambda 34=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_35 : lambda 35=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_36 : lambda 36=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_37 : lambda 37=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_38 : lambda 38=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_39 : lambda 39=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_40 : lambda 40=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_41 : lambda 41=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_42 : lambda 42=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_43 : lambda 43=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_44 : lambda 44=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_45 : lambda 45=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_46 : lambda 46=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_47 : lambda 47=(1 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_48 : lambda 48=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_49 : lambda 49=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_50 : lambda 50=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_51 : lambda 51=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_52 : lambda 52=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_53 : lambda 53=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_54 : lambda 54=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_55 : lambda 55=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_56 : lambda 56=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_57 : lambda 57=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_58 : lambda 58=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_59 : lambda 59=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_60 : lambda 60=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_61 : lambda 61=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_62 : lambda 62=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_63 : lambda 63=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_64 : lambda 64=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_65 : lambda 65=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_66 : lambda 66=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_67 : lambda 67=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_68 : lambda 68=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_69 : lambda 69=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_70 : lambda 70=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_71 : lambda 71=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_72 : lambda 72=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_73 : lambda 73=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_74 : lambda 74=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_75 : lambda 75=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_76 : lambda 76=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_77 : lambda 77=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_78 : lambda 78=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_79 : lambda 79=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_80 : lambda 80=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_81 : lambda 81=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_82 : lambda 82=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_83 : lambda 83=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_84 : lambda 84=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_85 : lambda 85=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_86 : lambda 86=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_87 : lambda 87=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_88 : lambda 88=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_89 : lambda 89=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_90 : lambda 90=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_91 : lambda 91=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_92 : lambda 92=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_93 : lambda 93=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_94 : lambda 94=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_95 : lambda 95=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_96 : lambda 96=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_97 : lambda 97=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_98 : lambda 98=(0 : ℝ) := by norm_num [lambda]

def rawRow (d aa : ℕ) : ℝ :=
  young (d-aa+1)*(t d/(t aa*t (d-aa+1)))*
    (twoRowsProfile theta (tripleHarmonicThetaProfile zeta) d aa)^2/
      (1-twoRowsLambda lambda (tripleHarmonicLambdaProfile zeta) aa (d-aa+1))

theorem grid_sum_interval_two (f : ℕ → ℝ) (N : ℕ) :
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

def rowGrid_5 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 5196 else
  if aa=4 then 7992727383 else
  0

theorem raw_first_cost_upper_5 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 5 ≤ (15414536053/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 4) :
      rawRow 5 aa ≤ rowGrid_5 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 4 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_5,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 5 ≤ (7421803474/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 4,rowGrid_5 aa/10000000000)+(7421803474/10000000000 : ℝ)=(15414536053/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_5]
  change (∑ aa ∈ Finset.Icc 2 4,rawRow 5 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 5 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_5 : c ≤ coefficient profile 5 := by
  have hf := raw_first_cost_upper_5
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 5-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 5-1-
      (K*C/young 5)*(5 : ℝ)^2-(15414536053/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 5 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 5-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 5-1-
      ((K*C/young 5)*(5 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 5+
        t 3*tripleHarmonicNeighborCharge K young zeta 5)
  linarith only [hf,hn]

def rowGrid_6 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 124523865 else
  if aa=4 then 8877744677 else
  if aa=5 then 8277868085 else
  0

theorem raw_first_cost_upper_6 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 6 ≤ (24288970662/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 5) :
      rawRow 6 aa ≤ rowGrid_6 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 5 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_6,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 6 ≤ (7008834035/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 5,rowGrid_6 aa/10000000000)+(7008834035/10000000000 : ℝ)=(24288970662/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_6]
  change (∑ aa ∈ Finset.Icc 2 5,rawRow 6 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 6 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_6 : c ≤ coefficient profile 6 := by
  have hf := raw_first_cost_upper_6
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 6-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 6-1-
      (K*C/young 6)*(6 : ℝ)^2-(24288970662/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 6 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 6-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 6-1-
      ((K*C/young 6)*(6 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 6+
        t 3*tripleHarmonicNeighborCharge K young zeta 6)
  linarith only [hf,hn]

def rowGrid_7 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 3669921098 else
  if aa=4 then 12015246546 else
  if aa=5 then 9409350284 else
  if aa=6 then 8471337531 else
  0

theorem raw_first_cost_upper_7 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 7 ≤ (39618270850/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 6) :
      rawRow 7 aa ≤ rowGrid_7 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 6 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_7,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 7 ≤ (6052415391/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 6,rowGrid_7 aa/10000000000)+(6052415391/10000000000 : ℝ)=(39618270850/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_7]
  change (∑ aa ∈ Finset.Icc 2 6,rawRow 7 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 7 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_7 : c ≤ coefficient profile 7 := by
  have hf := raw_first_cost_upper_7
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 7-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 7-1-
      (K*C/young 7)*(7 : ℝ)^2-(39618270850/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 7 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 7-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 7-1-
      ((K*C/young 7)*(7 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 7+
        t 3*tripleHarmonicNeighborCharge K young zeta 7)
  linarith only [hf,hn]

def rowGrid_8 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 6333932287 else
  if aa=4 then 14208836356 else
  if aa=5 then 13220699801 else
  if aa=6 then 9996728392 else
  if aa=7 then 8794613487 else
  0

theorem raw_first_cost_upper_8 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 8 ≤ (58245724315/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 7) :
      rawRow 8 aa ≤ rowGrid_8 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 7 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_8,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 8 ≤ (5690913992/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 7,rowGrid_8 aa/10000000000)+(5690913992/10000000000 : ℝ)=(58245724315/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_8]
  change (∑ aa ∈ Finset.Icc 2 7,rawRow 8 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 8 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_8 : c ≤ coefficient profile 8 := by
  have hf := raw_first_cost_upper_8
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 8-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 8-1-
      (K*C/young 8)*(8 : ℝ)^2-(58245724315/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 8 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 8-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 8-1-
      ((K*C/young 8)*(8 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 8+
        t 3*tripleHarmonicNeighborCharge K young zeta 8)
  linarith only [hf,hn]

def rowGrid_9 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 8391380459 else
  if aa=4 then 16381171728 else
  if aa=5 then 15848380012 else
  if aa=6 then 14238272701 else
  if aa=7 then 10520279313 else
  if aa=8 then 8915000337 else
  0

theorem raw_first_cost_upper_9 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 9 ≤ (80014720486/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 8) :
      rawRow 9 aa ≤ rowGrid_9 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 8 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_9,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 9 ≤ (5720235936/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 8,rowGrid_9 aa/10000000000)+(5720235936/10000000000 : ℝ)=(80014720486/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_9]
  change (∑ aa ∈ Finset.Icc 2 8,rawRow 9 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 9 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_9 : c ≤ coefficient profile 9 := by
  have hf := raw_first_cost_upper_9
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 9-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 9-1-
      (K*C/young 9)*(9 : ℝ)^2-(80014720486/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 9 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 9-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 9-1-
      ((K*C/young 9)*(9 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 9+
        t 3*tripleHarmonicNeighborCharge K young zeta 9)
  linarith only [hf,hn]

def rowGrid_10 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 10369888147 else
  if aa=4 then 18598431978 else
  if aa=5 then 18327817045 else
  if aa=6 then 17120922165 else
  if aa=7 then 15030246338 else
  if aa=8 then 10697228950 else
  if aa=9 then 8942537665 else
  0

theorem raw_first_cost_upper_10 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 10 ≤ (104973910505/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 9) :
      rawRow 10 aa ≤ rowGrid_10 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 9 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_10,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 10 ≤ (5886838217/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 9,rowGrid_10 aa/10000000000)+(5886838217/10000000000 : ℝ)=(104973910505/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_10]
  change (∑ aa ∈ Finset.Icc 2 9,rawRow 10 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 10 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_10 : c ≤ coefficient profile 10 := by
  have hf := raw_first_cost_upper_10
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 10-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 10-1-
      (K*C/young 10)*(10 : ℝ)^2-(104973910505/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 10 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 10-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 10-1-
      ((K*C/young 10)*(10 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 10+
        t 3*tripleHarmonicNeighborCharge K young zeta 10)
  linarith only [hf,hn]

def rowGrid_11 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 12355488826 else
  if aa=4 then 20961877240 else
  if aa=5 then 20890348350 else
  if aa=6 then 19877263330 else
  if aa=7 then 18144270772 else
  if aa=8 then 15343120385 else
  if aa=9 then 10772444831 else
  if aa=10 then 8977684758 else
  0

theorem raw_first_cost_upper_11 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 11 ≤ (133221470618/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 10) :
      rawRow 11 aa ≤ rowGrid_11 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 10 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_11,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 11 ≤ (5898972126/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 10,rowGrid_11 aa/10000000000)+(5898972126/10000000000 : ℝ)=(133221470618/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_11]
  change (∑ aa ∈ Finset.Icc 2 10,rawRow 11 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 11 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_11 : c ≤ coefficient profile 11 := by
  have hf := raw_first_cost_upper_11
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 11-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 11-1-
      (K*C/young 11)*(11 : ℝ)^2-(133221470618/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 11 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 11-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 11-1-
      ((K*C/young 11)*(11 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 11+
        t 3*tripleHarmonicNeighborCharge K young zeta 11)
  linarith only [hf,hn]

def rowGrid_12 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 14246703635 else
  if aa=4 then 22934817711 else
  if aa=5 then 23643507606 else
  if aa=6 then 22751179345 else
  if aa=7 then 21153456335 else
  if aa=8 then 18599423967 else
  if aa=9 then 15515617405 else
  if aa=10 then 10860010218 else
  if aa=11 then 9015228384 else
  0

theorem raw_first_cost_upper_12 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 12 ≤ (164454890975/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 11) :
      rawRow 12 aa ≤ rowGrid_12 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 11 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_12,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 12 ≤ (5734946369/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 11,rowGrid_12 aa/10000000000)+(5734946369/10000000000 : ℝ)=(164454890975/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_12]
  change (∑ aa ∈ Finset.Icc 2 11,rawRow 12 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 12 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_12 : c ≤ coefficient profile 12 := by
  have hf := raw_first_cost_upper_12
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 12-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 12-1-
      (K*C/young 12)*(12 : ℝ)^2-(164454890975/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 12 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 12-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 12-1-
      ((K*C/young 12)*(12 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 12+
        t 3*tripleHarmonicNeighborCharge K young zeta 12)
  linarith only [hf,hn]

def rowGrid_13 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 16302447587 else
  if aa=4 then 24410712737 else
  if aa=5 then 25975199599 else
  if aa=6 then 25855444357 else
  if aa=7 then 24311431349 else
  if aa=8 then 21773246129 else
  if aa=9 then 18885858491 else
  if aa=10 then 15706046719 else
  if aa=11 then 10950261319 else
  if aa=12 then 9052292969 else
  0

theorem raw_first_cost_upper_13 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 13 ≤ (198554132922/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 12) :
      rawRow 13 aa ≤ rowGrid_13 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 12 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_13,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 13 ≤ (5331191666/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 12,rowGrid_13 aa/10000000000)+(5331191666/10000000000 : ℝ)=(198554132922/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_13]
  change (∑ aa ∈ Finset.Icc 2 12,rawRow 13 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 13 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_13 : c ≤ coefficient profile 13 := by
  have hf := raw_first_cost_upper_13
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 13-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 13-1-
      (K*C/young 13)*(13 : ℝ)^2-(198554132922/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 13 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 13-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 13-1-
      ((K*C/young 13)*(13 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 13+
        t 3*tripleHarmonicNeighborCharge K young zeta 13)
  linarith only [hf,hn]

def rowGrid_14 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 18288221461 else
  if aa=4 then 25485683422 else
  if aa=5 then 27754299844 else
  if aa=6 then 28515776905 else
  if aa=7 then 27736064341 else
  if aa=8 then 25121096256 else
  if aa=9 then 22194564828 else
  if aa=10 then 19192023617 else
  if aa=11 then 15898177795 else
  if aa=12 then 11038055319 else
  if aa=13 then 9087508208 else
  0

theorem raw_first_cost_upper_14 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 14 ≤ (235118380027/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 13) :
      rawRow 14 aa ≤ rowGrid_14 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 13 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_14,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 14 ≤ (4806908031/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 13,rowGrid_14 aa/10000000000)+(4806908031/10000000000 : ℝ)=(235118380027/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_14]
  change (∑ aa ∈ Finset.Icc 2 13,rawRow 14 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 14 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_14 : c ≤ coefficient profile 14 := by
  have hf := raw_first_cost_upper_14
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 14-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 14-1-
      (K*C/young 14)*(14 : ℝ)^2-(235118380027/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 14 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 14-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 14-1-
      ((K*C/young 14)*(14 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 14+
        t 3*tripleHarmonicNeighborCharge K young zeta 14)
  linarith only [hf,hn]

def rowGrid_15 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 20416916504 else
  if aa=4 then 26261801070 else
  if aa=5 then 29081549368 else
  if aa=6 then 30579334623 else
  if aa=7 then 30700784909 else
  if aa=8 then 28763672505 else
  if aa=9 then 25700021130 else
  if aa=10 then 22636126532 else
  if aa=11 then 19497219211 else
  if aa=12 then 16083733670 else
  if aa=13 then 11121163404 else
  if aa=14 then 9120449788 else
  0

theorem raw_first_cost_upper_15 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 15 ≤ (274073168613/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 14) :
      rawRow 15 aa ≤ rowGrid_15 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 14 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_15,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 15 ≤ (4110395899/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 14,rowGrid_15 aa/10000000000)+(4110395899/10000000000 : ℝ)=(274073168613/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_15]
  change (∑ aa ∈ Finset.Icc 2 14,rawRow 15 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 15 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_15 : c ≤ coefficient profile 15 := by
  have hf := raw_first_cost_upper_15
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 15-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 15-1-
      (K*C/young 15)*(15 : ℝ)^2-(274073168613/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 15 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 15-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 15-1-
      ((K*C/young 15)*(15 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 15+
        t 3*tripleHarmonicNeighborCharge K young zeta 15)
  linarith only [hf,hn]

def rowGrid_16 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 22474724817 else
  if aa=4 then 26833636414 else
  if aa=5 then 30066238878 else
  if aa=6 then 32147605919 else
  if aa=7 then 33031298136 else
  if aa=8 then 31943486666 else
  if aa=9 then 29523821304 else
  if aa=10 then 26297974444 else
  if aa=11 then 23072112355 else
  if aa=12 then 19789988322 else
  if aa=13 then 16258402412 else
  if aa=14 then 11198374891 else
  if aa=15 then 9150600530 else
  0

theorem raw_first_cost_upper_16 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 16 ≤ (315143828647/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 15) :
      rawRow 16 aa ≤ rowGrid_16 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 15 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_16,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 16 ≤ (3355563559/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 15,rowGrid_16 aa/10000000000)+(3355563559/10000000000 : ℝ)=(315143828647/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_16]
  change (∑ aa ∈ Finset.Icc 2 15,rawRow 16 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 16 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_16 : c ≤ coefficient profile 16 := by
  have hf := raw_first_cost_upper_16
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 16-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 16-1-
      (K*C/young 16)*(16 : ℝ)^2-(315143828647/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 16 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 16-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 16-1-
      ((K*C/young 16)*(16 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 16+
        t 3*tripleHarmonicNeighborCharge K young zeta 16)
  linarith only [hf,hn]

def rowGrid_17 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 24621153009 else
  if aa=4 then 27270106345 else
  if aa=5 then 30813548047 else
  if aa=6 then 33336329494 else
  if aa=7 then 34830028310 else
  if aa=8 then 34471966739 else
  if aa=9 then 32886536074 else
  if aa=10 then 30301837696 else
  if aa=11 then 26885314744 else
  if aa=12 then 23489177100 else
  if aa=13 then 20065228718 else
  if aa=14 then 16420645679 else
  if aa=15 then 11269273608 else
  if aa=16 then 9178192827 else
  0

theorem raw_first_cost_upper_17 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 17 ≤ (358329694052/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 16) :
      rawRow 17 aa ≤ rowGrid_17 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 16 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_17,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 17 ≤ (2490355662/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 16,rowGrid_17 aa/10000000000)+(2490355662/10000000000 : ℝ)=(358329694052/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_17]
  change (∑ aa ∈ Finset.Icc 2 16,rawRow 17 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 17 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_17 : c ≤ coefficient profile 17 := by
  have hf := raw_first_cost_upper_17
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 17-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 17-1-
      (K*C/young 17)*(17 : ℝ)^2-(358329694052/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 17 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 17-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 17-1-
      ((K*C/young 17)*(17 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 17+
        t 3*tripleHarmonicNeighborCharge K young zeta 17)
  linarith only [hf,hn]

def rowGrid_18 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 27130543990 else
  if aa=4 then 27614426391 else
  if aa=5 then 31399681043 else
  if aa=6 then 34257574614 else
  if aa=7 then 36215893067 else
  if aa=8 then 36447729162 else
  if aa=9 then 35585912239 else
  if aa=10 then 33844707030 else
  if aa=11 then 31062615532 else
  if aa=12 then 27445541074 else
  if aa=13 then 23880455510 else
  if aa=14 then 20320421102 else
  if aa=15 then 16569422750 else
  if aa=16 then 11333909276 else
  if aa=17 then 9203084407 else
  0

theorem raw_first_cost_upper_18 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 18 ≤ (403702624146/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 17) :
      rawRow 18 aa ≤ rowGrid_18 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 17 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_18,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 18 ≤ (1390706959/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 17,rowGrid_18 aa/10000000000)+(1390706959/10000000000 : ℝ)=(403702624146/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_18]
  change (∑ aa ∈ Finset.Icc 2 17,rawRow 18 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 18 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_18 : c ≤ coefficient profile 18 := by
  have hf := raw_first_cost_upper_18
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 18-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 18-1-
      (K*C/young 18)*(18 : ℝ)^2-(403702624146/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 18 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 18-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 18-1-
      ((K*C/young 18)*(18 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 18+
        t 3*tripleHarmonicNeighborCharge K young zeta 18)
  linarith only [hf,hn]

def rowGrid_19 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 28966313615 else
  if aa=4 then 27899608464 else
  if aa=5 then 31874331091 else
  if aa=6 then 34995063717 else
  if aa=7 then 37308232927 else
  if aa=8 then 37991154817 else
  if aa=9 then 37718044158 else
  if aa=10 then 36712789034 else
  if aa=11 then 34779750391 else
  if aa=12 then 31787863645 else
  if aa=13 then 27971338524 else
  if aa=14 then 24243640964 else
  if aa=15 then 20554953574 else
  if aa=16 then 16705436785 else
  if aa=17 then 11392593659 else
  if aa=18 then 9225715404 else
  0

theorem raw_first_cost_upper_19 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 19 ≤ (450695967955/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 18) :
      rawRow 19 aa ≤ rowGrid_19 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 18 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_19,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 19 ≤ (569137186/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 18,rowGrid_19 aa/10000000000)+(569137186/10000000000 : ℝ)=(450695967955/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_19]
  change (∑ aa ∈ Finset.Icc 2 18,rawRow 19 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 19 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_19 : c ≤ coefficient profile 19 := by
  have hf := raw_first_cost_upper_19
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 19-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 19-1-
      (K*C/young 19)*(19 : ℝ)^2-(450695967955/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 19 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 19-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 19-1-
      ((K*C/young 19)*(19 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 19+
        t 3*tripleHarmonicNeighborCharge K young zeta 19)
  linarith only [hf,hn]

def rowGrid_20 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 30274329211 else
  if aa=4 then 28138566672 else
  if aa=5 then 32275265266 else
  if aa=6 then 35603221018 else
  if aa=7 then 38196319250 else
  if aa=8 then 39224248722 else
  if aa=9 then 39402868850 else
  if aa=10 then 38999146152 else
  if aa=11 then 37811137188 else
  if aa=12 then 35671094877 else
  if aa=13 then 32469040318 else
  if aa=14 then 28460016352 else
  if aa=15 then 24578099556 else
  if aa=16 then 20769862223 else
  if aa=17 then 16829351054 else
  if aa=18 then 11446057267 else
  if aa=19 then 9246273001 else
  0

theorem raw_first_cost_upper_20 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 20 ≤ (499394896977/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 19) :
      rawRow 20 aa ≤ rowGrid_20 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 19 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_20,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 20 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 19,rowGrid_20 aa/10000000000)+(0/10000000000 : ℝ)=(499394896977/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_20]
  change (∑ aa ∈ Finset.Icc 2 19,rawRow 20 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 20 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_20 : c ≤ coefficient profile 20 := by
  have hf := raw_first_cost_upper_20
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 20-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 20-1-
      (K*C/young 20)*(20 : ℝ)^2-(499394896977/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 20 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 20-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 20-1-
      ((K*C/young 20)*(20 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 20+
        t 3*tripleHarmonicNeighborCharge K young zeta 20)
  linarith only [hf,hn]

def rowGrid_21 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 30461861370 else
  if aa=4 then 28370545301 else
  if aa=5 then 32615764293 else
  if aa=6 then 36122009938 else
  if aa=7 then 38936588102 else
  if aa=8 then 40236977093 else
  if aa=9 then 40761847409 else
  if aa=10 then 40821377323 else
  if aa=11 then 40244944777 else
  if aa=12 then 38856492455 else
  if aa=13 then 36507191779 else
  if aa=14 then 33101313313 else
  if aa=15 then 28909426561 else
  if aa=16 then 24883948343 else
  if aa=17 then 20965104269 else
  if aa=18 then 16941605054 else
  if aa=19 then 11494139132 else
  if aa=20 then 9264470199 else
  0

theorem raw_first_cost_upper_21 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 21 ≤ (549495606711/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 20) :
      rawRow 21 aa ≤ rowGrid_21 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 20 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_21,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 21 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 20,rowGrid_21 aa/10000000000)+(0/10000000000 : ℝ)=(549495606711/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_21]
  change (∑ aa ∈ Finset.Icc 2 20,rawRow 21 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 21 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_21 : c ≤ coefficient profile 21 := by
  have hf := raw_first_cost_upper_21
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 21-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 21-1-
      (K*C/young 21)*(21 : ℝ)^2-(549495606711/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 21 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 21-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 21-1-
      ((K*C/young 21)*(21 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 21+
        t 3*tripleHarmonicNeighborCharge K young zeta 21)
  linarith only [hf,hn]

def rowGrid_22 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 30622808243 else
  if aa=4 then 28597315196 else
  if aa=5 then 32943439668 else
  if aa=6 then 36568346047 else
  if aa=7 then 39574567848 else
  if aa=8 then 41090118605 else
  if aa=9 then 41889023971 else
  if aa=10 then 42304770198 else
  if aa=11 then 42200690946 else
  if aa=12 then 41431519560 else
  if aa=13 then 39838341760 else
  if aa=14 then 37284632822 else
  if aa=15 then 33684121690 else
  if aa=16 then 29321497048 else
  if aa=17 then 25162765649 else
  if aa=18 then 21142672414 else
  if aa=19 then 17043185042 else
  if aa=20 then 11537348126 else
  if aa=21 then 9281031772 else
  0

theorem raw_first_cost_upper_22 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 22 ≤ (601518196605/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 21) :
      rawRow 22 aa ≤ rowGrid_22 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 21 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_22,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 22 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 21,rowGrid_22 aa/10000000000)+(0/10000000000 : ℝ)=(601518196605/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_22]
  change (∑ aa ∈ Finset.Icc 2 21,rawRow 22 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 22 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_22 : c ≤ coefficient profile 22 := by
  have hf := raw_first_cost_upper_22
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 22-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 22-1-
      (K*C/young 22)*(22 : ℝ)^2-(601518196605/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 22 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 22-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 22-1-
      ((K*C/young 22)*(22 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 22+
        t 3*tripleHarmonicNeighborCharge K young zeta 22)
  linarith only [hf,hn]

def rowGrid_23 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 30759216045 else
  if aa=4 then 28794963670 else
  if aa=5 then 33260533924 else
  if aa=6 then 36995542134 else
  if aa=7 then 40128440910 else
  if aa=8 then 41831012663 else
  if aa=9 then 42846463899 else
  if aa=10 then 43545012338 else
  if aa=11 then 43805026097 else
  if aa=12 then 43515280076 else
  if aa=13 then 42547222613 else
  if aa=14 then 40752606542 else
  if aa=15 then 38002535071 else
  if aa=16 then 34219572978 else
  if aa=17 then 29698048834 else
  if aa=18 then 25416978543 else
  if aa=19 then 21303883682 else
  if aa=20 then 17134956328 else
  if aa=21 then 11576688913 else
  if aa=22 then 9296060782 else
  0

theorem raw_first_cost_upper_23 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 23 ≤ (655430046042/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 22) :
      rawRow 23 aa ≤ rowGrid_23 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 22 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_23,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 23 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 22,rowGrid_23 aa/10000000000)+(0/10000000000 : ℝ)=(655430046042/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_23]
  change (∑ aa ∈ Finset.Icc 2 22,rawRow 23 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 23 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_23 : c ≤ coefficient profile 23 := by
  have hf := raw_first_cost_upper_23
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 23-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 23-1-
      (K*C/young 23)*(23 : ℝ)^2-(655430046042/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 23 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 23-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 23-1-
      ((K*C/young 23)*(23 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 23+
        t 3*tripleHarmonicNeighborCharge K young zeta 23)
  linarith only [hf,hn]

def rowGrid_24 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 30866409951 else
  if aa=4 then 28963588790 else
  if aa=5 then 33537144319 else
  if aa=6 then 37403759887 else
  if aa=7 then 40653875691 else
  if aa=8 then 42475653980 else
  if aa=9 then 43679892359 else
  if aa=10 then 44602453865 else
  if aa=11 then 45152168361 else
  if aa=12 then 45232621168 else
  if aa=13 then 44749452597 else
  if aa=14 then 43584387238 else
  if aa=15 then 41595244346 else
  if aa=16 then 38660504491 else
  if aa=17 then 34707389782 else
  if aa=18 then 30039939722 else
  if aa=19 then 25646518255 else
  if aa=20 then 21448484691 else
  if aa=21 then 17217375778 else
  if aa=22 then 11611615564 else
  if aa=23 then 9309032469 else
  0

theorem raw_first_cost_upper_24 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 24 ≤ (711137513304/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 23) :
      rawRow 24 aa ≤ rowGrid_24 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 23 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_24,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 24 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 23,rowGrid_24 aa/10000000000)+(0/10000000000 : ℝ)=(711137513304/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_24]
  change (∑ aa ∈ Finset.Icc 2 23,rawRow 24 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 24 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_24 : c ≤ coefficient profile 24 := by
  have hf := raw_first_cost_upper_24
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 24-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 24-1-
      (K*C/young 24)*(24 : ℝ)^2-(711137513304/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 24 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 24-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 24-1-
      ((K*C/young 24)*(24 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 24+
        t 3*tripleHarmonicNeighborCharge K young zeta 24)
  linarith only [hf,hn]

def rowGrid_25 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 30940801539 else
  if aa=4 then 29102060992 else
  if aa=5 then 33777105780 else
  if aa=6 then 37763534860 else
  if aa=7 then 41155542948 else
  if aa=8 then 43087397038 else
  if aa=9 then 44410306608 else
  if aa=10 then 45528762143 else
  if aa=11 then 46308366558 else
  if aa=12 then 46683879505 else
  if aa=13 then 46575573950 else
  if aa=14 then 45899501857 else
  if aa=15 then 44543029263 else
  if aa=16 then 42370066387 else
  if aa=17 then 39262269569 else
  if aa=18 then 35152288924 else
  if aa=19 then 30350375234 else
  if aa=20 then 25853941586 else
  if aa=21 then 21579485589 else
  if aa=22 then 17291623072 else
  if aa=23 then 11642835338 else
  if aa=24 then 9321054799 else
  0

theorem raw_first_cost_upper_25 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 25 ≤ (768599803539/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 24) :
      rawRow 25 aa ≤ rowGrid_25 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 24 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_25,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 25 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 24,rowGrid_25 aa/10000000000)+(0/10000000000 : ℝ)=(768599803539/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_25]
  change (∑ aa ∈ Finset.Icc 2 24,rawRow 25 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 25 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_25 : c ≤ coefficient profile 25 := by
  have hf := raw_first_cost_upper_25
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 25-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 25-1-
      (K*C/young 25)*(25 : ℝ)^2-(768599803539/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 25 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 25-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 25-1-
      ((K*C/young 25)*(25 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 25+
        t 3*tripleHarmonicNeighborCharge K young zeta 25)
  linarith only [hf,hn]

def rowGrid_26 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 30978522469 else
  if aa=4 then 29206089283 else
  if aa=5 then 33978016999 else
  if aa=6 then 38077919871 else
  if aa=7 then 41599674895 else
  if aa=8 then 43669765618 else
  if aa=9 then 45102246858 else
  if aa=10 then 46343867787 else
  if aa=11 then 47325016502 else
  if aa=12 then 47934920568 else
  if aa=13 then 48125762261 else
  if aa=14 then 47828050841 else
  if aa=15 then 46963558695 else
  if aa=16 then 45425470616 else
  if aa=17 then 43079559095 else
  if aa=18 then 39811750918 else
  if aa=19 then 35556813908 else
  if aa=20 then 30631385126 else
  if aa=21 then 26042067336 else
  if aa=22 then 21697720541 else
  if aa=23 then 17358255972 else
  if aa=24 then 11671414509 else
  if aa=25 then 9331882954 else
  0

theorem raw_first_cost_upper_26 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 26 ≤ (827739733622/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 25) :
      rawRow 26 aa ≤ rowGrid_26 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 25 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_26,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 26 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 25,rowGrid_26 aa/10000000000)+(0/10000000000 : ℝ)=(827739733622/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_26]
  change (∑ aa ∈ Finset.Icc 2 25,rawRow 26 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 26 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_26 : c ≤ coefficient profile 26 := by
  have hf := raw_first_cost_upper_26
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 26-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 26-1-
      (K*C/young 26)*(26 : ℝ)^2-(827739733622/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 26 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 26-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 26-1-
      ((K*C/young 26)*(26 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 26+
        t 3*tripleHarmonicNeighborCharge K young zeta 26)
  linarith only [hf,hn]

def rowGrid_27 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 30957871903 else
  if aa=4 then 29269992299 else
  if aa=5 then 34132472652 else
  if aa=6 then 38341479809 else
  if aa=7 then 41986586904 else
  if aa=8 then 44183744799 else
  if aa=9 then 45756083068 else
  if aa=10 then 47111479412 else
  if aa=11 then 48218896542 else
  if aa=12 then 49034684297 else
  if aa=13 then 49463261985 else
  if aa=14 then 49467748928 else
  if aa=15 then 48984171637 else
  if aa=16 then 47940299677 else
  if aa=17 then 46230820401 else
  if aa=18 then 43724735116 else
  if aa=19 then 40308864810 else
  if aa=20 then 35920756083 else
  if aa=21 then 30884131268 else
  if aa=22 then 26210091723 else
  if aa=23 then 21802409845 else
  if aa=24 then 17417703205 else
  if aa=25 then 11696280492 else
  if aa=26 then 9340913334 else
  0

theorem raw_first_cost_upper_27 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 27 ≤ (888385480189/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 26) :
      rawRow 27 aa ≤ rowGrid_27 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 26 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_27,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 27 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 26,rowGrid_27 aa/10000000000)+(0/10000000000 : ℝ)=(888385480189/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_27]
  change (∑ aa ∈ Finset.Icc 2 26,rawRow 27 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 27 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_27 : c ≤ coefficient profile 27 := by
  have hf := raw_first_cost_upper_27
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 27-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 27-1-
      (K*C/young 27)*(27 : ℝ)^2-(888385480189/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 27 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 27-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 27-1-
      ((K*C/young 27)*(27 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 27+
        t 3*tripleHarmonicNeighborCharge K young zeta 27)
  linarith only [hf,hn]

def rowGrid_28 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 30871718811 else
  if aa=4 then 29277036621 else
  if aa=5 then 34238210650 else
  if aa=6 then 38550738436 else
  if aa=7 then 42315583737 else
  if aa=8 then 44635177525 else
  if aa=9 then 46336647560 else
  if aa=10 then 47837834659 else
  if aa=11 then 49062067139 else
  if aa=12 then 50006215260 else
  if aa=13 then 50644027288 else
  if aa=14 then 50888703826 else
  if aa=15 then 50709501685 else
  if aa=16 then 50048333758 else
  if aa=17 then 48834530704 else
  if aa=18 then 46965791615 else
  if aa=19 then 44310901478 else
  if aa=20 then 40758416901 else
  if aa=21 then 36250026834 else
  if aa=22 then 31111616869 else
  if aa=23 then 26360463228 else
  if aa=24 then 21896938869 else
  if aa=25 then 17470658572 else
  if aa=26 then 11718227990 else
  if aa=27 then 9349393775 else
  0

theorem raw_first_cost_upper_28 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 28 ≤ (950448763790/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 27) :
      rawRow 28 aa ≤ rowGrid_28 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 27 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_28,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 28 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 27,rowGrid_28 aa/10000000000)+(0/10000000000 : ℝ)=(950448763790/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_28]
  change (∑ aa ∈ Finset.Icc 2 27,rawRow 28 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 28 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_28 : c ≤ coefficient profile 28 := by
  have hf := raw_first_cost_upper_28
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 28-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 28-1-
      (K*C/young 28)*(28 : ℝ)^2-(950448763790/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 28 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 28-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 28-1-
      ((K*C/young 28)*(28 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 28+
        t 3*tripleHarmonicNeighborCharge K young zeta 28)
  linarith only [hf,hn]

def rowGrid_29 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 30713642798 else
  if aa=4 then 29219252024 else
  if aa=5 then 34274240101 else
  if aa=6 then 38701542736 else
  if aa=7 then 42581056654 else
  if aa=8 then 45021431309 else
  if aa=9 then 46848061110 else
  if aa=10 then 48484123699 else
  if aa=11 then 49858921603 else
  if aa=12 then 50921926799 else
  if aa=13 then 51689353945 else
  if aa=14 then 52145776277 else
  if aa=15 then 52208456222 else
  if aa=16 then 51853188327 else
  if aa=17 then 51023255460 else
  if aa=18 then 49651152337 else
  if aa=19 then 47634028544 else
  if aa=20 then 44841444321 else
  if aa=21 then 41165409273 else
  if aa=22 then 36546668341 else
  if aa=23 then 31315499716 else
  if aa=24 then 26496237733 else
  if aa=25 then 21981334935 else
  if aa=26 then 17517644658 else
  if aa=27 then 11738384195 else
  if aa=28 then 9356980385 else
  0

theorem raw_first_cost_upper_29 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 29 ≤ (1013789013502/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 28) :
      rawRow 29 aa ≤ rowGrid_29 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 28 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_29,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 29 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 28,rowGrid_29 aa/10000000000)+(0/10000000000 : ℝ)=(1013789013502/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_29]
  change (∑ aa ∈ Finset.Icc 2 28,rawRow 29 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 29 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_29 : c ≤ coefficient profile 29 := by
  have hf := raw_first_cost_upper_29
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 29-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 29-1-
      (K*C/young 29)*(29 : ℝ)^2-(1013789013502/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 29 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 29-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 29-1-
      ((K*C/young 29)*(29 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 29+
        t 3*tripleHarmonicNeighborCharge K young zeta 29)
  linarith only [hf,hn]

def rowGrid_30 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 30423373583 else
  if aa=4 then 29089728897 else
  if aa=5 then 34230234429 else
  if aa=6 then 38769045867 else
  if aa=7 then 42777172068 else
  if aa=8 then 45335191670 else
  if aa=9 then 47286123624 else
  if aa=10 then 49053118556 else
  if aa=11 then 50567441229 else
  if aa=12 then 51784755138 else
  if aa=13 then 52672266501 else
  if aa=14 then 53258884661 else
  if aa=15 then 53535105106 else
  if aa=16 then 53422847694 else
  if aa=17 then 52899804494 else
  if aa=18 then 51912332014 else
  if aa=19 then 50392401827 else
  if aa=20 then 48237676413 else
  if aa=21 then 45320509461 else
  if aa=22 then 41530958803 else
  if aa=23 then 36811593427 else
  if aa=24 then 31498551350 else
  if aa=25 then 26616744142 else
  if aa=26 then 22055685489 else
  if aa=27 then 17559904482 else
  if aa=28 then 11756028966 else
  if aa=29 then 9363447491 else
  0

theorem raw_first_cost_upper_30 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 30 ≤ (1078160927382/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 29) :
      rawRow 30 aa ≤ rowGrid_30 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 29 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_30,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 30 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 29,rowGrid_30 aa/10000000000)+(0/10000000000 : ℝ)=(1078160927382/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_30]
  change (∑ aa ∈ Finset.Icc 2 29,rawRow 30 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 30 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_30 : c ≤ coefficient profile 30 := by
  have hf := raw_first_cost_upper_30
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 30-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 30-1-
      (K*C/young 30)*(30 : ℝ)^2-(1078160927382/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 30 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 30-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 30-1-
      ((K*C/young 30)*(30 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 30+
        t 3*tripleHarmonicNeighborCharge K young zeta 30)
  linarith only [hf,hn]

def rowGrid_31 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 30022457434 else
  if aa=4 then 28832883322 else
  if aa=5 then 34099876990 else
  if aa=6 then 38743558843 else
  if aa=7 then 42878665998 else
  if aa=8 then 45572562784 else
  if aa=9 then 47645537537 else
  if aa=10 then 49542860024 else
  if aa=11 then 51192979887 else
  if aa=12 then 52553589435 else
  if aa=13 then 53598355478 else
  if aa=14 then 54305689128 else
  if aa=15 then 54712171151 else
  if aa=16 then 54814720225 else
  if aa=17 then 54535336271 else
  if aa=18 then 53855343529 else
  if aa=19 then 52720391202 else
  if aa=20 then 51063018653 else
  if aa=21 then 48783609423 else
  if aa=22 then 45751639612 else
  if aa=23 then 41858257144 else
  if aa=24 then 37049999837 else
  if aa=25 then 31661658341 else
  if aa=26 then 26723527580 else
  if aa=27 then 22122762463 else
  if aa=28 then 17597332346 else
  if aa=29 then 11771534158 else
  if aa=30 then 9369321438 else
  0

theorem raw_first_cost_upper_31 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 31 ≤ (1143379640233/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 30) :
      rawRow 31 aa ≤ rowGrid_31 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 30 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_31,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 31 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 30,rowGrid_31 aa/10000000000)+(0/10000000000 : ℝ)=(1143379640233/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_31]
  change (∑ aa ∈ Finset.Icc 2 30,rawRow 31 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 31 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_31 : c ≤ coefficient profile 31 := by
  have hf := raw_first_cost_upper_31
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 31-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 31-1-
      (K*C/young 31)*(31 : ℝ)^2-(1143379640233/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 31 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 31-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 31-1-
      ((K*C/young 31)*(31 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 31+
        t 3*tripleHarmonicNeighborCharge K young zeta 31)
  linarith only [hf,hn]

def rowGrid_32 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 29565584182 else
  if aa=4 then 28468803798 else
  if aa=5 then 33817655095 else
  if aa=6 then 38617550867 else
  if aa=7 then 42874388709 else
  if aa=8 then 45706179854 else
  if aa=9 then 47921731797 else
  if aa=10 then 49947283056 else
  if aa=11 then 51732937436 else
  if aa=12 then 53233386240 else
  if aa=13 then 54424468819 else
  if aa=14 then 55291333570 else
  if aa=15 then 55818670561 else
  if aa=16 then 56051181162 else
  if aa=17 then 55987418127 else
  if aa=18 then 55551399730 else
  if aa=19 then 54724167482 else
  if aa=20 then 53451799211 else
  if aa=21 then 51669744331 else
  if aa=22 then 49275164946 else
  if aa=23 then 46137931946 else
  if aa=24 then 42152856761 else
  if aa=25 then 37262635250 else
  if aa=26 then 31806420141 else
  if aa=27 then 26819758272 else
  if aa=28 then 22182287038 else
  if aa=29 then 17630374331 else
  if aa=30 then 11785491637 else
  if aa=31 then 9374549707 else
  0

theorem raw_first_cost_upper_32 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 32 ≤ (1209283154056/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 31) :
      rawRow 32 aa ≤ rowGrid_32 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 31 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_32,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 32 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 31,rowGrid_32 aa/10000000000)+(0/10000000000 : ℝ)=(1209283154056/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_32]
  change (∑ aa ∈ Finset.Icc 2 31,rawRow 32 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 32 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_32 : c ≤ coefficient profile 32 := by
  have hf := raw_first_cost_upper_32
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 32-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 32-1-
      (K*C/young 32)*(32 : ℝ)^2-(1209283154056/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 32 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 32-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 32-1-
      ((K*C/young 32)*(32 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 32+
        t 3*tripleHarmonicNeighborCharge K young zeta 32)
  linarith only [hf,hn]

def rowGrid_33 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 29058249263 else
  if aa=4 then 28050637765 else
  if aa=5 then 33408573252 else
  if aa=6 then 38318517567 else
  if aa=7 then 42757908259 else
  if aa=8 then 45726177042 else
  if aa=9 then 48088061487 else
  if aa=10 then 50263813598 else
  if aa=11 then 52183262484 else
  if aa=12 then 53823770176 else
  if aa=13 then 55158087815 else
  if aa=14 then 56173708057 else
  if aa=15 then 56862312529 else
  if aa=16 then 57215487408 else
  if aa=17 then 57281093643 else
  if aa=18 then 57061179556 else
  if aa=19 then 56477915977 else
  if aa=20 then 55513187057 else
  if aa=21 then 54115970279 else
  if aa=22 then 52218424343 else
  if aa=23 then 49717907498 else
  if aa=24 then 46487617489 else
  if aa=25 then 42417557912 else
  if aa=26 then 37453119162 else
  if aa=27 then 31938106051 else
  if aa=28 then 26906370459 else
  if aa=29 then 22235879489 else
  if aa=30 then 17660763060 else
  if aa=31 then 11798404327 else
  if aa=32 then 9379586868 else
  0

theorem raw_first_cost_upper_33 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 33 ≤ (1275751649872/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 32) :
      rawRow 33 aa ≤ rowGrid_33 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 32 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_33,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 33 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 32,rowGrid_33 aa/10000000000)+(0/10000000000 : ℝ)=(1275751649872/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_33]
  change (∑ aa ∈ Finset.Icc 2 32,rawRow 33 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 33 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_33 : c ≤ coefficient profile 33 := by
  have hf := raw_first_cost_upper_33
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 33-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 33-1-
      (K*C/young 33)*(33 : ℝ)^2-(1275751649872/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 33 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 33-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 33-1-
      ((K*C/young 33)*(33 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 33+
        t 3*tripleHarmonicNeighborCharge K young zeta 33)
  linarith only [hf,hn]

def rowGrid_34 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 27837641591 else
  if aa=4 then 27582557661 else
  if aa=5 then 32933680212 else
  if aa=6 then 37873195726 else
  if aa=7 then 42447218566 else
  if aa=8 then 45623880195 else
  if aa=9 then 48132237845 else
  if aa=10 then 50462529553 else
  if aa=11 then 52539218565 else
  if aa=12 then 54318406247 else
  if aa=13 then 55796638938 else
  if aa=14 then 56958285783 else
  if aa=15 then 57797540851 else
  if aa=16 then 58313276729 else
  if aa=17 then 58499068245 else
  if aa=18 then 58407742453 else
  if aa=19 then 58040776798 else
  if aa=20 then 57319774793 else
  if aa=21 then 56230001756 else
  if aa=22 then 54716929022 else
  if aa=23 then 52712951388 else
  if aa=24 then 50118818156 else
  if aa=25 then 46802036638 else
  if aa=26 then 42654897530 else
  if aa=27 then 37626270571 else
  if aa=28 then 32056657081 else
  if aa=29 then 26984347619 else
  if aa=30 then 22284918841 else
  if aa=31 then 17688615827 else
  if aa=32 then 11810421123 else
  if aa=33 then 9384097783 else
  0

theorem raw_first_cost_upper_34 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 34 ≤ (1341954634086/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 33) :
      rawRow 34 aa ≤ rowGrid_34 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 33 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_34,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 34 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 33,rowGrid_34 aa/10000000000)+(0/10000000000 : ℝ)=(1341954634086/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_34]
  change (∑ aa ∈ Finset.Icc 2 33,rawRow 34 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 34 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_34 : c ≤ coefficient profile 34 := by
  have hf := raw_first_cost_upper_34
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 34-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 34-1-
      (K*C/young 34)*(34 : ℝ)^2-(1341954634086/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 34 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 34-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 34-1-
      ((K*C/young 34)*(34 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 34+
        t 3*tripleHarmonicNeighborCharge K young zeta 34)
  linarith only [hf,hn]

def rowGrid_35 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 27583638149 else
  if aa=4 then 26435932121 else
  if aa=5 then 32398817400 else
  if aa=6 then 37351787190 else
  if aa=7 then 41972959268 else
  if aa=8 then 45312925675 else
  if aa=9 then 48046358548 else
  if aa=10 then 50531815264 else
  if aa=11 then 52770874216 else
  if aa=12 then 54713752244 else
  if aa=13 then 56334966639 else
  if aa=14 then 57643832342 else
  if aa=15 then 58631401734 else
  if aa=16 then 59299275548 else
  if aa=17 then 59648550149 else
  if aa=18 then 59676750530 else
  if aa=19 then 59437425618 else
  if aa=20 then 58932671384 else
  if aa=21 then 58086272832 else
  if aa=22 then 56880245391 else
  if aa=23 then 55260191257 else
  if aa=24 then 53162134705 else
  if aa=25 then 50480701786 else
  if aa=26 then 47085273018 else
  if aa=27 then 42871549852 else
  if aa=28 then 37783078986 else
  if aa=29 then 32164154242 else
  if aa=30 then 27056135623 else
  if aa=31 then 22330196343 else
  if aa=32 then 17714669624 else
  if aa=33 then 11821464905 else
  if aa=34 then 9388357606 else
  0

theorem raw_first_cost_upper_35 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 35 ≤ (1408808160189/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 34) :
      rawRow 35 aa ≤ rowGrid_35 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 34 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_35,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 35 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 34,rowGrid_35 aa/10000000000)+(0/10000000000 : ℝ)=(1408808160189/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_35]
  change (∑ aa ∈ Finset.Icc 2 34,rawRow 35 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 35 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_35 : c ≤ coefficient profile 35 := by
  have hf := raw_first_cost_upper_35
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 35-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 35-1-
      (K*C/young 35)*(35 : ℝ)^2-(1408808160189/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 35 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 35-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 35-1-
      ((K*C/young 35)*(35 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 35+
        t 3*tripleHarmonicNeighborCharge K young zeta 35)
  linarith only [hf,hn]

def rowGrid_36 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 27350341293 else
  if aa=4 then 26204138856 else
  if aa=5 then 31063143829 else
  if aa=6 then 36758386224 else
  if aa=7 then 41409995205 else
  if aa=8 then 44822761758 else
  if aa=9 then 47736054379 else
  if aa=10 then 50459794748 else
  if aa=11 then 52862333216 else
  if aa=12 then 54974759152 else
  if aa=13 then 56765396825 else
  if aa=14 then 58220912123 else
  if aa=15 then 59358425053 else
  if aa=16 then 60176435674 else
  if aa=17 then 60678940597 else
  if aa=18 then 60871256486 else
  if aa=19 then 60750645057 else
  if aa=20 then 60372485860 else
  if aa=21 then 59742214788 else
  if aa=22 then 58779113355 else
  if aa=23 then 57465645101 else
  if aa=24 then 55751122807 else
  if aa=25 then 53565249244 else
  if aa=26 then 50804464799 else
  if aa=27 then 47341447211 else
  if aa=28 then 43065700131 else
  if aa=29 then 37923412228 else
  if aa=30 then 32261320260 else
  if aa=31 then 27120856962 else
  if aa=32 then 22371129161 else
  if aa=33 then 17737611032 else
  if aa=34 then 11831084399 else
  if aa=35 then 9391733915 else
  0

theorem raw_first_cost_upper_36 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 36 ≤ (1475988311728/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 35) :
      rawRow 36 aa ≤ rowGrid_36 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 35 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_36,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 36 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 35,rowGrid_36 aa/10000000000)+(0/10000000000 : ℝ)=(1475988311728/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_36]
  change (∑ aa ∈ Finset.Icc 2 35,rawRow 36 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 36 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_36 : c ≤ coefficient profile 36 := by
  have hf := raw_first_cost_upper_36
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 36-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 36-1-
      (K*C/young 36)*(36 : ℝ)^2-(1475988311728/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 36 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 36-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 36-1-
      ((K*C/young 36)*(36 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 36+
        t 3*tripleHarmonicNeighborCharge K young zeta 36)
  linarith only [hf,hn]

def rowGrid_37 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 27111472657 else
  if aa=4 then 25989758301 else
  if aa=5 then 30799368861 else
  if aa=6 then 35252817402 else
  if aa=7 then 40763491534 else
  if aa=8 then 44233911830 else
  if aa=9 then 47232852391 else
  if aa=10 then 50147890255 else
  if aa=11 then 52801717994 else
  if aa=12 then 55085401587 else
  if aa=13 then 57052103252 else
  if aa=14 then 58682118934 else
  if aa=15 then 59969395836 else
  if aa=16 then 60939613852 else
  if aa=17 then 61593687876 else
  if aa=18 then 61940044028 else
  if aa=19 then 61983934244 else
  if aa=20 then 61723579913 else
  if aa=21 then 61218882125 else
  if aa=22 then 60471673114 else
  if aa=23 then 59400623181 else
  if aa=24 then 57992344483 else
  if aa=25 then 56189540724 else
  if aa=26 then 53923835145 else
  if aa=27 then 51095124673 else
  if aa=28 then 47569107540 else
  if aa=29 then 43237713371 else
  if aa=30 then 38048588715 else
  if aa=31 then 32347514999 else
  if aa=32 then 27178151625 else
  if aa=33 then 22406350252 else
  if aa=34 then 17756997262 else
  if aa=35 then 11838641081 else
  if aa=36 then 9394354084 else
  0

theorem raw_first_cost_upper_37 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 37 ≤ (1543372603121/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 36) :
      rawRow 37 aa ≤ rowGrid_37 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 36 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_37,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 37 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 36,rowGrid_37 aa/10000000000)+(0/10000000000 : ℝ)=(1543372603121/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_37]
  change (∑ aa ∈ Finset.Icc 2 36,rawRow 37 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 37 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_37 : c ≤ coefficient profile 37 := by
  have hf := raw_first_cost_upper_37
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 37-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 37-1-
      (K*C/young 37)*(37 : ℝ)^2-(1543372603121/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 37 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 37-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 37-1-
      ((K*C/young 37)*(37 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 37+
        t 3*tripleHarmonicNeighborCharge K young zeta 37)
  linarith only [hf,hn]

def rowGrid_38 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 26834015642 else
  if aa=4 then 25771507787 else
  if aa=5 then 30557751488 else
  if aa=6 then 34965317004 else
  if aa=7 then 39107134915 else
  if aa=8 then 43558084443 else
  if aa=9 then 46628144992 else
  if aa=10 then 49636088432 else
  if aa=11 then 52493130034 else
  if aa=12 then 55040893362 else
  if aa=13 then 57186309852 else
  if aa=14 then 58998503735 else
  if aa=15 then 60464948145 else
  if aa=16 then 61587734822 else
  if aa=17 then 62395989246 else
  if aa=18 then 62895120991 else
  if aa=19 then 63093643950 else
  if aa=20 then 62997973653 else
  if aa=21 then 62610139637 else
  if aa=22 then 61987381321 else
  if aa=23 then 61131800095 else
  if aa=24 then 59965382798 else
  if aa=25 then 58468204801 else
  if aa=26 then 56584874056 else
  if aa=27 then 54250729678 else
  if aa=28 then 51358243936 else
  if aa=29 then 47775301748 else
  if aa=30 then 43395139926 else
  if aa=31 then 38163181095 else
  if aa=32 then 32426842410 else
  if aa=33 then 27230170554 else
  if aa=34 then 22438444665 else
  if aa=35 then 17774363528 else
  if aa=36 then 11845959091 else
  if aa=37 then 9397539379 else
  0

theorem raw_first_cost_upper_38 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 38 ≤ (1611015991211/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 37) :
      rawRow 38 aa ≤ rowGrid_38 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 37 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_38,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 38 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 37,rowGrid_38 aa/10000000000)+(0/10000000000 : ℝ)=(1611015991211/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_38]
  change (∑ aa ∈ Finset.Icc 2 37,rawRow 38 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 38 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_38 : c ≤ coefficient profile 38 := by
  have hf := raw_first_cost_upper_38
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 38-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 38-1-
      (K*C/young 38)*(38 : ℝ)^2-(1611015991211/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 38 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 38-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 38-1-
      ((K*C/young 38)*(38 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 38+
        t 3*tripleHarmonicNeighborCharge K young zeta 38)
  linarith only [hf,hn]

def rowGrid_39 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 26582008931 else
  if aa=4 then 25513325151 else
  if aa=5 then 30307747315 else
  if aa=6 then 34698581688 else
  if aa=7 then 38796657765 else
  if aa=8 then 41797284957 else
  if aa=9 then 45925748002 else
  if aa=10 then 49011296392 else
  if aa=11 then 51968720929 else
  if aa=12 then 54731149059 else
  if aa=13 then 57152561953 else
  if aa=14 then 59150182214 else
  if aa=15 then 60804198869 else
  if aa=16 then 62110198617 else
  if aa=17 then 63073347854 else
  if aa=18 then 63728265617 else
  if aa=19 then 64080476648 else
  if aa=20 then 64139818769 else
  if aa=21 then 63916770246 else
  if aa=22 then 63409925488 else
  if aa=23 then 62677716404 else
  if aa=24 then 61726473942 else
  if aa=25 then 60470614105 else
  if aa=26 then 58892407225 else
  if aa=27 then 56940311779 else
  if aa=28 then 54541987823 else
  if aa=29 then 51592108416 else
  if aa=30 then 47959703472 else
  if aa=31 then 43535324329 else
  if aa=32 then 38265111388 else
  if aa=33 then 32495990635 else
  if aa=34 then 27275119806 else
  if aa=35 then 22465286238 else
  if aa=36 then 17789228288 else
  if aa=37 then 11852559200 else
  if aa=38 then 9399588254 else
  0

theorem raw_first_cost_upper_39 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 39 ≤ (1678777797768/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 38) :
      rawRow 39 aa ≤ rowGrid_39 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 38 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_39,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 39 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 38,rowGrid_39 aa/10000000000)+(0/10000000000 : ℝ)=(1678777797768/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_39]
  change (∑ aa ∈ Finset.Icc 2 38,rawRow 39 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 39 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_39 : c ≤ coefficient profile 39 := by
  have hf := raw_first_cost_upper_39
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 39-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 39-1-
      (K*C/young 39)*(39 : ℝ)^2-(1678777797768/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 39 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 39-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 39-1-
      ((K*C/young 39)*(39 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 39+
        t 3*tripleHarmonicNeighborCharge K young zeta 39)
  linarith only [hf,hn]

def rowGrid_40 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 26320106016 else
  if aa=4 then 25281008949 else
  if aa=5 then 30012771449 else
  if aa=6 then 34424623086 else
  if aa=7 then 38511796191 else
  if aa=8 then 41477406572 else
  if aa=9 then 44081944712 else
  if aa=10 then 48286919248 else
  if aa=11 then 51329363154 else
  if aa=12 then 54200005688 else
  if aa=13 then 56847320945 else
  if aa=14 then 59132320804 else
  if aa=15 then 60978097096 else
  if aa=16 then 62476689842 else
  if aa=17 then 63626755477 else
  if aa=18 then 64438662206 else
  if aa=19 then 64948045055 else
  if aa=20 then 65161797940 else
  if aa=21 then 65094032617 else
  if aa=22 then 64751912427 else
  if aa=23 then 64134590422 else
  if aa=24 then 63305676970 else
  if aa=25 then 62264491441 else
  if aa=26 then 60926907297 else
  if aa=27 then 59279427563 else
  if aa=28 then 57262516053 else
  if aa=29 then 54806148161 else
  if aa=30 then 51806175758 else
  if aa=31 then 48128506814 else
  if aa=32 then 43664189729 else
  if aa=33 then 38357766346 else
  if aa=34 then 32559017698 else
  if aa=35 then 27315621145 else
  if aa=36 then 22490557147 else
  if aa=37 then 17804272006 else
  if aa=38 then 11858561667 else
  if aa=39 then 9402298555 else
  0

theorem raw_first_cost_upper_40 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 40 ≤ (1746748309737/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 39) :
      rawRow 40 aa ≤ rowGrid_40 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 39 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_40,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 40 ≤ (5491/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 39,rowGrid_40 aa/10000000000)+(5491/10000000000 : ℝ)=(1746748309737/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_40]
  change (∑ aa ∈ Finset.Icc 2 39,rawRow 40 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 40 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_40 : c ≤ coefficient profile 40 := by
  have hf := raw_first_cost_upper_40
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 40-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 40-1-
      (K*C/young 40)*(40 : ℝ)^2-(1746748309737/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 40 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 40-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 40-1-
      ((K*C/young 40)*(40 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 40+
        t 3*tripleHarmonicNeighborCharge K young zeta 40)
  linarith only [hf,hn]

def rowGrid_41 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 26080574264 else
  if aa=4 then 25028273146 else
  if aa=5 then 29735134570 else
  if aa=6 then 34084592483 else
  if aa=7 then 38202141948 else
  if aa=8 then 41166839222 else
  if aa=9 then 43738182865 else
  if aa=10 then 46341541251 else
  if aa=11 then 50563328194 else
  if aa=12 then 53525366402 else
  if aa=13 then 56287406326 else
  if aa=14 then 58807902871 else
  if aa=15 then 60950766814 else
  if aa=16 then 62646206404 else
  if aa=17 then 63992833444 else
  if aa=18 then 64994540649 else
  if aa=19 then 65662432660 else
  if aa=20 then 66034345453 else
  if aa=21 then 66121542493 else
  if aa=22 then 65934910946 else
  if aa=23 then 65482334077 else
  if aa=24 then 64767671932 else
  if aa=25 then 63848118272 else
  if aa=26 then 62725144208 else
  if aa=27 then 61318326984 else
  if aa=28 then 59606147845 else
  if aa=29 then 57531435917 else
  if aa=30 then 55025501226 else
  if aa=31 then 51980912853 else
  if aa=32 then 48263907267 else
  if aa=33 then 43763515527 else
  if aa=34 then 38426540840 else
  if aa=35 then 32602595542 else
  if aa=36 then 27342348035 else
  if aa=37 then 22506284014 else
  if aa=38 then 17810682941 else
  if aa=39 then 11860245879 else
  if aa=40 then 9400923230 else
  0

theorem raw_first_cost_upper_41 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 41 ≤ (1814161555580/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 40) :
      rawRow 41 aa ≤ rowGrid_41 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 40 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_41,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 41 ≤ (56586/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 40,rowGrid_41 aa/10000000000)+(56586/10000000000 : ℝ)=(1814161555580/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_41]
  change (∑ aa ∈ Finset.Icc 2 40,rawRow 41 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 41 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_41 : c ≤ coefficient profile 41 := by
  have hf := raw_first_cost_upper_41
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 41-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 41-1-
      (K*C/young 41)*(41 : ℝ)^2-(1814161555580/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 41 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 41-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 41-1-
      ((K*C/young 41)*(41 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 41+
        t 3*tripleHarmonicNeighborCharge K young zeta 41)
  linarith only [hf,hn]

def rowGrid_42 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 25880242730 else
  if aa=4 then 24858180842 else
  if aa=5 then 29506224289 else
  if aa=6 then 33847699806 else
  if aa=7 then 37912626590 else
  if aa=8 then 40930656461 else
  if aa=9 then 43511485741 else
  if aa=10 then 46086922810 else
  if aa=11 then 48638914692 else
  if aa=12 then 52848987678 else
  if aa=13 then 55715855251 else
  if aa=14 then 58363882529 else
  if aa=15 then 60757121398 else
  if aa=16 then 62763525550 else
  if aa=17 then 64315455975 else
  if aa=18 then 65520271508 else
  if aa=19 then 66382649007 else
  if aa=20 then 66915697611 else
  if aa=21 then 67162529183 else
  if aa=22 then 67131209279 else
  if aa=23 then 66833502708 else
  if aa=24 then 66282267892 else
  if aa=25 then 65474317343 else
  if aa=26 then 64469837108 else
  if aa=27 then 63274697760 else
  if aa=28 then 61799448424 else
  if aa=29 then 60025127360 else
  if aa=30 then 57895817132 else
  if aa=31 then 55339294994 else
  if aa=32 then 52248188717 else
  if aa=33 then 48486018351 else
  if aa=34 then 43943781918 else
  if aa=35 then 38567316415 else
  if aa=36 then 32710271597 else
  if aa=37 then 27424999949 else
  if aa=38 then 22566665652 else
  if aa=39 then 17854574149 else
  if aa=40 then 11886046058 else
  if aa=41 then 9422751840 else
  0

theorem raw_first_cost_upper_42 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 42 ≤ (1885555191831/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 41) :
      rawRow 42 aa ≤ rowGrid_42 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 41 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_42,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 42 ≤ (127534/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 41,rowGrid_42 aa/10000000000)+(127534/10000000000 : ℝ)=(1885555191831/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_42]
  change (∑ aa ∈ Finset.Icc 2 41,rawRow 42 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 42 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_42 : c ≤ coefficient profile 42 := by
  have hf := raw_first_cost_upper_42
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 42-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 42-1-
      (K*C/young 42)*(42 : ℝ)^2-(1885555191831/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 42 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 42-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 42-1-
      ((K*C/young 42)*(42 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 42+
        t 3*tripleHarmonicNeighborCharge K young zeta 42)
  linarith only [hf,hn]

def rowGrid_43 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 25964282491 else
  if aa=4 then 24915023446 else
  if aa=5 then 29599915701 else
  if aa=6 then 33924329234 else
  if aa=7 then 38027108674 else
  if aa=8 then 41028274004 else
  if aa=9 then 43696180568 else
  if aa=10 then 46308345650 else
  if aa=11 then 48857303197 else
  if aa=12 then 51347969406 else
  if aa=13 then 55564089612 else
  if aa=14 then 58351243639 else
  if aa=15 then 60903752126 else
  if aa=16 then 63192236182 else
  if aa=17 then 65082808317 else
  if aa=18 then 66511704711 else
  if aa=19 then 67591450499 else
  if aa=20 then 68328832187 else
  if aa=21 then 68742219871 else
  if aa=22 then 68872669127 else
  if aa=23 then 68729256705 else
  if aa=24 then 68329117095 else
  if aa=25 then 67678142383 else
  if aa=26 then 66775604364 else
  if aa=27 then 65687595012 else
  if aa=28 then 64411403000 else
  if aa=29 then 62858644445 else
  if aa=30 then 61011744396 else
  if aa=31 then 58810541801 else
  if aa=32 then 56182277066 else
  if aa=33 then 53015597547 else
  if aa=34 then 49174519878 else
  if aa=35 then 44547561734 else
  if aa=36 then 39083169170 else
  if aa=37 then 33138538905 else
  if aa=38 then 27774651125 else
  if aa=39 then 22849394496 else
  if aa=40 then 18073055829 else
  if aa=41 then 12033252614 else
  if aa=42 then 9517351984 else
  0

theorem raw_first_cost_upper_43 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 43 ≤ (1976491214842/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 42) :
      rawRow 43 aa ≤ rowGrid_43 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 42 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_43,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 43 ≤ (56651/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 42,rowGrid_43 aa/10000000000)+(56651/10000000000 : ℝ)=(1976491214842/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_43]
  change (∑ aa ∈ Finset.Icc 2 42,rawRow 43 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 43 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_43 : c ≤ coefficient profile 43 := by
  have hf := raw_first_cost_upper_43
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 43-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 43-1-
      (K*C/young 43)*(43 : ℝ)^2-(1976491214842/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 43 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 43-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 43-1-
      ((K*C/young 43)*(43 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 43+
        t 3*tripleHarmonicNeighborCharge K young zeta 43)
  linarith only [hf,hn]

def rowGrid_44 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 25323667251 else
  if aa=4 then 24356755332 else
  if aa=5 then 28909125645 else
  if aa=6 then 33161993487 else
  if aa=7 then 37138806240 else
  if aa=8 then 40100076864 else
  if aa=9 then 42680602358 else
  if aa=10 then 45315977885 else
  if aa=11 then 47836959847 else
  if aa=12 then 50259876234 else
  if aa=13 then 52605763654 else
  if aa=14 then 56704567674 else
  if aa=15 then 59333848256 else
  if aa=16 then 61725285783 else
  if aa=17 then 63852102640 else
  if aa=18 then 65584548925 else
  if aa=19 then 66860047757 else
  if aa=20 then 67794382769 else
  if aa=21 then 68399364433 else
  if aa=22 then 68690384896 else
  if aa=23 then 68709472795 else
  if aa=24 then 68470856229 else
  if aa=25 then 67984421222 else
  if aa=26 then 67258596959 else
  if aa=27 then 66297498388 else
  if aa=28 then 65158123214 else
  if aa=29 then 63840414287 else
  if aa=30 then 62258390412 else
  if aa=31 then 60391241828 else
  if aa=32 then 58179960351 else
  if aa=33 then 55550028227 else
  if aa=34 then 52393787337 else
  if aa=35 then 48575710475 else
  if aa=36 then 43989276118 else
  if aa=37 then 38582601201 else
  if aa=38 then 32703019907 else
  if aa=39 then 27403651721 else
  if aa=40 then 22537685546 else
  if aa=41 then 17829113131 else
  if aa=42 then 11843332906 else
  if aa=43 then 9274033423 else
  0

theorem raw_first_cost_upper_44 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 44 ≤ (2015865648221/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 43) :
      rawRow 44 aa ≤ rowGrid_44 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 43 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_44,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 44 ≤ (294614/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 43,rowGrid_44 aa/10000000000)+(294614/10000000000 : ℝ)=(2015865648221/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_44]
  change (∑ aa ∈ Finset.Icc 2 43,rawRow 44 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 44 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_44 : c ≤ coefficient profile 44 := by
  have hf := raw_first_cost_upper_44
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 44-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 44-1-
      (K*C/young 44)*(44 : ℝ)^2-(2015865648221/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 44 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 44-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 44-1-
      ((K*C/young 44)*(44 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 44+
        t 3*tripleHarmonicNeighborCharge K young zeta 44)
  linarith only [hf,hn]

def rowGrid_45 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 25196224282 else
  if aa=4 then 24462545470 else
  if aa=5 then 29101599378 else
  if aa=6 then 33351001494 else
  if aa=7 then 37383595428 else
  if aa=8 then 40327714234 else
  if aa=9 then 42955251447 else
  if aa=10 then 45578726497 else
  if aa=11 then 48203595017 else
  if aa=12 then 50673308730 else
  if aa=13 then 53021894127 else
  if aa=14 then 55281642457 else
  if aa=15 then 59373713344 else
  if aa=16 then 61922052666 else
  if aa=17 then 64224148674 else
  if aa=18 then 66257374448 else
  if aa=19 then 67888139534 else
  if aa=20 then 69054565161 else
  if aa=21 then 69882035559 else
  if aa=22 then 70379832891 else
  if aa=23 then 70565011989 else
  if aa=24 then 70486264557 else
  if aa=25 then 70150879778 else
  if aa=26 then 69571688867 else
  if aa=27 then 68762377664 else
  if aa=28 then 67718310470 else
  if aa=29 then 66500555327 else
  if aa=30 then 65110696599 else
  if aa=31 then 63457385413 else
  if aa=32 then 61519949228 else
  if aa=33 then 59235510478 else
  if aa=34 then 56530676660 else
  if aa=35 then 53294524749 else
  if aa=36 then 49393045633 else
  if aa=37 then 44716964470 else
  if aa=38 then 39207556252 else
  if aa=39 then 33225494497 else
  if aa=40 then 27833436236 else
  if aa=41 then 22894503700 else
  if aa=42 then 18069428279 else
  if aa=43 then 11883660339 else
  if aa=44 then 9549759279 else
  0

theorem raw_first_cost_upper_45 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 45 ≤ (2114196641302/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 44) :
      rawRow 45 aa ≤ rowGrid_45 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 44 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_45,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 45 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 44,rowGrid_45 aa/10000000000)+(0/10000000000 : ℝ)=(2114196641302/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_45]
  change (∑ aa ∈ Finset.Icc 2 44,rawRow 45 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 45 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_45 : c ≤ coefficient profile 45 := by
  have hf := raw_first_cost_upper_45
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 45-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 45-1-
      (K*C/young 45)*(45 : ℝ)^2-(2114196641302/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 45 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 45-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 45-1-
      ((K*C/young 45)*(45 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 45+
        t 3*tripleHarmonicNeighborCharge K young zeta 45)
  linarith only [hf,hn]

def rowGrid_46 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 25156478255 else
  if aa=4 then 23766733002 else
  if aa=5 then 28540928792 else
  if aa=6 then 32783839348 else
  if aa=7 then 36712871155 else
  if aa=8 then 39639280865 else
  if aa=9 then 42183605753 else
  if aa=10 then 44793700714 else
  if aa=11 then 47343383368 else
  if aa=12 then 49861363697 else
  if aa=13 then 52201396073 else
  if aa=14 then 54409142129 else
  if aa=15 then 56523121443 else
  if aa=16 then 60507062756 else
  if aa=17 then 62914336832 else
  if aa=18 then 65076832654 else
  if aa=19 then 66972363437 else
  if aa=20 then 68468159129 else
  if aa=21 then 69507755141 else
  if aa=22 then 70215136394 else
  if aa=23 then 70600980577 else
  if aa=24 then 70688103641 else
  if aa=25 then 70518146820 else
  if aa=26 then 70101174668 else
  if aa=27 then 69455182975 else
  if aa=28 then 68584960048 else
  if aa=29 then 67488822590 else
  if aa=30 then 66229419578 else
  if aa=31 then 64804573894 else
  if aa=32 then 63123811517 else
  if aa=33 then 61163695116 else
  if aa=34 then 58864175773 else
  if aa=35 then 56150808845 else
  if aa=36 then 52917372295 else
  if aa=37 then 49029824335 else
  if aa=38 then 44373084286 else
  if aa=39 then 38897563701 else
  if aa=40 then 32953296977 else
  if aa=41 then 27609451356 else
  if aa=42 then 22657653778 else
  if aa=43 then 17704747471 else
  if aa=44 then 11949315551 else
  if aa=45 then 9325270887 else
  0

theorem raw_first_cost_upper_46 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 46 ≤ (2162768927616/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 45) :
      rawRow 46 aa ≤ rowGrid_46 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 45 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_46,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 46 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 45,rowGrid_46 aa/10000000000)+(0/10000000000 : ℝ)=(2162768927616/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_46]
  change (∑ aa ∈ Finset.Icc 2 45,rawRow 46 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 46 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_46 : c ≤ coefficient profile 46 := by
  have hf := raw_first_cost_upper_46
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 46-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 46-1-
      (K*C/young 46)*(46 : ℝ)^2-(2162768927616/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 46 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 46-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 46-1-
      ((K*C/young 46)*(46 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 46+
        t 3*tripleHarmonicNeighborCharge K young zeta 46)
  linarith only [hf,hn]

def rowGrid_47 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 24916753616 else
  if aa=4 then 24256075567 else
  if aa=5 then 28344749028 else
  if aa=6 then 32866066503 else
  if aa=7 then 36889770700 else
  if aa=8 then 39792362254 else
  if aa=9 then 42384057677 else
  if aa=10 then 44965668082 else
  if aa=11 then 47560971963 else
  if aa=12 then 50058829097 else
  if aa=13 then 52505364779 else
  if aa=14 then 54756468505 else
  if aa=15 then 56866140095 else
  if aa=16 then 58880931198 else
  if aa=17 then 62841569384 else
  if aa=18 then 65164992085 else
  if aa=19 then 67239501176 else
  if aa=20 then 69044174613 else
  if aa=21 then 70447598282 else
  if aa=22 then 71389630161 else
  if aa=23 then 71999572544 else
  if aa=24 then 72294343265 else
  if aa=25 then 72290195403 else
  if aa=26 then 72032707131 else
  if aa=27 then 71537553163 else
  if aa=28 then 70814034306 else
  if aa=29 then 69870089550 else
  if aa=30 then 68705926600 else
  if aa=31 then 67381541033 else
  if aa=32 then 65895138042 else
  if aa=33 then 64151620805 else
  if aa=34 then 62129708964 else
  if aa=35 then 59766740671 else
  if aa=36 then 56991274049 else
  if aa=37 then 53694459389 else
  if aa=38 then 49732960421 else
  if aa=39 then 44999627190 else
  if aa=40 then 39435421968 else
  if aa=41 then 33413848182 else
  if aa=42 then 27930464089 else
  if aa=43 then 22693262348 else
  if aa=44 then 18197813459 else
  if aa=45 then 11927481026 else
  if aa=46 then 9532309371 else
  0

theorem raw_first_cost_upper_47 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 47 ≤ (2258589767734/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 46) :
      rawRow 47 aa ≤ rowGrid_47 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 46 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_47,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 47 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 46,rowGrid_47 aa/10000000000)+(0/10000000000 : ℝ)=(2258589767734/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_47]
  change (∑ aa ∈ Finset.Icc 2 46,rawRow 47 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 47 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_47 : c ≤ coefficient profile 47 := by
  have hf := raw_first_cost_upper_47
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 47-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 47-1-
      (K*C/young 47)*(47 : ℝ)^2-(2258589767734/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 47 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 47-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 47-1-
      ((K*C/young 47)*(47 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 47+
        t 3*tripleHarmonicNeighborCharge K young zeta 47)
  linarith only [hf,hn]

def rowGrid_48 (aa : ℕ) : ℝ :=
  if aa=2 then 0 else
  if aa=3 then 24410654212 else
  if aa=4 then 23203407746 else
  if aa=5 then 27939156175 else
  if aa=6 then 31524039523 else
  if aa=7 then 35717700576 else
  if aa=8 then 38616859040 else
  if aa=9 then 41092835186 else
  if aa=10 then 43634449637 else
  if aa=11 then 46110990089 else
  if aa=12 then 48569287970 else
  if aa=13 then 50910789811 else
  if aa=14 then 53192035839 else
  if aa=15 then 55272221823 else
  if aa=16 then 57212628734 else
  if aa=17 then 59061604450 else
  if aa=18 then 62863906540 else
  if aa=19 then 65028246326 else
  if aa=20 then 66949219676 else
  if aa=21 then 68611071564 else
  if aa=22 then 69880769857 else
  if aa=23 then 70700734561 else
  if aa=24 then 71205431341 else
  if aa=25 then 71404733774 else
  if aa=26 then 71317787956 else
  if aa=27 then 70995061981 else
  if aa=28 then 70443086834 else
  if aa=29 then 69674099853 else
  if aa=30 then 68697869575 else
  if aa=31 then 67510886519 else
  if aa=32 then 66172611075 else
  if aa=33 then 64678123430 else
  if aa=34 then 62936539140 else
  if aa=35 then 60925267431 else
  if aa=36 then 58587037954 else
  if aa=37 then 55850773115 else
  if aa=38 then 52602098300 else
  if aa=39 then 48710572140 else
  if aa=40 then 44061839786 else
  if aa=41 then 38619241048 else
  if aa=42 then 32646489646 else
  if aa=43 then 27017786736 else
  if aa=44 then 22527657037 else
  if aa=45 then 17543430998 else
  if aa=46 then 11775382592 else
  if aa=47 then 9206355661 else
  0

theorem raw_first_cost_upper_48 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 48 ≤ (2275612773257/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 47) :
      rawRow 48 aa ≤ rowGrid_48 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 47 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_48,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 48 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 47,rowGrid_48 aa/10000000000)+(0/10000000000 : ℝ)=(2275612773257/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_48]
  change (∑ aa ∈ Finset.Icc 2 47,rawRow 48 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 48 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_48 : c ≤ coefficient profile 48 := by
  have hf := raw_first_cost_upper_48
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 48-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 48-1-
      (K*C/young 48)*(48 : ℝ)^2-(2275612773257/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 48 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 48-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 48-1-
      ((K*C/young 48)*(48 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 48+
        t 3*tripleHarmonicNeighborCharge K young zeta 48)
  linarith only [hf,hn]

def rowGrid_49 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 24241130497 else
  if aa=4 then 23574330351 else
  if aa=5 then 27716867932 else
  if aa=6 then 32224201529 else
  if aa=7 then 35528531580 else
  if aa=8 then 38775206170 else
  if aa=9 then 41356422539 else
  if aa=10 then 43872532988 else
  if aa=11 then 46403691611 else
  if aa=12 then 48833189982 else
  if aa=13 then 51226008423 else
  if aa=14 then 53487512298 else
  if aa=15 then 55682373196 else
  if aa=16 then 57669303587 else
  if aa=17 then 59514406349 else
  if aa=18 then 61271599301 else
  if aa=19 then 65056200195 else
  if aa=20 then 67146396555 else
  if aa=21 then 68994156854 else
  if aa=22 then 70580596380 else
  if aa=23 then 71770522349 else
  if aa=24 then 72511478736 else
  if aa=25 then 72934908305 else
  if aa=26 then 73054185358 else
  if aa=27 then 72894691542 else
  if aa=28 then 72499009289 else
  if aa=29 then 71877016254 else
  if aa=30 then 71043274103 else
  if aa=31 then 70003944415 else
  if aa=32 then 68756027350 else
  if aa=33 then 67356876949 else
  if aa=34 then 65803995986 else
  if aa=35 then 64003041808 else
  if aa=36 then 61935414061 else
  if aa=37 then 59541805151 else
  if aa=38 then 56741709489 else
  if aa=39 then 53429562684 else
  if aa=40 then 49462558190 else
  if aa=41 then 44748605066 else
  if aa=42 then 39130316624 else
  if aa=43 then 32749731192 else
  if aa=44 then 27814322985 else
  if aa=45 then 22522208893 else
  if aa=46 then 17961411286 else
  if aa=47 then 11794085684 else
  if aa=48 then 9547449742 else
  0

theorem raw_first_cost_upper_49 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 49 ≤ (2683505552569/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 48) :
      rawRow 49 aa ≤ rowGrid_49 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 48 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_49,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 49 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 48,rowGrid_49 aa/10000000000)+(0/10000000000 : ℝ)=(2683505552569/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_49]
  change (∑ aa ∈ Finset.Icc 2 48,rawRow 49 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 49 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_49 : c ≤ coefficient profile 49 := by
  have hf := raw_first_cost_upper_49
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 49-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 49-1-
      (K*C/young 49)*(49 : ℝ)^2-(2683505552569/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 49 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 49-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 49-1-
      ((K*C/young 49)*(49 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 49+
        t 3*tripleHarmonicNeighborCharge K young zeta 49)
  linarith only [hf,hn]

def rowGrid_50 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 23410614622 else
  if aa=5 then 28159941337 else
  if aa=6 then 31967820803 else
  if aa=7 then 36317635017 else
  if aa=8 then 38569843934 else
  if aa=9 then 41526003158 else
  if aa=10 then 44153950534 else
  if aa=11 then 46656884822 else
  if aa=12 then 49143171378 else
  if aa=13 then 51504345768 else
  if aa=14 then 53818684912 else
  if aa=15 then 55991683230 else
  if aa=16 then 58097242673 else
  if aa=17 then 59989454138 else
  if aa=18 then 61741344354 else
  if aa=19 then 63408363396 else
  if aa=20 then 67175260959 else
  if aa=21 then 69197356422 else
  if aa=22 then 70974678379 else
  if aa=23 then 72489273949 else
  if aa=24 then 73608665278 else
  if aa=25 then 74272677702 else
  if aa=26 then 74619706968 else
  if aa=27 then 74669482329 else
  if aa=28 then 74438880279 else
  if aa=29 then 73974788773 else
  if aa=30 then 73289480283 else
  if aa=31 then 72393939465 else
  if aa=32 then 71295066100 else
  if aa=33 then 69986527635 else
  if aa=34 then 68529379416 else
  if aa=35 then 66919089670 else
  if aa=36 then 65064218226 else
  if aa=37 then 62944748272 else
  if aa=38 then 60491621189 else
  if aa=39 then 57634292585 else
  if aa=40 then 54254399758 else
  if aa=41 then 50233501206 else
  if aa=42 then 45340794826 else
  if aa=43 then 39254062681 else
  if aa=44 then 33715256173 else
  if aa=45 then 27807596301 else
  if aa=46 then 23058810846 else
  if aa=47 then 17989939778 else
  if aa=48 then 12231054768 else
  if aa=49 then 9547449742 else
  0

theorem raw_first_cost_upper_50 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 50 ≤ (2809319590494/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 49) :
      rawRow 50 aa ≤ rowGrid_50 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 49 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_50,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 50 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 49,rowGrid_50 aa/10000000000)+(0/10000000000 : ℝ)=(2809319590494/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_50]
  change (∑ aa ∈ Finset.Icc 2 49,rawRow 50 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 50 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_50 : c ≤ coefficient profile 50 := by
  have hf := raw_first_cost_upper_50
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 50-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 50-1-
      (K*C/young 50)*(50 : ℝ)^2-(2809319590494/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 50 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 50-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 50-1-
      ((K*C/young 50)*(50 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 50+
        t 3*tripleHarmonicNeighborCharge K young zeta 50)
  linarith only [hf,hn]

def rowGrid_51 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 27964380093 else
  if aa=6 then 32478848645 else
  if aa=7 then 36028686301 else
  if aa=8 then 39426496181 else
  if aa=9 then 41306072081 else
  if aa=10 then 44335002322 else
  if aa=11 then 46956162414 else
  if aa=12 then 49411312056 else
  if aa=13 then 51831283021 else
  if aa=14 then 54111109607 else
  if aa=15 then 56338360638 else
  if aa=16 then 58419967067 else
  if aa=17 then 60434610062 else
  if aa=18 then 62234167704 else
  if aa=19 then 63894490172 else
  if aa=20 then 65473749548 else
  if aa=21 then 69227102478 else
  if aa=22 then 71183710921 else
  if aa=23 then 72894012921 else
  if aa=24 then 74345825106 else
  if aa=25 then 75396513319 else
  if aa=26 then 75988378880 else
  if aa=27 then 76269619099 else
  if aa=28 then 76251267931 else
  if aa=29 then 75954147500 else
  if aa=30 then 75428476386 else
  if aa=31 then 74682850221 else
  if aa=32 then 73729141157 else
  if aa=33 then 72571006590 else
  if aa=34 then 71204805264 else
  if aa=35 then 69690656584 else
  if aa=36 then 68028614434 else
  if aa=37 then 66124541182 else
  if aa=38 then 63948848353 else
  if aa=39 then 61443192775 else
  if aa=40 then 58524041609 else
  if aa=41 then 55100030314 else
  if aa=42 then 50898276453 else
  if aa=43 then 45484180954 else
  if aa=44 then 40411347848 else
  if aa=45 then 33707102393 else
  if aa=46 then 28470125032 else
  if aa=47 then 23095435648 else
  if aa=48 then 18656464317 else
  if aa=49 then 12231054768 else
  if aa=50 then 9547449742 else
  0

theorem raw_first_cost_upper_51 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 51 ≤ (2935912693569/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 50) :
      rawRow 51 aa ≤ rowGrid_51 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 50 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_51,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 51 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 50,rowGrid_51 aa/10000000000)+(0/10000000000 : ℝ)=(2935912693569/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_51]
  change (∑ aa ∈ Finset.Icc 2 50,rawRow 51 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 51 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_51 : c ≤ coefficient profile 51 := by
  have hf := raw_first_cost_upper_51
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 51-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 51-1-
      (K*C/young 51)*(51 : ℝ)^2-(2935912693569/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 51 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 51-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 51-1-
      ((K*C/young 51)*(51 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 51+
        t 3*tripleHarmonicNeighborCharge K young zeta 51)
  linarith only [hf,hn]

def rowGrid_52 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 32253294055 else
  if aa=7 then 36604629902 else
  if aa=8 then 39112812886 else
  if aa=9 then 42223497091 else
  if aa=10 then 44100194152 else
  if aa=11 then 47148704578 else
  if aa=12 then 49728257745 else
  if aa=13 then 52114090886 else
  if aa=14 then 54454593973 else
  if aa=15 then 56644476032 else
  if aa=16 then 58781679406 else
  if aa=17 then 60770318299 else
  if aa=18 then 62695980682 else
  if aa=19 then 64404500069 else
  if aa=20 then 65975710821 else
  if aa=21 then 67473619080 else
  if aa=22 then 71214310856 else
  if aa=23 then 73108698230 else
  if aa=24 then 74760930006 else
  if aa=25 then 76151577694 else
  if aa=26 then 77138175135 else
  if aa=27 then 77668553638 else
  if aa=28 then 77885301727 else
  if aa=29 then 77803427857 else
  if aa=30 then 77446731734 else
  if aa=31 then 76862512636 else
  if aa=32 then 76060267568 else
  if aa=33 then 75048643356 else
  if aa=34 then 73834273060 else
  if aa=35 then 72411419352 else
  if aa=36 then 70846134187 else
  if aa=37 then 69137246852 else
  if aa=38 then 67179365595 else
  if aa=39 then 64954804316 else
  if aa=40 then 62391742993 else
  if aa=41 then 59436220493 else
  if aa=42 then 55829207764 else
  if aa=43 then 51059237610 else
  if aa=44 then 46825141975 else
  if aa=45 then 40401574668 else
  if aa=46 then 34510189562 else
  if aa=47 then 28515344739 else
  if aa=48 then 23951118034 else
  if aa=49 then 18656464317 else
  if aa=50 then 12231054768 else
  if aa=51 then 9547449742 else
  0

theorem raw_first_cost_upper_52 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 52 ≤ (3068656813374/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 51) :
      rawRow 52 aa ≤ rowGrid_52 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 51 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_52,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 52 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 51,rowGrid_52 aa/10000000000)+(0/10000000000 : ℝ)=(3068656813374/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_52]
  change (∑ aa ∈ Finset.Icc 2 51,rawRow 52 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 52 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_52 : c ≤ coefficient profile 52 := by
  have hf := raw_first_cost_upper_52
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 52-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 52-1-
      (K*C/young 52)*(52 : ℝ)^2-(3068656813374/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 52 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 52-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 52-1-
      ((K*C/young 52)*(52 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 52+
        t 3*tripleHarmonicNeighborCharge K young zeta 52)
  linarith only [hf,hn]

def rowGrid_53 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 36350423160 else
  if aa=8 then 39738058394 else
  if aa=9 then 41887560424 else
  if aa=10 then 45079677774 else
  if aa=11 then 46898994406 else
  if aa=12 then 49932166792 else
  if aa=13 then 52448373377 else
  if aa=14 then 54751715452 else
  if aa=15 then 57004041601 else
  if aa=16 then 59101070613 else
  if aa=17 then 61146583044 else
  if aa=18 then 63044250607 else
  if aa=19 then 64882418150 else
  if aa=20 then 66502333154 else
  if aa=21 then 67990912559 else
  if aa=22 then 69410492593 else
  if aa=23 then 73140125666 else
  if aa=24 then 74981113705 else
  if aa=25 then 76576764891 else
  if aa=26 then 77910681520 else
  if aa=27 then 78843772973 else
  if aa=28 then 79313871057 else
  if aa=29 then 79470723811 else
  if aa=30 then 79332352525 else
  if aa=31 then 78919138788 else
  if aa=32 then 78280130709 else
  if aa=33 then 77421489043 else
  if aa=34 then 76355038834 else
  if aa=35 then 75085445277 else
  if aa=36 then 73612007455 else
  if aa=37 then 72000682485 else
  if aa=38 then 70240130208 else
  if aa=39 then 68236139644 else
  if aa=40 then 65957566233 else
  if aa=41 then 63364205402 else
  if aa=42 then 60222781797 else
  if aa=43 then 56005762541 else
  if aa=44 then 52564562009 else
  if aa=45 then 46813817667 else
  if aa=46 then 41364160709 else
  if aa=47 then 34565002832 else
  if aa=48 then 29571833935 else
  if aa=49 then 23951118034 else
  if aa=50 then 18656464317 else
  if aa=51 then 12231054768 else
  if aa=52 then 9547449742 else
  0

theorem raw_first_cost_upper_53 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 53 ≤ (3207200404096/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 52) :
      rawRow 53 aa ≤ rowGrid_53 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 52 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_53,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 53 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 52,rowGrid_53 aa/10000000000)+(0/10000000000 : ℝ)=(3207200404096/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_53]
  change (∑ aa ∈ Finset.Icc 2 52,rawRow 53 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 53 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_53 : c ≤ coefficient profile 53 := by
  have hf := raw_first_cost_upper_53
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 53-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 53-1-
      (K*C/young 53)*(53 : ℝ)^2-(3207200404096/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 53 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 53-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 53-1-
      ((K*C/young 53)*(53 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 53+
        t 3*tripleHarmonicNeighborCharge K young zeta 53)
  linarith only [hf,hn]

def rowGrid_54 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 39462091055 else
  if aa=9 then 42557162201 else
  if aa=10 then 44721016892 else
  if aa=11 then 47940640543 else
  if aa=12 then 49667714777 else
  if aa=13 then 52663436166 else
  if aa=14 then 55102916815 else
  if aa=15 then 57315073672 else
  if aa=16 then 59476230056 else
  if aa=17 then 61478823992 else
  if aa=18 then 63434594603 else
  if aa=19 then 65242833517 else
  if aa=20 then 66995818351 else
  if aa=21 then 68533620362 else
  if aa=22 then 69942635314 else
  if aa=23 then 71287527601 else
  if aa=24 then 75013346041 else
  if aa=25 then 76802296534 else
  if aa=26 then 78345690555 else
  if aa=27 then 79633360204 else
  if aa=28 then 80513986039 else
  if aa=29 then 80928372895 else
  if aa=30 then 81032412715 else
  if aa=31 then 80840608753 else
  if aa=32 then 80374688361 else
  if aa=33 then 79681080225 else
  if aa=34 then 78769189397 else
  if aa=35 then 77648927150 else
  if aa=36 then 76330368981 else
  if aa=37 then 74811629975 else
  if aa=38 then 73149243614 else
  if aa=39 then 71345052026 else
  if aa=40 then 69289558294 else
  if aa=41 then 66985606976 else
  if aa=42 then 64202748493 else
  if aa=43 then 60413230851 else
  if aa=44 then 57656919997 else
  if aa=45 then 52551849667 else
  if aa=46 then 47929178337 else
  if aa=47 then 41429860288 else
  if aa=48 then 35845630942 else
  if aa=49 then 29571833935 else
  if aa=50 then 23951118034 else
  if aa=51 then 18656464317 else
  if aa=52 then 12231054768 else
  if aa=53 then 9547449742 else
  0

theorem raw_first_cost_upper_54 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 54 ≤ (3351274851055/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 53) :
      rawRow 54 aa ≤ rowGrid_54 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 53 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_54,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 54 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 53,rowGrid_54 aa/10000000000)+(0/10000000000 : ℝ)=(3351274851055/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_54]
  change (∑ aa ∈ Finset.Icc 2 53,rawRow 54 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 54 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_54 : c ≤ coefficient profile 54 := by
  have hf := raw_first_cost_upper_54
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 54-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 54-1-
      (K*C/young 54)*(54 : ℝ)^2-(3351274851055/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 54 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 54-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 54-1-
      ((K*C/young 54)*(54 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 54+
        t 3*tripleHarmonicNeighborCharge K young zeta 54)
  linarith only [hf,hn]

def rowGrid_55 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 42261617141 else
  if aa=10 then 45435913441 else
  if aa=11 then 47559217400 else
  if aa=12 then 50770855343 else
  if aa=13 then 52384518732 else
  if aa=14 then 55328864471 else
  if aa=15 then 57682717533 else
  if aa=16 then 59800751169 else
  if aa=17 then 61869076844 else
  if aa=18 then 63779267499 else
  if aa=19 then 65646790232 else
  if aa=20 then 67367973446 else
  if aa=21 then 69042178867 else
  if aa=22 then 70500921891 else
  if aa=23 then 71834060805 else
  if aa=24 then 73113300363 else
  if aa=25 then 76835311746 else
  if aa=26 then 78576431986 else
  if aa=27 then 80077987699 else
  if aa=28 then 81320299750 else
  if aa=29 then 82152917245 else
  if aa=30 then 82518706239 else
  if aa=31 then 82572990264 else
  if aa=32 then 82331597065 else
  if aa=33 then 81813123373 else
  if aa=34 then 81068113997 else
  if aa=35 then 80103987144 else
  if aa=36 then 78936353623 else
  if aa=37 then 77574291443 else
  if aa=38 then 76005031581 else
  if aa=39 then 74299927633 else
  if aa=40 then 72446465569 else
  if aa=41 then 70369532783 else
  if aa=42 then 67872074620 else
  if aa=43 then 64405783828 else
  if aa=44 then 62194328938 else
  if aa=45 then 57642976106 else
  if aa=46 then 53803921580 else
  if aa=47 then 48005305274 else
  if aa=48 then 42964830325 else
  if aa=49 then 35845630942 else
  if aa=50 then 29571833935 else
  if aa=51 then 23951118034 else
  if aa=52 then 18656464317 else
  if aa=53 then 12231054768 else
  if aa=54 then 9547449742 else
  0

theorem raw_first_cost_upper_55 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 55 ≤ (3499807357804/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 54) :
      rawRow 55 aa ≤ rowGrid_55 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 54 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_55,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 55 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 54,rowGrid_55 aa/10000000000)+(0/10000000000 : ℝ)=(3499807357804/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_55]
  change (∑ aa ∈ Finset.Icc 2 54,rawRow 55 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 55 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_55 : c ≤ coefficient profile 55 := by
  have hf := raw_first_cost_upper_55
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 55-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 55-1-
      (K*C/young 55)*(55 : ℝ)^2-(3499807357804/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 55 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 55-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 55-1-
      ((K*C/young 55)*(55 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 55+
        t 3*tripleHarmonicNeighborCharge K young zeta 55)
  linarith only [hf,hn]

def rowGrid_56 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 45120376430 else
  if aa=11 then 48319484557 else
  if aa=12 then 50366914574 else
  if aa=13 then 53548000642 else
  if aa=14 then 55035830328 else
  if aa=15 then 57919243574 else
  if aa=16 then 60184339248 else
  if aa=17 then 62206654086 else
  if aa=18 then 64184123016 else
  if aa=19 then 66003483129 else
  if aa=20 then 67785088150 else
  if aa=21 then 69425701291 else
  if aa=22 then 71024078895 else
  if aa=23 then 72407444861 else
  if aa=24 then 73673831042 else
  if aa=25 then 74889116706 else
  if aa=26 then 78610209851 else
  if aa=27 then 80313831040 else
  if aa=28 then 81774346159 else
  if aa=29 then 82975644164 else
  if aa=30 then 83767314261 else
  if aa=31 then 84087541004 else
  if aa=32 then 84095929852 else
  if aa=33 then 83805054123 else
  if aa=34 then 83237270295 else
  if aa=35 then 82441868592 else
  if aa=36 then 81432118741 else
  if aa=37 then 80222744670 else
  if aa=38 then 78811763265 else
  if aa=39 then 77200638957 else
  if aa=40 then 75446958075 else
  if aa=41 then 73575644866 else
  if aa=42 then 71300782297 else
  if aa=43 then 68086713865 else
  if aa=44 then 66304590046 else
  if aa=45 then 62179287709 else
  if aa=46 then 59016346440 else
  if aa=47 then 53889379497 else
  if aa=48 then 49783894550 else
  if aa=49 then 42964830325 else
  if aa=50 then 35845630942 else
  if aa=51 then 29571833935 else
  if aa=52 then 23951118034 else
  if aa=53 then 18656464317 else
  if aa=54 then 12231054768 else
  if aa=55 then 9547449742 else
  0

theorem raw_first_cost_upper_56 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 56 ≤ (3652377587651/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 55) :
      rawRow 56 aa ≤ rowGrid_56 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 55 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_56,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 56 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 55,rowGrid_56 aa/10000000000)+(0/10000000000 : ℝ)=(3652377587651/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_56]
  change (∑ aa ∈ Finset.Icc 2 55,rawRow 56 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 56 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_56 : c ≤ coefficient profile 56 := by
  have hf := raw_first_cost_upper_56
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 56-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 56-1-
      (K*C/young 56)*(56 : ℝ)^2-(3652377587651/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 56 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 56-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 56-1-
      ((K*C/young 56)*(56 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 56+
        t 3*tripleHarmonicNeighborCharge K young zeta 56)
  linarith only [hf,hn]

def rowGrid_57 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 47983922123 else
  if aa=12 then 51172064722 else
  if aa=13 then 53121964476 else
  if aa=14 then 56258198969 else
  if aa=15 then 57612490199 else
  if aa=16 then 60431123105 else
  if aa=17 then 62605674675 else
  if aa=18 then 64534331881 else
  if aa=19 then 66422457433 else
  if aa=20 then 68153399524 else
  if aa=21 then 69855556597 else
  if aa=22 then 71418610576 else
  if aa=23 then 72944749352 else
  if aa=24 then 74261900262 else
  if aa=25 then 75463261865 else
  if aa=26 then 76619057645 else
  if aa=27 then 80348355766 else
  if aa=28 then 82015185565 else
  if aa=29 then 83438933076 else
  if aa=30 then 84606208686 else
  if aa=31 then 85359887397 else
  if aa=32 then 85638414294 else
  if aa=33 then 85600962497 else
  if aa=34 then 85263875213 else
  if aa=35 then 84647782726 else
  if aa=36 then 83808762482 else
  if aa=37 then 82759182175 else
  if aa=38 then 81502464848 else
  if aa=39 then 80051522310 else
  if aa=40 then 78392450118 else
  if aa=41 then 76622904235 else
  if aa=42 then 74549323116 else
  if aa=43 then 71526264518 else
  if aa=44 then 70094040971 else
  if aa=45 then 66288554782 else
  if aa=46 then 63660737748 else
  if aa=47 then 59110083363 else
  if aa=48 then 55885972830 else
  if aa=49 then 49783894550 else
  if aa=50 then 42964830325 else
  if aa=51 then 35845630942 else
  if aa=52 then 29571833935 else
  if aa=53 then 23951118034 else
  if aa=54 then 18656464317 else
  if aa=55 then 12231054768 else
  if aa=56 then 9547449742 else
  0

theorem raw_first_cost_upper_57 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 57 ≤ (3808938987033/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 56) :
      rawRow 57 aa ≤ rowGrid_57 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 56 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_57,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 57 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 56,rowGrid_57 aa/10000000000)+(0/10000000000 : ℝ)=(3808938987033/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_57]
  change (∑ aa ∈ Finset.Icc 2 56,rawRow 57 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 57 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_57 : c ≤ coefficient profile 57 := by
  have hf := raw_first_cost_upper_57
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 57-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 57-1-
      (K*C/young 57)*(57 : ℝ)^2-(3808938987033/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 57 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 57-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 57-1-
      ((K*C/young 57)*(57 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 57+
        t 3*tripleHarmonicNeighborCharge K young zeta 57)
  linarith only [hf,hn]

def rowGrid_58 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 50816692086 else
  if aa=13 then 53971156012 else
  if aa=14 then 55810600046 else
  if aa=15 then 58892087526 else
  if aa=16 then 60111066249 else
  if aa=17 then 62862387136 else
  if aa=18 then 64948283210 else
  if aa=19 then 66784879359 else
  if aa=20 then 68586020983 else
  if aa=21 then 70235117894 else
  if aa=22 then 71860805154 else
  if aa=23 then 73349950165 else
  if aa=24 then 74812965867 else
  if aa=25 then 76065614436 else
  if aa=26 then 77206465574 else
  if aa=27 then 78313177305 else
  if aa=28 then 82050441657 else
  if aa=29 then 83684674975 else
  if aa=30 then 85078601746 else
  if aa=31 then 86214730773 else
  if aa=32 then 86934227279 else
  if aa=33 then 87171052193 else
  if aa=34 then 87091045533 else
  if aa=35 then 86708729850 else
  if aa=36 then 86051250879 else
  if aa=37 then 85174557035 else
  if aa=38 then 84079363824 else
  if aa=39 then 82784550337 else
  if aa=40 then 81287344954 else
  if aa=41 then 79614305884 else
  if aa=42 then 77636909011 else
  if aa=43 then 74785078550 else
  if aa=44 then 73634996184 else
  if aa=45 then 70077089256 else
  if aa=46 then 67867909992 else
  if aa=47 then 63761851456 else
  if aa=48 then 61300102982 else
  if aa=49 then 55885972830 else
  if aa=50 then 49783894550 else
  if aa=51 then 42964830325 else
  if aa=52 then 35845630942 else
  if aa=53 then 29571833935 else
  if aa=54 then 23951118034 else
  if aa=55 then 18656464317 else
  if aa=56 then 12231054768 else
  if aa=57 then 9547449742 else
  0

theorem raw_first_cost_upper_58 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 58 ≤ (3969398865168/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 57) :
      rawRow 58 aa ≤ rowGrid_58 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 57 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_58,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 58 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 57,rowGrid_58 aa/10000000000)+(0/10000000000 : ℝ)=(3969398865168/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_58]
  change (∑ aa ∈ Finset.Icc 2 57,rawRow 58 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 58 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_58 : c ≤ coefficient profile 58 := by
  have hf := raw_first_cost_upper_58
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 58-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 58-1-
      (K*C/young 58)*(58 : ℝ)^2-(3969398865168/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 58 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 58-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 58-1-
      ((K*C/young 58)*(58 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 58+
        t 3*tripleHarmonicNeighborCharge K young zeta 58)
  linarith only [hf,hn]

def rowGrid_59 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 53596344636 else
  if aa=14 then 56702771291 else
  if aa=15 then 58423532978 else
  if aa=16 then 61446157988 else
  if aa=17 then 62529453758 else
  if aa=18 then 65214601459 else
  if aa=19 then 67213266680 else
  if aa=20 then 68960247995 else
  if aa=21 then 70680953603 else
  if aa=22 then 72251262002 else
  if aa=23 then 73804102802 else
  if aa=24 then 75228544438 else
  if aa=25 then 76630064628 else
  if aa=26 then 77822732509 else
  if aa=27 then 78913573379 else
  if aa=28 then 79972150322 else
  if aa=29 then 83720648735 else
  if aa=30 then 85329172749 else
  if aa=31 then 86696104907 else
  if aa=32 then 87804837007 else
  if aa=33 then 88490055846 else
  if aa=34 then 88688466277 else
  if aa=35 then 88566862820 else
  if aa=36 then 88146368698 else
  if aa=37 then 87453590278 else
  if aa=38 then 86533268952 else
  if aa=39 then 85401985569 else
  if aa=40 then 84062565032 else
  if aa=41 then 82554321697 else
  if aa=42 then 80667897981 else
  if aa=43 then 77882428654 else
  if aa=44 then 76989886313 else
  if aa=45 then 73617188116 else
  if aa=46 then 71746708038 else
  if aa=47 then 67975706042 else
  if aa=48 then 66124218377 else
  if aa=49 then 61300102982 else
  if aa=50 then 55885972830 else
  if aa=51 then 49783894550 else
  if aa=52 then 42964830325 else
  if aa=53 then 35845630942 else
  if aa=54 then 29571833935 else
  if aa=55 then 23951118034 else
  if aa=56 then 18656464317 else
  if aa=57 then 12231054768 else
  if aa=58 then 9547449742 else
  0

theorem raw_first_cost_upper_59 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 59 ≤ (4133639173887/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 58) :
      rawRow 59 aa ≤ rowGrid_59 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 58 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_59,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 59 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 58,rowGrid_59 aa/10000000000)+(0/10000000000 : ℝ)=(4133639173887/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_59]
  change (∑ aa ∈ Finset.Icc 2 58,rawRow 59 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 59 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_59 : c ≤ coefficient profile 59 := by
  have hf := raw_first_cost_upper_59
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 59-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 59-1-
      (K*C/young 59)*(59 : ℝ)^2-(4133639173887/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 59 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 59-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 59-1-
      ((K*C/young 59)*(59 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 59+
        t 3*tripleHarmonicNeighborCharge K young zeta 59)
  linarith only [hf,hn]

def rowGrid_60 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 56308989774 else
  if aa=15 then 59357473774 else
  if aa=16 then 60957282861 else
  if aa=17 then 63918258887 else
  if aa=18 then 64869210223 else
  if aa=19 then 67488872417 else
  if aa=20 then 69402589078 else
  if aa=21 then 71066611230 else
  if aa=22 then 72709895711 else
  if aa=23 then 74205118589 else
  if aa=24 then 75694328555 else
  if aa=25 then 77055737001 else
  if aa=26 then 78400221518 else
  if aa=27 then 79543466556 else
  if aa=28 then 80585265084 else
  if aa=29 then 81600051998 else
  if aa=30 then 85365853433 else
  if aa=31 then 86951439733 else
  if aa=32 then 88295089392 else
  if aa=33 then 89376246543 else
  if aa=34 then 90030430244 else
  if aa=35 then 90191352949 else
  if aa=36 then 90035309686 else
  if aa=37 then 89582851312 else
  if aa=38 then 88848657532 else
  if aa=39 then 87894492182 else
  if aa=40 then 86720407812 else
  if aa=41 then 85372797454 else
  if aa=42 then 83646821092 else
  if aa=43 then 80923002850 else
  if aa=44 then 80178552248 else
  if aa=45 then 76971266890 else
  if aa=46 then 75371151375 else
  if aa=47 then 71860664865 else
  if aa=48 then 70494195636 else
  if aa=49 then 66124218377 else
  if aa=50 then 61300102982 else
  if aa=51 then 55885972830 else
  if aa=52 then 49783894550 else
  if aa=53 then 42964830325 else
  if aa=54 then 35845630942 else
  if aa=55 then 29571833935 else
  if aa=56 then 23951118034 else
  if aa=57 then 18656464317 else
  if aa=58 then 12231054768 else
  if aa=59 then 9547449742 else
  0

theorem raw_first_cost_upper_60 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 60 ≤ (4301527980562/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 59) :
      rawRow 60 aa ≤ rowGrid_60 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 59 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_60,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 60 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 59,rowGrid_60 aa/10000000000)+(0/10000000000 : ℝ)=(4301527980562/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_60]
  change (∑ aa ∈ Finset.Icc 2 59,rawRow 60 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 60 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_60 : c ≤ coefficient profile 60 := by
  have hf := raw_first_cost_upper_60
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 60-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 60-1-
      (K*C/young 60)*(60 : ℝ)^2-(4301527980562/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 60 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 60-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 60-1-
      ((K*C/young 60)*(60 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 60+
        t 3*tripleHarmonicNeighborCharge K young zeta 60)
  linarith only [hf,hn]

def rowGrid_61 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 58945256247 else
  if aa=16 then 61931727410 else
  if aa=17 then 63409715344 else
  if aa=18 then 66309982315 else
  if aa=19 then 67131436130 else
  if aa=20 then 69687172058 else
  if aa=21 then 71522463445 else
  if aa=22 then 73106623887 else
  if aa=23 then 74676154911 else
  if aa=24 then 76105614914 else
  if aa=25 then 77532834341 else
  if aa=26 then 78835726936 else
  if aa=27 then 80133724393 else
  if aa=28 then 81228501811 else
  if aa=29 then 82225647236 else
  if aa=30 then 83203584591 else
  if aa=31 then 86988817785 else
  if aa=32 then 88555133500 else
  if aa=33 then 89875272787 else
  if aa=34 then 90932047142 else
  if aa=35 then 91556057413 else
  if aa=36 then 91686734015 else
  if aa=37 then 91502575541 else
  if aa=38 then 91011884722 else
  if aa=39 then 90246303293 else
  if aa=40 then 89251393345 else
  if aa=41 then 88072066424 else
  if aa=42 then 86502595720 else
  if aa=43 then 83911346534 else
  if aa=44 then 83308768412 else
  if aa=45 then 80159161670 else
  if aa=46 then 78805142615 else
  if aa=47 then 75490864984 else
  if aa=48 then 74523091594 else
  if aa=49 then 70494195636 else
  if aa=50 then 66124218377 else
  if aa=51 then 61300102982 else
  if aa=52 then 55885972830 else
  if aa=53 then 49783894550 else
  if aa=54 then 42964830325 else
  if aa=55 then 35845630942 else
  if aa=56 then 29571833935 else
  if aa=57 then 23951118034 else
  if aa=58 then 18656464317 else
  if aa=59 then 12231054768 else
  if aa=60 then 9547449742 else
  0

theorem raw_first_cost_upper_61 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 61 ≤ (4472929305322/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 60) :
      rawRow 61 aa ≤ rowGrid_61 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 60 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_61,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 61 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 60,rowGrid_61 aa/10000000000)+(0/10000000000 : ℝ)=(4472929305322/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_61]
  change (∑ aa ∈ Finset.Icc 2 60,rawRow 61 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 61 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_61 : c ≤ coefficient profile 61 := by
  have hf := raw_first_cost_upper_61
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 61-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 61-1-
      (K*C/young 61)*(61 : ℝ)^2-(4472929305322/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 61 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 61-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 61-1-
      ((K*C/young 61)*(61 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 61+
        t 3*tripleHarmonicNeighborCharge K young zeta 61)
  linarith only [hf,hn]

def rowGrid_62 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 61501632565 else
  if aa=17 then 64423363731 else
  if aa=18 then 65782409850 else
  if aa=19 then 68622453198 else
  if aa=20 then 69318093080 else
  if aa=21 then 71815738898 else
  if aa=22 then 73575561632 else
  if aa=23 then 75083611619 else
  if aa=24 then 76588715132 else
  if aa=25 then 77954110251 else
  if aa=26 then 79323845240 else
  if aa=27 then 80578859246 else
  if aa=28 then 81831263569 else
  if aa=29 then 82881977599 else
  if aa=30 then 83841473478 else
  if aa=31 then 84785440173 else
  if aa=32 then 88593200937 else
  if aa=33 then 90139970805 else
  if aa=34 then 91439760094 else
  if aa=35 then 92472952826 else
  if aa=36 then 93074065406 else
  if aa=37 then 93180912405 else
  if aa=38 then 92962232559 else
  if aa=39 then 92443559420 else
  if aa=40 then 91639511341 else
  if aa=41 then 90642500899 else
  if aa=42 then 89237586014 else
  if aa=43 then 86776152289 else
  if aa=44 then 86385214207 else
  if aa=45 then 83288620815 else
  if aa=46 then 82068990450 else
  if aa=47 then 78930310505 else
  if aa=48 then 78287790076 else
  if aa=49 then 74523091594 else
  if aa=50 then 70494195636 else
  if aa=51 then 66124218377 else
  if aa=52 then 61300102982 else
  if aa=53 then 55885972830 else
  if aa=54 then 49783894550 else
  if aa=55 then 42964830325 else
  if aa=56 then 35845630942 else
  if aa=57 then 29571833935 else
  if aa=58 then 23951118034 else
  if aa=59 then 18656464317 else
  if aa=60 then 12231054768 else
  if aa=61 then 9547449742 else
  0

theorem raw_first_cost_upper_62 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 62 ≤ (4647703121788/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 61) :
      rawRow 62 aa ≤ rowGrid_62 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 61 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_62,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 62 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 61,rowGrid_62 aa/10000000000)+(0/10000000000 : ℝ)=(4647703121788/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_62]
  change (∑ aa ∈ Finset.Icc 2 61,rawRow 62 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 62 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_62 : c ≤ coefficient profile 62 := by
  have hf := raw_first_cost_upper_62
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 62-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 62-1-
      (K*C/young 62)*(62 : ℝ)^2-(4647703121788/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 62 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 62-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 62-1-
      ((K*C/young 62)*(62 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 62+
        t 3*tripleHarmonicNeighborCharge K young zeta 62)
  linarith only [hf,hn]

def rowGrid_63 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 63975965317 else
  if aa=18 then 66833987409 else
  if aa=19 then 68076482357 else
  if aa=20 then 70857676707 else
  if aa=21 then 71435386551 else
  if aa=22 then 73877255746 else
  if aa=23 then 75565230625 else
  if aa=24 then 77006607373 else
  if aa=25 then 78448944275 else
  if aa=26 then 79754852636 else
  if aa=27 then 81077770306 else
  if aa=28 then 82285828084 else
  if aa=29 then 83497009089 else
  if aa=30 then 84510701469 else
  if aa=31 then 85435456519 else
  if aa=32 then 86349185206 else
  if aa=33 then 90178719520 else
  if aa=34 then 91709065795 else
  if aa=35 then 92989269321 else
  if aa=36 then 94006163031 else
  if aa=37 then 94590852526 else
  if aa=38 then 94667342398 else
  if aa=39 then 94424587465 else
  if aa=40 then 93870688358 else
  if aa=41 then 93067841048 else
  if aa=42 then 91842036857 else
  if aa=43 then 89519791740 else
  if aa=44 then 89334479938 else
  if aa=45 then 86364322595 else
  if aa=46 then 85273010393 else
  if aa=47 then 82199342379 else
  if aa=48 then 81854666531 else
  if aa=49 then 78287790076 else
  if aa=50 then 74523091594 else
  if aa=51 then 70494195636 else
  if aa=52 then 66124218377 else
  if aa=53 then 61300102982 else
  if aa=54 then 55885972830 else
  if aa=55 then 49783894550 else
  if aa=56 then 42964830325 else
  if aa=57 then 35845630942 else
  if aa=58 then 29571833935 else
  if aa=59 then 23951118034 else
  if aa=60 then 18656464317 else
  if aa=61 then 12231054768 else
  if aa=62 then 9547449742 else
  0

theorem raw_first_cost_upper_63 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 63 ≤ (4825710945470/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 62) :
      rawRow 63 aa ≤ rowGrid_63 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 62 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_63,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 63 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 62,rowGrid_63 aa/10000000000)+(0/10000000000 : ℝ)=(4825710945470/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_63]
  change (∑ aa ∈ Finset.Icc 2 62,rawRow 63 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 63 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_63 : c ≤ coefficient profile 63 := by
  have hf := raw_first_cost_upper_63
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 63-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 63-1-
      (K*C/young 63)*(63 : ℝ)^2-(4825710945470/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 63 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 63-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 63-1-
      ((K*C/young 63)*(63 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 63+
        t 3*tripleHarmonicNeighborCharge K young zeta 63)
  linarith only [hf,hn]

def rowGrid_64 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 66369848030 else
  if aa=19 then 69164732260 else
  if aa=20 then 70293922083 else
  if aa=21 then 73021996144 else
  if aa=22 then 73485985140 else
  if aa=23 then 75875083310 else
  if aa=24 then 77500561312 else
  if aa=25 then 78876986515 else
  if aa=26 then 80261117342 else
  if aa=27 then 81518307683 else
  if aa=28 then 82795307991 else
  if aa=29 then 83960826654 else
  if aa=30 then 85137819018 else
  if aa=31 then 86117407784 else
  if aa=32 then 87011190165 else
  if aa=33 then 87894543499 else
  if aa=34 then 91748489021 else
  if aa=35 then 93263138590 else
  if aa=36 then 94531040101 else
  if aa=37 then 95538140136 else
  if aa=38 then 96099774006 else
  if aa=39 then 96156519764 else
  if aa=40 then 95882299198 else
  if aa=41 then 95333794073 else
  if aa=42 then 94299473238 else
  if aa=43 then 92132478921 else
  if aa=44 then 92159007151 else
  if aa=45 then 89312875068 else
  if aa=46 then 88421992178 else
  if aa=47 then 85408451335 else
  if aa=48 then 85244815540 else
  if aa=49 then 81854666531 else
  if aa=50 then 78287790076 else
  if aa=51 then 74523091594 else
  if aa=52 then 70494195636 else
  if aa=53 then 66124218377 else
  if aa=54 then 61300102982 else
  if aa=55 then 55885972830 else
  if aa=56 then 49783894550 else
  if aa=57 then 42964830325 else
  if aa=58 then 35845630942 else
  if aa=59 then 29571833935 else
  if aa=60 then 23951118034 else
  if aa=61 then 18656464317 else
  if aa=62 then 12231054768 else
  if aa=63 then 9547449742 else
  0

theorem raw_first_cost_upper_64 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 64 ≤ (5006815704176/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 63) :
      rawRow 64 aa ≤ rowGrid_64 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 63 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_64,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 64 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 63,rowGrid_64 aa/10000000000)+(0/10000000000 : ℝ)=(5006815704176/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_64]
  change (∑ aa ∈ Finset.Icc 2 63,rawRow 64 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 64 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_64 : c ≤ coefficient profile 64 := by
  have hf := raw_first_cost_upper_64
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 64-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 64-1-
      (K*C/young 64)*(64 : ℝ)^2-(5006815704176/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 64 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 64-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 64-1-
      ((K*C/young 64)*(64 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 64+
        t 3*tripleHarmonicNeighborCharge K young zeta 64)
  linarith only [hf,hn]

def rowGrid_65 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 68684406649 else
  if aa=20 then 71417619302 else
  if aa=21 then 72441021861 else
  if aa=22 then 75118139380 else
  if aa=23 then 75473231759 else
  if aa=24 then 77818349755 else
  if aa=25 then 79382937880 else
  if aa=26 then 80699047370 else
  if aa=27 then 82035766379 else
  if aa=28 then 83245177636 else
  if aa=29 then 84480677462 else
  if aa=30 then 85610751118 else
  if aa=31 then 86756448010 else
  if aa=32 then 87705719036 else
  if aa=33 then 88568396107 else
  if aa=34 then 89424551625 else
  if aa=35 then 93303229870 else
  if aa=36 then 94809450149 else
  if aa=37 then 96071570897 else
  if aa=38 then 97062172830 else
  if aa=39 then 97611484431 else
  if aa=40 then 97640968792 else
  if aa=41 then 97376758677 else
  if aa=42 then 96595413213 else
  if aa=43 then 94597686721 else
  if aa=44 then 94848721368 else
  if aa=45 then 92136719190 else
  if aa=46 then 91440795266 else
  if aa=47 then 88562434715 else
  if aa=48 then 88572821497 else
  if aa=49 then 85244815540 else
  if aa=50 then 81854666531 else
  if aa=51 then 78287790076 else
  if aa=52 then 74523091594 else
  if aa=53 then 70494195636 else
  if aa=54 then 66124218377 else
  if aa=55 then 61300102982 else
  if aa=56 then 55885972830 else
  if aa=57 then 49783894550 else
  if aa=58 then 42964830325 else
  if aa=59 then 35845630942 else
  if aa=60 then 29571833935 else
  if aa=61 then 23951118034 else
  if aa=62 then 18656464317 else
  if aa=63 then 12231054768 else
  if aa=64 then 9547449742 else
  0

theorem raw_first_cost_upper_65 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 65 ≤ (5190886436804/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 64) :
      rawRow 65 aa ≤ rowGrid_65 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 64 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_65,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 65 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 64,rowGrid_65 aa/10000000000)+(0/10000000000 : ℝ)=(5190886436804/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_65]
  change (∑ aa ∈ Finset.Icc 2 64,rawRow 65 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 65 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_65 : c ≤ coefficient profile 65 := by
  have hf := raw_first_cost_upper_65
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 65-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 65-1-
      (K*C/young 65)*(65 : ℝ)^2-(5190886436804/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 65 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 65-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 65-1-
      ((K*C/young 65)*(65 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 65+
        t 3*tripleHarmonicNeighborCharge K young zeta 65)
  linarith only [hf,hn]

def rowGrid_66 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 70921648154 else
  if aa=21 then 73599041962 else
  if aa=22 then 74520487856 else
  if aa=23 then 77149523571 else
  if aa=24 then 77406206227 else
  if aa=25 then 79708444945 else
  if aa=26 then 81216686228 else
  if aa=27 then 82483379454 else
  if aa=28 then 83773598089 else
  if aa=29 then 84939704590 else
  if aa=30 then 86140817577 else
  if aa=31 then 87238371433 else
  if aa=32 then 88356545436 else
  if aa=33 then 89275354696 else
  if aa=34 then 90110134198 else
  if aa=35 then 90939911767 else
  if aa=36 then 94850206145 else
  if aa=37 then 96354518071 else
  if aa=38 then 97604112925 else
  if aa=39 then 98589022399 else
  if aa=40 then 99118394971 else
  if aa=41 then 99162839592 else
  if aa=42 then 98665413804 else
  if aa=43 then 96900887396 else
  if aa=44 then 97386608229 else
  if aa=45 then 94825782921 else
  if aa=46 then 94331918769 else
  if aa=47 then 91586032633 else
  if aa=48 then 91843659482 else
  if aa=49 then 88572821497 else
  if aa=50 then 85244815540 else
  if aa=51 then 81854666531 else
  if aa=52 then 78287790076 else
  if aa=53 then 74523091594 else
  if aa=54 then 70494195636 else
  if aa=55 then 66124218377 else
  if aa=56 then 61300102982 else
  if aa=57 then 55885972830 else
  if aa=58 then 49783894550 else
  if aa=59 then 42964830325 else
  if aa=60 then 35845630942 else
  if aa=61 then 29571833935 else
  if aa=62 then 23951118034 else
  if aa=63 then 18656464317 else
  if aa=64 then 12231054768 else
  if aa=65 then 9547449742 else
  0

theorem raw_first_cost_upper_66 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 66 ≤ (5377795761774/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 65) :
      rawRow 66 aa ≤ rowGrid_66 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 65 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_66,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 66 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 65,rowGrid_66 aa/10000000000)+(0/10000000000 : ℝ)=(5377795761774/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_66]
  change (∑ aa ∈ Finset.Icc 2 65,rawRow 66 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 66 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_66 : c ≤ coefficient profile 66 := by
  have hf := raw_first_cost_upper_66
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 66-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 66-1-
      (K*C/young 66)*(66 : ℝ)^2-(5377795761774/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 66 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 66-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 66-1-
      ((K*C/young 66)*(66 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 66+
        t 3*tripleHarmonicNeighborCharge K young zeta 66)
  linarith only [hf,hn]

def rowGrid_67 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 73087921574 else
  if aa=22 then 75711749667 else
  if aa=23 then 76535710041 else
  if aa=24 then 79125430204 else
  if aa=25 then 79286291046 else
  if aa=26 then 81549712516 else
  if aa=27 then 83012463795 else
  if aa=28 then 84230693323 else
  if aa=29 then 85478881493 else
  if aa=30 then 86608865104 else
  if aa=31 then 87778515446 else
  if aa=32 then 88847357241 else
  if aa=33 then 89937828687 else
  if aa=34 then 90829399039 else
  if aa=35 then 91637112006 else
  if aa=36 then 92447704007 else
  if aa=37 then 96395938251 else
  if aa=38 then 97891573697 else
  if aa=39 then 99139487555 else
  if aa=40 then 100111024015 else
  if aa=41 then 100663293520 else
  if aa=42 then 100475131183 else
  if aa=43 then 98977434175 else
  if aa=44 then 99757711684 else
  if aa=45 then 97363056013 else
  if aa=46 then 97085050676 else
  if aa=47 then 94481748169 else
  if aa=48 then 94979281244 else
  if aa=49 then 91843659482 else
  if aa=50 then 88572821497 else
  if aa=51 then 85244815540 else
  if aa=52 then 81854666531 else
  if aa=53 then 78287790076 else
  if aa=54 then 74523091594 else
  if aa=55 then 70494195636 else
  if aa=56 then 66124218377 else
  if aa=57 then 61300102982 else
  if aa=58 then 55885972830 else
  if aa=59 then 49783894550 else
  if aa=60 then 42964830325 else
  if aa=61 then 35845630942 else
  if aa=62 then 29571833935 else
  if aa=63 then 23951118034 else
  if aa=64 then 18656464317 else
  if aa=65 then 12231054768 else
  if aa=66 then 9547449742 else
  0

theorem raw_first_cost_upper_67 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 67 ≤ (5567418320760/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 66) :
      rawRow 67 aa ≤ rowGrid_67 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 66 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_67,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 67 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 66,rowGrid_67 aa/10000000000)+(0/10000000000 : ℝ)=(5567418320760/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_67]
  change (∑ aa ∈ Finset.Icc 2 66,rawRow 67 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 67 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_67 : c ≤ coefficient profile 67 := by
  have hf := raw_first_cost_upper_67
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 67-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 67-1-
      (K*C/young 67)*(67 : ℝ)^2-(5567418320760/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 67 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 67-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 67-1-
      ((K*C/young 67)*(67 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 67+
        t 3*tripleHarmonicNeighborCharge K young zeta 67)
  linarith only [hf,hn]

def rowGrid_68 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 75185957241 else
  if aa=23 then 77759186580 else
  if aa=24 then 78495896056 else
  if aa=25 then 81047272488 else
  if aa=26 then 81117806849 else
  if aa=27 then 83352853609 else
  if aa=28 then 84770985697 else
  if aa=29 then 85945281292 else
  if aa=30 then 87158637438 else
  if aa=31 then 88255461430 else
  if aa=32 then 89397463430 else
  if aa=33 then 90437424363 else
  if aa=34 then 91503404924 else
  if aa=35 then 92368565281 else
  if aa=36 then 93156463891 else
  if aa=37 then 93954283591 else
  if aa=38 then 97933654614 else
  if aa=39 then 99431470267 else
  if aa=40 then 100669987165 else
  if aa=41 then 101671394073 else
  if aa=42 then 101995441674 else
  if aa=43 then 100792874621 else
  if aa=44 then 101895479051 else
  if aa=45 then 99733586034 else
  if aa=46 then 99682775462 else
  if aa=47 then 97239252934 else
  if aa=48 then 97982282601 else
  if aa=49 then 94979281244 else
  if aa=50 then 91843659482 else
  if aa=51 then 88572821497 else
  if aa=52 then 85244815540 else
  if aa=53 then 81854666531 else
  if aa=54 then 78287790076 else
  if aa=55 then 74523091594 else
  if aa=56 then 70494195636 else
  if aa=57 then 66124218377 else
  if aa=58 then 61300102982 else
  if aa=59 then 55885972830 else
  if aa=60 then 49783894550 else
  if aa=61 then 42964830325 else
  if aa=62 then 35845630942 else
  if aa=63 then 29571833935 else
  if aa=64 then 23951118034 else
  if aa=65 then 18656464317 else
  if aa=66 then 12231054768 else
  if aa=67 then 9547449742 else
  0

theorem raw_first_cost_upper_68 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 68 ≤ (5759636790046/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 67) :
      rawRow 68 aa ≤ rowGrid_68 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 67 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_68,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 68 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 67,rowGrid_68 aa/10000000000)+(0/10000000000 : ℝ)=(5759636790046/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_68]
  change (∑ aa ∈ Finset.Icc 2 67,rawRow 68 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 68 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_68 : c ≤ coefficient profile 68 := by
  have hf := raw_first_cost_upper_68
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 68-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 68-1-
      (K*C/young 68)*(68 : ℝ)^2-(5759636790046/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 68 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 68-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 68-1-
      ((K*C/young 68)*(68 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 68+
        t 3*tripleHarmonicNeighborCharge K young zeta 68)
  linarith only [hf,hn]

def rowGrid_69 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 77219175398 else
  if aa=24 then 79750707531 else
  if aa=25 then 80402447866 else
  if aa=26 then 82919467018 else
  if aa=27 then 82911398100 else
  if aa=28 then 85118586271 else
  if aa=29 then 86496571781 else
  if aa=30 then 87634202517 else
  if aa=31 then 88815685964 else
  if aa=32 then 89883205994 else
  if aa=33 then 90997375591 else
  if aa=34 then 92011697220 else
  if aa=35 then 93053992656 else
  if aa=36 then 93900044730 else
  if aa=37 then 94674593824 else
  if aa=38 then 95453050468 else
  if aa=39 then 99474213144 else
  if aa=40 then 100966477459 else
  if aa=41 then 102239069443 else
  if aa=42 then 103016883130 else
  if aa=43 then 102317992954 else
  if aa=44 then 103764442168 else
  if aa=45 then 101870836398 else
  if aa=46 then 102109784449 else
  if aa=47 then 99841103742 else
  if aa=48 then 100841952499 else
  if aa=49 then 97982282601 else
  if aa=50 then 94979281244 else
  if aa=51 then 91843659482 else
  if aa=52 then 88572821497 else
  if aa=53 then 85244815540 else
  if aa=54 then 81854666531 else
  if aa=55 then 78287790076 else
  if aa=56 then 74523091594 else
  if aa=57 then 70494195636 else
  if aa=58 then 66124218377 else
  if aa=59 then 61300102982 else
  if aa=60 then 55885972830 else
  if aa=61 then 49783894550 else
  if aa=62 then 42964830325 else
  if aa=63 then 35845630942 else
  if aa=64 then 29571833935 else
  if aa=65 then 23951118034 else
  if aa=66 then 18656464317 else
  if aa=67 then 12231054768 else
  if aa=68 then 9547449742 else
  0

theorem raw_first_cost_upper_69 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 69 ≤ (5954339995258/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 68) :
      rawRow 69 aa ≤ rowGrid_69 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 68 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_69,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 69 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 68,rowGrid_69 aa/10000000000)+(0/10000000000 : ℝ)=(5954339995258/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_69]
  change (∑ aa ∈ Finset.Icc 2 68,rawRow 69 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 69 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_69 : c ≤ coefficient profile 69 := by
  have hf := raw_first_cost_upper_69
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 69-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 69-1-
      (K*C/young 69)*(69 : ℝ)^2-(5954339995258/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 69 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 69-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 69-1-
      ((K*C/young 69)*(69 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 69+
        t 3*tripleHarmonicNeighborCharge K young zeta 69)
  linarith only [hf,hn]

def rowGrid_70 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 79196865912 else
  if aa=25 then 81687736897 else
  if aa=26 then 82259746926 else
  if aa=27 then 84752894675 else
  if aa=28 then 84667779043 else
  if aa=29 then 86851248062 else
  if aa=30 then 88196326483 else
  if aa=31 then 89300292423 else
  if aa=32 then 90453763061 else
  if aa=33 then 91491811304 else
  if aa=34 then 92581395697 else
  if aa=35 then 93570898312 else
  if aa=36 then 94596836555 else
  if aa=37 then 95430292472 else
  if aa=38 then 96184851152 else
  if aa=39 then 96954587521 else
  if aa=40 then 101009880194 else
  if aa=41 then 102540180953 else
  if aa=42 then 103592070948 else
  if aa=43 then 103342664626 else
  if aa=44 then 105334523919 else
  if aa=45 then 103739347521 else
  if aa=46 then 104297955783 else
  if aa=47 then 102271967599 else
  if aa=48 then 103540201485 else
  if aa=49 then 100841952499 else
  if aa=50 then 97982282601 else
  if aa=51 then 94979281244 else
  if aa=52 then 91843659482 else
  if aa=53 then 88572821497 else
  if aa=54 then 85244815540 else
  if aa=55 then 81854666531 else
  if aa=56 then 78287790076 else
  if aa=57 then 74523091594 else
  if aa=58 then 70494195636 else
  if aa=59 then 66124218377 else
  if aa=60 then 61300102982 else
  if aa=61 then 55885972830 else
  if aa=62 then 49783894550 else
  if aa=63 then 42964830325 else
  if aa=64 then 35845630942 else
  if aa=65 then 29571833935 else
  if aa=66 then 23951118034 else
  if aa=67 then 18656464317 else
  if aa=68 then 12231054768 else
  if aa=69 then 9547449742 else
  0

theorem raw_first_cost_upper_70 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 70 ≤ (6151423898435/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 69) :
      rawRow 70 aa ≤ rowGrid_70 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 69 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_70,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 70 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 69,rowGrid_70 aa/10000000000)+(0/10000000000 : ℝ)=(6151423898435/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_70]
  change (∑ aa ∈ Finset.Icc 2 69,rawRow 70 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 70 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_70 : c ≤ coefficient profile 70 := by
  have hf := raw_first_cost_upper_70
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 70-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 70-1-
      (K*C/young 70)*(70 : ℝ)^2-(6151423898435/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 70 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 70-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 70-1-
      ((K*C/young 70)*(70 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 70+
        t 3*tripleHarmonicNeighborCharge K young zeta 70)
  linarith only [hf,hn]

def rowGrid_71 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 81120443266 else
  if aa=26 then 83574726174 else
  if aa=27 then 84078587550 else
  if aa=28 then 86548285568 else
  if aa=29 then 86391264267 else
  if aa=30 then 88557972551 else
  if aa=31 then 89873103415 else
  if aa=32 then 90947307387 else
  if aa=33 then 92072579412 else
  if aa=34 then 93084438209 else
  if aa=35 then 94150250719 else
  if aa=36 then 95122312556 else
  if aa=37 then 96138439607 else
  if aa=38 then 96952604771 else
  if aa=39 then 97697899894 else
  if aa=40 then 98451356992 else
  if aa=41 then 102584260180 else
  if aa=42 then 103897167278 else
  if aa=43 then 103919671423 else
  if aa=44 then 106389404880 else
  if aa=45 then 105309049560 else
  if aa=46 then 106210985039 else
  if aa=47 then 104463614452 else
  if aa=48 then 106061128479 else
  if aa=49 then 103540201485 else
  if aa=50 then 100841952499 else
  if aa=51 then 97982282601 else
  if aa=52 then 94979281244 else
  if aa=53 then 91843659482 else
  if aa=54 then 88572821497 else
  if aa=55 then 85244815540 else
  if aa=56 then 81854666531 else
  if aa=57 then 78287790076 else
  if aa=58 then 74523091594 else
  if aa=59 then 70494195636 else
  if aa=60 then 66124218377 else
  if aa=61 then 61300102982 else
  if aa=62 then 55885972830 else
  if aa=63 then 49783894550 else
  if aa=64 then 42964830325 else
  if aa=65 then 35845630942 else
  if aa=66 then 29571833935 else
  if aa=67 then 23951118034 else
  if aa=68 then 18656464317 else
  if aa=69 then 12231054768 else
  if aa=70 then 9547449742 else
  0

theorem raw_first_cost_upper_71 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 71 ≤ (6350793069663/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 70) :
      rawRow 71 aa ≤ rowGrid_71 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 70 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_71,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 71 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 70,rowGrid_71 aa/10000000000)+(0/10000000000 : ℝ)=(6350793069663/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_71]
  change (∑ aa ∈ Finset.Icc 2 70,rawRow 71 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 71 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_71 : c ≤ coefficient profile 71 := by
  have hf := raw_first_cost_upper_71
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 71-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 71-1-
      (K*C/young 71)*(71 : ℝ)^2-(6350793069663/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 71 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 71-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 71-1-
      ((K*C/young 71)*(71 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 71+
        t 3*tripleHarmonicNeighborCharge K young zeta 71)
  linarith only [hf,hn]

def rowGrid_72 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 82994328043 else
  if aa=27 then 85422642230 else
  if aa=28 then 85859694036 else
  if aa=29 then 88310050115 else
  if aa=30 then 88088949558 else
  if aa=31 then 90241625051 else
  if aa=32 then 91530683051 else
  if aa=33 then 92574956512 else
  if aa=34 then 93675315931 else
  if aa=35 then 94661817630 else
  if aa=36 then 95711270680 else
  if aa=37 then 96672479059 else
  if aa=38 then 97672048330 else
  if aa=39 then 98477730764 else
  if aa=40 then 99206144502 else
  if aa=41 then 99985858822 else
  if aa=42 then 103941829837 else
  if aa=43 then 104225732593 else
  if aa=44 then 106983422946 else
  if aa=45 then 106363675405 else
  if aa=46 then 107818085949 else
  if aa=47 then 106379682214 else
  if aa=48 then 108333975515 else
  if aa=49 then 106061128479 else
  if aa=50 then 103540201485 else
  if aa=51 then 100841952499 else
  if aa=52 then 97982282601 else
  if aa=53 then 94979281244 else
  if aa=54 then 91843659482 else
  if aa=55 then 88572821497 else
  if aa=56 then 85244815540 else
  if aa=57 then 81854666531 else
  if aa=58 then 78287790076 else
  if aa=59 then 74523091594 else
  if aa=60 then 70494195636 else
  if aa=61 then 66124218377 else
  if aa=62 then 61300102982 else
  if aa=63 then 55885972830 else
  if aa=64 then 49783894550 else
  if aa=65 then 42964830325 else
  if aa=66 then 35845630942 else
  if aa=67 then 29571833935 else
  if aa=68 then 23951118034 else
  if aa=69 then 18656464317 else
  if aa=70 then 12231054768 else
  if aa=71 then 9547449742 else
  0

theorem raw_first_cost_upper_72 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 72 ≤ (6552355647792/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 71) :
      rawRow 72 aa ≤ rowGrid_72 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 71 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_72,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 72 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 71,rowGrid_72 aa/10000000000)+(0/10000000000 : ℝ)=(6552355647792/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_72]
  change (∑ aa ∈ Finset.Icc 2 71,rawRow 72 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 72 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_72 : c ≤ coefficient profile 72 := by
  have hf := raw_first_cost_upper_72
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 72-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 72-1-
      (K*C/young 72)*(72 : ℝ)^2-(6552355647792/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 72 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 72-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 72-1-
      ((K*C/young 72)*(72 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 72+
        t 3*tripleHarmonicNeighborCharge K young zeta 72)
  linarith only [hf,hn]

def rowGrid_73 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 84829410948 else
  if aa=28 then 87232220941 else
  if aa=29 then 87607441711 else
  if aa=30 then 90045441700 else
  if aa=31 then 89763685055 else
  if aa=32 then 91906001536 else
  if aa=33 then 93168772627 else
  if aa=34 then 94186438067 else
  if aa=35 then 95262708179 else
  if aa=36 then 96231319418 else
  if aa=37 then 97271035175 else
  if aa=38 then 98214606826 else
  if aa=39 then 99208491628 else
  if aa=40 then 99998014278 else
  if aa=41 then 100752410750 else
  if aa=42 then 101309042006 else
  if aa=43 then 104270536392 else
  if aa=44 then 107298507387 else
  if aa=45 then 106957549813 else
  if aa=46 then 108897838739 else
  if aa=47 then 107989335716 else
  if aa=48 then 110321033296 else
  if aa=49 then 108333975515 else
  if aa=50 then 106061128479 else
  if aa=51 then 103540201485 else
  if aa=52 then 100841952499 else
  if aa=53 then 97982282601 else
  if aa=54 then 94979281244 else
  if aa=55 then 91843659482 else
  if aa=56 then 88572821497 else
  if aa=57 then 85244815540 else
  if aa=58 then 81854666531 else
  if aa=59 then 78287790076 else
  if aa=60 then 74523091594 else
  if aa=61 then 70494195636 else
  if aa=62 then 66124218377 else
  if aa=63 then 61300102982 else
  if aa=64 then 55885972830 else
  if aa=65 then 49783894550 else
  if aa=66 then 42964830325 else
  if aa=67 then 35845630942 else
  if aa=68 then 29571833935 else
  if aa=69 then 23951118034 else
  if aa=70 then 18656464317 else
  if aa=71 then 12231054768 else
  if aa=72 then 9547449742 else
  0

theorem raw_first_cost_upper_73 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 73 ≤ (6756033397991/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 72) :
      rawRow 73 aa ≤ rowGrid_73 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 72 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_73,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 73 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 72,rowGrid_73 aa/10000000000)+(0/10000000000 : ℝ)=(6756033397991/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_73]
  change (∑ aa ∈ Finset.Icc 2 72,rawRow 73 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 73 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_73 : c ≤ coefficient profile 73 := by
  have hf := raw_first_cost_upper_73
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 73-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 73-1-
      (K*C/young 73)*(73 : ℝ)^2-(6756033397991/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 73 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 73-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 73-1-
      ((K*C/young 73)*(73 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 73+
        t 3*tripleHarmonicNeighborCharge K young zeta 73)
  linarith only [hf,hn]

def rowGrid_74 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 86626422749 else
  if aa=29 then 89007907579 else
  if aa=30 then 89329026254 else
  if aa=31 then 91757373768 else
  if aa=32 then 91419246627 else
  if aa=33 then 93550808043 else
  if aa=34 then 94790590927 else
  if aa=35 then 95782491630 else
  if aa=36 then 96842172788 else
  if aa=37 then 97799558919 else
  if aa=38 then 98822711161 else
  if aa=39 then 99759584912 else
  if aa=40 then 100740056511 else
  if aa=41 then 101556622921 else
  if aa=42 then 102085738255 else
  if aa=43 then 101629422611 else
  if aa=44 then 107344632088 else
  if aa=45 then 107272558052 else
  if aa=46 then 109505862476 else
  if aa=47 then 109070803500 else
  if aa=48 then 111990324217 else
  if aa=49 then 110321033296 else
  if aa=50 then 108333975515 else
  if aa=51 then 106061128479 else
  if aa=52 then 103540201485 else
  if aa=53 then 100841952499 else
  if aa=54 then 97982282601 else
  if aa=55 then 94979281244 else
  if aa=56 then 91843659482 else
  if aa=57 then 88572821497 else
  if aa=58 then 85244815540 else
  if aa=59 then 81854666531 else
  if aa=60 then 78287790076 else
  if aa=61 then 74523091594 else
  if aa=62 then 70494195636 else
  if aa=63 then 66124218377 else
  if aa=64 then 61300102982 else
  if aa=65 then 55885972830 else
  if aa=66 then 49783894550 else
  if aa=67 then 42964830325 else
  if aa=68 then 35845630942 else
  if aa=69 then 29571833935 else
  if aa=70 then 23951118034 else
  if aa=71 then 18656464317 else
  if aa=72 then 12231054768 else
  if aa=73 then 9547449742 else
  0

theorem raw_first_cost_upper_74 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 74 ≤ (6961779634065/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 73) :
      rawRow 74 aa ≤ rowGrid_74 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 73 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_74,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 74 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 73,rowGrid_74 aa/10000000000)+(0/10000000000 : ℝ)=(6961779634065/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_74]
  change (∑ aa ∈ Finset.Icc 2 73,rawRow 74 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 74 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_74 : c ≤ coefficient profile 74 := by
  have hf := raw_first_cost_upper_74
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 74-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 74-1-
      (K*C/young 74)*(74 : ℝ)^2-(6961779634065/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 74 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 74-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 74-1-
      ((K*C/young 74)*(74 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 74+
        t 3*tripleHarmonicNeighborCharge K young zeta 74)
  linarith only [hf,hn]

def rowGrid_75 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 88389777845 else
  if aa=30 then 90757012847 else
  if aa=31 then 91027337925 else
  if aa=32 then 93449706049 else
  if aa=33 then 93055341867 else
  if aa=34 then 95179276555 else
  if aa=35 then 96396882273 else
  if aa=36 then 97370574297 else
  if aa=37 then 98420367098 else
  if aa=38 then 99359665961 else
  if aa=39 then 100377255114 else
  if aa=40 then 101299657486 else
  if aa=41 then 102310230918 else
  if aa=42 then 102900593131 else
  if aa=43 then 102408575090 else
  if aa=44 then 104625653199 else
  if aa=45 then 107318671599 else
  if aa=46 then 109828375932 else
  if aa=47 then 109679792975 else
  if aa=48 then 113111860219 else
  if aa=49 then 111990324217 else
  if aa=50 then 110321033296 else
  if aa=51 then 108333975515 else
  if aa=52 then 106061128479 else
  if aa=53 then 103540201485 else
  if aa=54 then 100841952499 else
  if aa=55 then 97982282601 else
  if aa=56 then 94979281244 else
  if aa=57 then 91843659482 else
  if aa=58 then 88572821497 else
  if aa=59 then 85244815540 else
  if aa=60 then 81854666531 else
  if aa=61 then 78287790076 else
  if aa=62 then 74523091594 else
  if aa=63 then 70494195636 else
  if aa=64 then 66124218377 else
  if aa=65 then 61300102982 else
  if aa=66 then 55885972830 else
  if aa=67 then 49783894550 else
  if aa=68 then 42964830325 else
  if aa=69 then 35845630942 else
  if aa=70 then 29571833935 else
  if aa=71 then 23951118034 else
  if aa=72 then 18656464317 else
  if aa=73 then 12231054768 else
  if aa=74 then 9547449742 else
  0

theorem raw_first_cost_upper_75 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 75 ≤ (7169448025389/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 74) :
      rawRow 75 aa ≤ rowGrid_75 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 74 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_75,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 75 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 74,rowGrid_75 aa/10000000000)+(0/10000000000 : ℝ)=(7169448025389/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_75]
  change (∑ aa ∈ Finset.Icc 2 74,rawRow 75 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 75 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_75 : c ≤ coefficient profile 75 := by
  have hf := raw_first_cost_upper_75
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 75-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 75-1-
      (K*C/young 75)*(75 : ℝ)^2-(7169448025389/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 75 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 75-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 75-1-
      ((K*C/young 75)*(75 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 75+
        t 3*tripleHarmonicNeighborCharge K young zeta 75)
  linarith only [hf,hn]

def rowGrid_76 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 90126736170 else
  if aa=31 then 92482473211 else
  if aa=32 then 92706205750 else
  if aa=33 then 95122139645 else
  if aa=34 then 94675185643 else
  if aa=35 then 96792154444 else
  if aa=36 then 97995151594 else
  if aa=37 then 98957379734 else
  if aa=38 then 99990377326 else
  if aa=39 then 100922656554 else
  if aa=40 then 101926863182 else
  if aa=41 then 102878554056 else
  if aa=42 then 103664174153 else
  if aa=43 then 103226006871 else
  if aa=44 then 105427776590 else
  if aa=45 then 104600350275 else
  if aa=46 then 109875588155 else
  if aa=47 then 110002818685 else
  if aa=48 then 113743412661 else
  if aa=49 then 113111860219 else
  if aa=50 then 111990324217 else
  if aa=51 then 110321033296 else
  if aa=52 then 108333975515 else
  if aa=53 then 106061128479 else
  if aa=54 then 103540201485 else
  if aa=55 then 100841952499 else
  if aa=56 then 97982282601 else
  if aa=57 then 94979281244 else
  if aa=58 then 91843659482 else
  if aa=59 then 88572821497 else
  if aa=60 then 85244815540 else
  if aa=61 then 81854666531 else
  if aa=62 then 78287790076 else
  if aa=63 then 74523091594 else
  if aa=64 then 70494195636 else
  if aa=65 then 66124218377 else
  if aa=66 then 61300102982 else
  if aa=67 then 55885972830 else
  if aa=68 then 49783894550 else
  if aa=69 then 42964830325 else
  if aa=70 then 35845630942 else
  if aa=71 then 29571833935 else
  if aa=72 then 23951118034 else
  if aa=73 then 18656464317 else
  if aa=74 then 12231054768 else
  if aa=75 then 9547449742 else
  0

theorem raw_first_cost_upper_76 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 76 ≤ (7379068873095/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 75) :
      rawRow 76 aa ≤ rowGrid_76 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 75 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_76,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 76 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 75,rowGrid_76 aa/10000000000)+(0/10000000000 : ℝ)=(7379068873095/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_76]
  change (∑ aa ∈ Finset.Icc 2 75,rawRow 76 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 76 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_76 : c ≤ coefficient profile 76 := by
  have hf := raw_first_cost_upper_76
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 76-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 76-1-
      (K*C/young 76)*(76 : ℝ)^2-(7379068873095/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 76 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 76-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 76-1-
      ((K*C/young 76)*(76 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 76+
        t 3*tripleHarmonicNeighborCharge K young zeta 76)
  linarith only [hf,hn]

def rowGrid_77 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 91840213797 else
  if aa=32 then 94188178905 else
  if aa=33 then 94365333205 else
  if aa=34 then 96777960823 else
  if aa=35 then 96279521367 else
  if aa=36 then 98396977415 else
  if aa=37 then 99592135493 else
  if aa=38 then 100535956434 else
  if aa=39 then 101563289409 else
  if aa=40 then 102480684443 else
  if aa=41 then 103515535628 else
  if aa=42 then 104240018310 else
  if aa=43 then 103992002648 else
  if aa=44 then 106269307830 else
  if aa=45 then 105402279678 else
  if aa=46 then 107092501579 else
  if aa=47 then 110050105897 else
  if aa=48 then 114078406425 else
  if aa=49 then 113743412661 else
  if aa=50 then 113111860219 else
  if aa=51 then 111990324217 else
  if aa=52 then 110321033296 else
  if aa=53 then 108333975515 else
  if aa=54 then 106061128479 else
  if aa=55 then 103540201485 else
  if aa=56 then 100841952499 else
  if aa=57 then 97982282601 else
  if aa=58 then 94979281244 else
  if aa=59 then 91843659482 else
  if aa=60 then 88572821497 else
  if aa=61 then 85244815540 else
  if aa=62 then 81854666531 else
  if aa=63 then 78287790076 else
  if aa=64 then 74523091594 else
  if aa=65 then 70494195636 else
  if aa=66 then 66124218377 else
  if aa=67 then 61300102982 else
  if aa=68 then 55885972830 else
  if aa=69 then 49783894550 else
  if aa=70 then 42964830325 else
  if aa=71 then 35845630942 else
  if aa=72 then 29571833935 else
  if aa=73 then 23951118034 else
  if aa=74 then 18656464317 else
  if aa=75 then 12231054768 else
  if aa=76 then 9547449742 else
  0

theorem raw_first_cost_upper_77 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 77 ≤ (7590527142968/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 76) :
      rawRow 77 aa ≤ rowGrid_77 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 76 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_77,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 77 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 76,rowGrid_77 aa/10000000000)+(0/10000000000 : ℝ)=(7590527142968/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_77]
  change (∑ aa ∈ Finset.Icc 2 76,rawRow 77 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 77 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_77 : c ≤ coefficient profile 77 := by
  have hf := raw_first_cost_upper_77
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 77-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 77-1-
      (K*C/young 77)*(77 : ℝ)^2-(7590527142968/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 77 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 77-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 77-1-
      ((K*C/young 77)*(77 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 77+
        t 3*tripleHarmonicNeighborCharge K young zeta 77)
  linarith only [hf,hn]

def rowGrid_78 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 93534073943 else
  if aa=33 then 95873828666 else
  if aa=34 then 96007980414 else
  if aa=35 then 98417929509 else
  if aa=36 then 97875844834 else
  if aa=37 then 100000509692 else
  if aa=38 then 101180837872 else
  if aa=39 then 102117450823 else
  if aa=40 then 103131207286 else
  if aa=41 then 104077988966 else
  if aa=42 then 104885429507 else
  if aa=43 then 104569667860 else
  if aa=44 then 107057886634 else
  if aa=45 then 106243607400 else
  if aa=46 then 107913537318 else
  if aa=47 then 107262598885 else
  if aa=48 then 114127445620 else
  if aa=49 then 114078406425 else
  if aa=50 then 113743412661 else
  if aa=51 then 113111860219 else
  if aa=52 then 111990324217 else
  if aa=53 then 110321033296 else
  if aa=54 then 108333975515 else
  if aa=55 then 106061128479 else
  if aa=56 then 103540201485 else
  if aa=57 then 100841952499 else
  if aa=58 then 97982282601 else
  if aa=59 then 94979281244 else
  if aa=60 then 91843659482 else
  if aa=61 then 88572821497 else
  if aa=62 then 85244815540 else
  if aa=63 then 81854666531 else
  if aa=64 then 78287790076 else
  if aa=65 then 74523091594 else
  if aa=66 then 70494195636 else
  if aa=67 then 66124218377 else
  if aa=68 then 61300102982 else
  if aa=69 then 55885972830 else
  if aa=70 then 49783894550 else
  if aa=71 then 42964830325 else
  if aa=72 then 35845630942 else
  if aa=73 then 29571833935 else
  if aa=74 then 23951118034 else
  if aa=75 then 18656464317 else
  if aa=76 then 12231054768 else
  if aa=77 then 9547449742 else
  0

theorem raw_first_cost_upper_78 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 78 ≤ (7803856818592/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 77) :
      rawRow 78 aa ≤ rowGrid_78 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 77 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_78,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 78 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 77,rowGrid_78 aa/10000000000)+(0/10000000000 : ℝ)=(7803856818592/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_78]
  change (∑ aa ∈ Finset.Icc 2 77,rawRow 78 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 78 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_78 : c ≤ coefficient profile 78 := by
  have hf := raw_first_cost_upper_78
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 78-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 78-1-
      (K*C/young 78)*(78 : ℝ)^2-(7803856818592/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 78 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 78-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 78-1-
      ((K*C/young 78)*(78 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 78+
        t 3*tripleHarmonicNeighborCharge K young zeta 78)
  linarith only [hf,hn]

def rowGrid_79 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 95208017438 else
  if aa=34 then 97542734733 else
  if aa=35 then 97634901256 else
  if aa=36 then 100049707983 else
  if aa=37 then 99470884442 else
  if aa=38 then 101595726492 else
  if aa=39 then 102772476655 else
  if aa=40 then 103693923755 else
  if aa=41 then 104738651116 else
  if aa=42 then 105455326186 else
  if aa=43 then 105217120111 else
  if aa=44 then 107652582526 else
  if aa=45 then 107031995492 else
  if aa=46 then 108774910058 else
  if aa=47 then 108084938693 else
  if aa=48 then 111236661896 else
  if aa=49 then 114127445620 else
  if aa=50 then 114078406425 else
  if aa=51 then 113743412661 else
  if aa=52 then 113111860219 else
  if aa=53 then 111990324217 else
  if aa=54 then 110321033296 else
  if aa=55 then 108333975515 else
  if aa=56 then 106061128479 else
  if aa=57 then 103540201485 else
  if aa=58 then 100841952499 else
  if aa=59 then 97982282601 else
  if aa=60 then 94979281244 else
  if aa=61 then 91843659482 else
  if aa=62 then 88572821497 else
  if aa=63 then 85244815540 else
  if aa=64 then 81854666531 else
  if aa=65 then 78287790076 else
  if aa=66 then 74523091594 else
  if aa=67 then 70494195636 else
  if aa=68 then 66124218377 else
  if aa=69 then 61300102982 else
  if aa=70 then 55885972830 else
  if aa=71 then 49783894550 else
  if aa=72 then 42964830325 else
  if aa=73 then 35845630942 else
  if aa=74 then 29571833935 else
  if aa=75 then 23951118034 else
  if aa=76 then 18656464317 else
  if aa=77 then 12231054768 else
  if aa=78 then 9547449742 else
  0

theorem raw_first_cost_upper_79 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 79 ≤ (8018924599480/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 78) :
      rawRow 79 aa ≤ rowGrid_79 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 78 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_79,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 79 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 78,rowGrid_79 aa/10000000000)+(0/10000000000 : ℝ)=(8018924599480/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_79]
  change (∑ aa ∈ Finset.Icc 2 78,rawRow 79 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 79 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_79 : c ≤ coefficient profile 79 := by
  have hf := raw_first_cost_upper_79
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 79-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 79-1-
      (K*C/young 79)*(79 : ℝ)^2-(8018924599480/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 79 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 79-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 79-1-
      ((K*C/young 79)*(79 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 79+
        t 3*tripleHarmonicNeighborCharge K young zeta 79)
  linarith only [hf,hn]

def rowGrid_80 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 96865333519 else
  if aa=35 then 99195663036 else
  if aa=36 then 99253697048 else
  if aa=37 then 101680174084 else
  if aa=38 then 101057652614 else
  if aa=39 then 103193891736 else
  if aa=40 then 104359061771 else
  if aa=41 then 105310138306 else
  if aa=42 then 106124731342 else
  if aa=43 then 105788819036 else
  if aa=44 then 108319122913 else
  if aa=45 then 107626547561 else
  if aa=46 then 109582081858 else
  if aa=47 then 108947679570 else
  if aa=48 then 112089469269 else
  if aa=49 then 111236661896 else
  if aa=50 then 114127445620 else
  if aa=51 then 114078406425 else
  if aa=52 then 113743412661 else
  if aa=53 then 113111860219 else
  if aa=54 then 111990324217 else
  if aa=55 then 110321033296 else
  if aa=56 then 108333975515 else
  if aa=57 then 106061128479 else
  if aa=58 then 103540201485 else
  if aa=59 then 100841952499 else
  if aa=60 then 97982282601 else
  if aa=61 then 94979281244 else
  if aa=62 then 91843659482 else
  if aa=63 then 88572821497 else
  if aa=64 then 85244815540 else
  if aa=65 then 81854666531 else
  if aa=66 then 78287790076 else
  if aa=67 then 74523091594 else
  if aa=68 then 70494195636 else
  if aa=69 then 66124218377 else
  if aa=70 then 61300102982 else
  if aa=71 then 55885972830 else
  if aa=72 then 49783894550 else
  if aa=73 then 42964830325 else
  if aa=74 then 35845630942 else
  if aa=75 then 29571833935 else
  if aa=76 then 23951118034 else
  if aa=77 then 18656464317 else
  if aa=78 then 12231054768 else
  if aa=79 then 9547449742 else
  0

theorem raw_first_cost_upper_80 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 80 ≤ (8235835859355/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 79) :
      rawRow 80 aa ≤ rowGrid_80 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 79 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_80,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 80 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 79,rowGrid_80 aa/10000000000)+(0/10000000000 : ℝ)=(8235835859355/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_80]
  change (∑ aa ∈ Finset.Icc 2 79,rawRow 80 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 80 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_80 : c ≤ coefficient profile 80 := by
  have hf := raw_first_cost_upper_80
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 80-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 80-1-
      (K*C/young 80)*(80 : ℝ)^2-(8235835859355/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 80 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 80-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 80-1-
      ((K*C/young 80)*(80 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 80+
        t 3*tripleHarmonicNeighborCharge K young zeta 80)
  linarith only [hf,hn]

def rowGrid_81 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 195790976138 else
  if aa=35 then 98506782795 else
  if aa=36 then 100840336404 else
  if aa=37 then 100871190908 else
  if aa=38 then 103302185035 else
  if aa=39 then 102647353615 else
  if aa=40 then 104786982591 else
  if aa=41 then 105985643427 else
  if aa=42 then 106703781425 else
  if aa=43 then 106460341125 else
  if aa=44 then 108907676621 else
  if aa=45 then 108292926751 else
  if aa=46 then 110190799403 else
  if aa=47 then 109756133418 else
  if aa=48 then 112984174565 else
  if aa=49 then 112089469269 else
  if aa=50 then 111236661896 else
  if aa=51 then 114127445620 else
  if aa=52 then 114078406425 else
  if aa=53 then 113743412661 else
  if aa=54 then 113111860219 else
  if aa=55 then 111990324217 else
  if aa=56 then 110321033296 else
  if aa=57 then 108333975515 else
  if aa=58 then 106061128479 else
  if aa=59 then 103540201485 else
  if aa=60 then 100841952499 else
  if aa=61 then 97982282601 else
  if aa=62 then 94979281244 else
  if aa=63 then 91843659482 else
  if aa=64 then 88572821497 else
  if aa=65 then 85244815540 else
  if aa=66 then 81854666531 else
  if aa=67 then 78287790076 else
  if aa=68 then 74523091594 else
  if aa=69 then 70494195636 else
  if aa=70 then 66124218377 else
  if aa=71 then 61300102982 else
  if aa=72 then 55885972830 else
  if aa=73 then 49783894550 else
  if aa=74 then 42964830325 else
  if aa=75 then 35845630942 else
  if aa=76 then 29571833935 else
  if aa=77 then 23951118034 else
  if aa=78 then 18656464317 else
  if aa=79 then 12231054768 else
  if aa=80 then 9547449742 else
  0

theorem raw_first_cost_upper_81 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 81 ≤ (8454558549182/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 80) :
      rawRow 81 aa ≤ rowGrid_81 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 80 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_81,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 81 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 80,rowGrid_81 aa/10000000000)+(0/10000000000 : ℝ)=(8454558549182/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_81]
  change (∑ aa ∈ Finset.Icc 2 80,rawRow 81 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 81 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_81 : c ≤ coefficient profile 81 := by
  have hf := raw_first_cost_upper_81
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 81-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 81-1-
      (K*C/young 81)*(81 : ℝ)^2-(8454558549182/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 81 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 81-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 81-1-
      ((K*C/young 81)*(81 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 81+
        t 3*tripleHarmonicNeighborCharge K young zeta 81)
  linarith only [hf,hn]

def rowGrid_82 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 195790976138 else
  if aa=35 then 199108788037 else
  if aa=36 then 100140034465 else
  if aa=37 then 102483687029 else
  if aa=38 then 102480296890 else
  if aa=39 then 104927193956 else
  if aa=40 then 104232007102 else
  if aa=41 then 106420233991 else
  if aa=42 then 107388225980 else
  if aa=43 then 107041222401 else
  if aa=44 then 109598996471 else
  if aa=45 then 108881338121 else
  if aa=46 then 110873055383 else
  if aa=47 then 110365817802 else
  if aa=48 then 113822581505 else
  if aa=49 then 112984174565 else
  if aa=50 then 112089469269 else
  if aa=51 then 111236661896 else
  if aa=52 then 114127445620 else
  if aa=53 then 114078406425 else
  if aa=54 then 113743412661 else
  if aa=55 then 113111860219 else
  if aa=56 then 111990324217 else
  if aa=57 then 110321033296 else
  if aa=58 then 108333975515 else
  if aa=59 then 106061128479 else
  if aa=60 then 103540201485 else
  if aa=61 then 100841952499 else
  if aa=62 then 97982282601 else
  if aa=63 then 94979281244 else
  if aa=64 then 91843659482 else
  if aa=65 then 88572821497 else
  if aa=66 then 85244815540 else
  if aa=67 then 81854666531 else
  if aa=68 then 78287790076 else
  if aa=69 then 74523091594 else
  if aa=70 then 70494195636 else
  if aa=71 then 66124218377 else
  if aa=72 then 61300102982 else
  if aa=73 then 55885972830 else
  if aa=74 then 49783894550 else
  if aa=75 then 42964830325 else
  if aa=76 then 35845630942 else
  if aa=77 then 29571833935 else
  if aa=78 then 23951118034 else
  if aa=79 then 18656464317 else
  if aa=80 then 12231054768 else
  if aa=81 then 9547449742 else
  0

theorem raw_first_cost_upper_82 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 82 ≤ (8675069894797/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 81) :
      rawRow 82 aa ≤ rowGrid_82 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 81 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_82,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 82 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 81,rowGrid_82 aa/10000000000)+(0/10000000000 : ℝ)=(8675069894797/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_82]
  change (∑ aa ∈ Finset.Icc 2 81,rawRow 82 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 82 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_82 : c ≤ coefficient profile 82 := by
  have hf := raw_first_cost_upper_82
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 82-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 82-1-
      (K*C/young 82)*(82 : ℝ)^2-(8675069894797/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 82 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 82-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 82-1-
      ((K*C/young 82)*(82 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 82+
        t 3*tripleHarmonicNeighborCharge K young zeta 82)
  linarith only [hf,hn]

def rowGrid_83 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 195790976138 else
  if aa=35 then 199108788037 else
  if aa=36 then 202410030360 else
  if aa=37 then 101771972576 else
  if aa=38 then 104118515688 else
  if aa=39 then 104092376989 else
  if aa=40 then 106547043254 else
  if aa=41 then 105856608433 else
  if aa=42 then 107828567786 else
  if aa=43 then 107727831449 else
  if aa=44 then 110197003242 else
  if aa=45 then 109572490781 else
  if aa=46 then 111475485923 else
  if aa=47 then 111049157423 else
  if aa=48 then 114454854603 else
  if aa=49 then 113822581505 else
  if aa=50 then 112984174565 else
  if aa=51 then 112089469269 else
  if aa=52 then 111236661896 else
  if aa=53 then 114127445620 else
  if aa=54 then 114078406425 else
  if aa=55 then 113743412661 else
  if aa=56 then 113111860219 else
  if aa=57 then 111990324217 else
  if aa=58 then 110321033296 else
  if aa=59 then 108333975515 else
  if aa=60 then 106061128479 else
  if aa=61 then 103540201485 else
  if aa=62 then 100841952499 else
  if aa=63 then 97982282601 else
  if aa=64 then 94979281244 else
  if aa=65 then 91843659482 else
  if aa=66 then 88572821497 else
  if aa=67 then 85244815540 else
  if aa=68 then 81854666531 else
  if aa=69 then 78287790076 else
  if aa=70 then 74523091594 else
  if aa=71 then 70494195636 else
  if aa=72 then 66124218377 else
  if aa=73 then 61300102982 else
  if aa=74 then 55885972830 else
  if aa=75 then 49783894550 else
  if aa=76 then 42964830325 else
  if aa=77 then 35845630942 else
  if aa=78 then 29571833935 else
  if aa=79 then 23951118034 else
  if aa=80 then 18656464317 else
  if aa=81 then 12231054768 else
  if aa=82 then 9547449742 else
  0

theorem raw_first_cost_upper_83 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 83 ≤ (8897339723713/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 82) :
      rawRow 83 aa ≤ rowGrid_83 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 82 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_83,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 83 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 82,rowGrid_83 aa/10000000000)+(0/10000000000 : ℝ)=(8897339723713/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_83]
  change (∑ aa ∈ Finset.Icc 2 82,rawRow 83 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 83 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_83 : c ≤ coefficient profile 83 := by
  have hf := raw_first_cost_upper_83
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 83-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 83-1-
      (K*C/young 83)*(83 : ℝ)^2-(8897339723713/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 83 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 83-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 83-1-
      ((K*C/young 83)*(83 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 83+
        t 3*tripleHarmonicNeighborCharge K young zeta 83)
  linarith only [hf,hn]

def rowGrid_84 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 195790976138 else
  if aa=35 then 199108788037 else
  if aa=36 then 202410030360 else
  if aa=37 then 205708617628 else
  if aa=38 then 103395447905 else
  if aa=39 then 105756366008 else
  if aa=40 then 105699338516 else
  if aa=41 then 108207727656 else
  if aa=42 then 107257483376 else
  if aa=43 then 108169565796 else
  if aa=44 then 110903854845 else
  if aa=45 then 110170352929 else
  if aa=46 then 112183105612 else
  if aa=47 then 111652544817 else
  if aa=48 then 115163511853 else
  if aa=49 then 114454854603 else
  if aa=50 then 113822581505 else
  if aa=51 then 112984174565 else
  if aa=52 then 112089469269 else
  if aa=53 then 111236661896 else
  if aa=54 then 114127445620 else
  if aa=55 then 114078406425 else
  if aa=56 then 113743412661 else
  if aa=57 then 113111860219 else
  if aa=58 then 111990324217 else
  if aa=59 then 110321033296 else
  if aa=60 then 108333975515 else
  if aa=61 then 106061128479 else
  if aa=62 then 103540201485 else
  if aa=63 then 100841952499 else
  if aa=64 then 97982282601 else
  if aa=65 then 94979281244 else
  if aa=66 then 91843659482 else
  if aa=67 then 88572821497 else
  if aa=68 then 85244815540 else
  if aa=69 then 81854666531 else
  if aa=70 then 78287790076 else
  if aa=71 then 74523091594 else
  if aa=72 then 70494195636 else
  if aa=73 then 66124218377 else
  if aa=74 then 61300102982 else
  if aa=75 then 55885972830 else
  if aa=76 then 49783894550 else
  if aa=77 then 42964830325 else
  if aa=78 then 35845630942 else
  if aa=79 then 29571833935 else
  if aa=80 then 23951118034 else
  if aa=81 then 18656464317 else
  if aa=82 then 12231054768 else
  if aa=83 then 9547449742 else
  0

theorem raw_first_cost_upper_84 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 84 ≤ (9121370587110/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 83) :
      rawRow 84 aa ≤ rowGrid_84 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 83 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_84,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 84 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 83,rowGrid_84 aa/10000000000)+(0/10000000000 : ℝ)=(9121370587110/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_84]
  change (∑ aa ∈ Finset.Icc 2 83,rawRow 84 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 84 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_84 : c ≤ coefficient profile 84 := by
  have hf := raw_first_cost_upper_84
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 84-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 84-1-
      (K*C/young 84)*(84 : ℝ)^2-(9121370587110/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 84 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 84-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 84-1-
      ((K*C/young 84)*(84 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 84+
        t 3*tripleHarmonicNeighborCharge K young zeta 84)
  linarith only [hf,hn]

def rowGrid_85 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 195790976138 else
  if aa=35 then 199108788037 else
  if aa=36 then 202410030360 else
  if aa=37 then 205708617628 else
  if aa=38 then 208990099329 else
  if aa=39 then 105021923910 else
  if aa=40 then 107389015932 else
  if aa=41 then 107346810256 else
  if aa=42 then 109639716612 else
  if aa=43 then 107596675383 else
  if aa=44 then 111358612368 else
  if aa=45 then 110877033584 else
  if aa=46 then 112795212100 else
  if aa=47 then 112361288433 else
  if aa=48 then 115789254659 else
  if aa=49 then 115163511853 else
  if aa=50 then 114454854603 else
  if aa=51 then 113822581505 else
  if aa=52 then 112984174565 else
  if aa=53 then 112089469269 else
  if aa=54 then 111236661896 else
  if aa=55 then 114127445620 else
  if aa=56 then 114078406425 else
  if aa=57 then 113743412661 else
  if aa=58 then 113111860219 else
  if aa=59 then 111990324217 else
  if aa=60 then 110321033296 else
  if aa=61 then 108333975515 else
  if aa=62 then 106061128479 else
  if aa=63 then 103540201485 else
  if aa=64 then 100841952499 else
  if aa=65 then 97982282601 else
  if aa=66 then 94979281244 else
  if aa=67 then 91843659482 else
  if aa=68 then 88572821497 else
  if aa=69 then 85244815540 else
  if aa=70 then 81854666531 else
  if aa=71 then 78287790076 else
  if aa=72 then 74523091594 else
  if aa=73 then 70494195636 else
  if aa=74 then 66124218377 else
  if aa=75 then 61300102982 else
  if aa=76 then 55885972830 else
  if aa=77 then 49783894550 else
  if aa=78 then 42964830325 else
  if aa=79 then 35845630942 else
  if aa=80 then 29571833935 else
  if aa=81 then 23951118034 else
  if aa=82 then 18656464317 else
  if aa=83 then 12231054768 else
  if aa=84 then 9547449742 else
  0

theorem raw_first_cost_upper_85 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 85 ≤ (9347140442216/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 84) :
      rawRow 85 aa ≤ rowGrid_85 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 84 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_85,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 85 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 84,rowGrid_85 aa/10000000000)+(0/10000000000 : ℝ)=(9347140442216/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_85]
  change (∑ aa ∈ Finset.Icc 2 84,rawRow 85 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 85 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_85 : c ≤ coefficient profile 85 := by
  have hf := raw_first_cost_upper_85
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 85-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 85-1-
      (K*C/young 85)*(85 : ℝ)^2-(9347140442216/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 85 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 85-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 85-1-
      ((K*C/young 85)*(85 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 85+
        t 3*tripleHarmonicNeighborCharge K young zeta 85)
  linarith only [hf,hn]

def rowGrid_86 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 195790976138 else
  if aa=35 then 199108788037 else
  if aa=36 then 202410030360 else
  if aa=37 then 205708617628 else
  if aa=38 then 208990099329 else
  if aa=39 then 212277646205 else
  if aa=40 then 106643235634 else
  if aa=41 then 109062823654 else
  if aa=42 then 108767406087 else
  if aa=43 then 109986442215 else
  if aa=44 then 110768832046 else
  if aa=45 then 111331681128 else
  if aa=46 then 113518729746 else
  if aa=47 then 112974367142 else
  if aa=48 then 116524257118 else
  if aa=49 then 115789254659 else
  if aa=50 then 115163511853 else
  if aa=51 then 114454854603 else
  if aa=52 then 113822581505 else
  if aa=53 then 112984174565 else
  if aa=54 then 112089469269 else
  if aa=55 then 111236661896 else
  if aa=56 then 114127445620 else
  if aa=57 then 114078406425 else
  if aa=58 then 113743412661 else
  if aa=59 then 113111860219 else
  if aa=60 then 111990324217 else
  if aa=61 then 110321033296 else
  if aa=62 then 108333975515 else
  if aa=63 then 106061128479 else
  if aa=64 then 103540201485 else
  if aa=65 then 100841952499 else
  if aa=66 then 97982282601 else
  if aa=67 then 94979281244 else
  if aa=68 then 91843659482 else
  if aa=69 then 88572821497 else
  if aa=70 then 85244815540 else
  if aa=71 then 81854666531 else
  if aa=72 then 78287790076 else
  if aa=73 then 74523091594 else
  if aa=74 then 70494195636 else
  if aa=75 then 66124218377 else
  if aa=76 then 61300102982 else
  if aa=77 then 55885972830 else
  if aa=78 then 49783894550 else
  if aa=79 then 42964830325 else
  if aa=80 then 35845630942 else
  if aa=81 then 29571833935 else
  if aa=82 then 23951118034 else
  if aa=83 then 18656464317 else
  if aa=84 then 12231054768 else
  if aa=85 then 9547449742 else
  0

theorem raw_first_cost_upper_86 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 86 ≤ (9574609574613/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 85) :
      rawRow 86 aa ≤ rowGrid_86 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 85 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_86,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 86 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 85,rowGrid_86 aa/10000000000)+(0/10000000000 : ℝ)=(9574609574613/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_86]
  change (∑ aa ∈ Finset.Icc 2 85,rawRow 86 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 86 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_86 : c ≤ coefficient profile 86 := by
  have hf := raw_first_cost_upper_86
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 86-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 86-1-
      (K*C/young 86)*(86 : ℝ)^2-(9574609574613/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 86 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 86-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 86-1-
      ((K*C/young 86)*(86 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 86+
        t 3*tripleHarmonicNeighborCharge K young zeta 86)
  linarith only [hf,hn]

def rowGrid_87 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 195790976138 else
  if aa=35 then 199108788037 else
  if aa=36 then 202410030360 else
  if aa=37 then 205708617628 else
  if aa=38 then 208990099329 else
  if aa=39 then 212277646205 else
  if aa=40 then 215554754677 else
  if aa=41 then 108305419329 else
  if aa=42 then 110506128697 else
  if aa=43 then 109111373087 else
  if aa=44 then 113229053794 else
  if aa=45 then 110742043439 else
  if aa=46 then 113984209476 else
  if aa=47 then 113699033967 else
  if aa=48 then 117160050301 else
  if aa=49 then 116524257118 else
  if aa=50 then 115789254659 else
  if aa=51 then 115163511853 else
  if aa=52 then 114454854603 else
  if aa=53 then 113822581505 else
  if aa=54 then 112984174565 else
  if aa=55 then 112089469269 else
  if aa=56 then 111236661896 else
  if aa=57 then 114127445620 else
  if aa=58 then 114078406425 else
  if aa=59 then 113743412661 else
  if aa=60 then 113111860219 else
  if aa=61 then 111990324217 else
  if aa=62 then 110321033296 else
  if aa=63 then 108333975515 else
  if aa=64 then 106061128479 else
  if aa=65 then 103540201485 else
  if aa=66 then 100841952499 else
  if aa=67 then 97982282601 else
  if aa=68 then 94979281244 else
  if aa=69 then 91843659482 else
  if aa=70 then 88572821497 else
  if aa=71 then 85244815540 else
  if aa=72 then 81854666531 else
  if aa=73 then 78287790076 else
  if aa=74 then 74523091594 else
  if aa=75 then 70494195636 else
  if aa=76 then 66124218377 else
  if aa=77 then 61300102982 else
  if aa=78 then 55885972830 else
  if aa=79 then 49783894550 else
  if aa=80 then 42964830325 else
  if aa=81 then 35845630942 else
  if aa=82 then 29571833935 else
  if aa=83 then 23951118034 else
  if aa=84 then 18656464317 else
  if aa=85 then 12231054768 else
  if aa=86 then 9547449742 else
  0

theorem raw_first_cost_upper_87 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 87 ≤ (9803848123728/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 86) :
      rawRow 87 aa ≤ rowGrid_87 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 86 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_87,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 87 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 86,rowGrid_87 aa/10000000000)+(0/10000000000 : ℝ)=(9803848123728/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_87]
  change (∑ aa ∈ Finset.Icc 2 86,rawRow 87 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 87 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_87 : c ≤ coefficient profile 87 := by
  have hf := raw_first_cost_upper_87
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 87-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 87-1-
      (K*C/young 87)*(87 : ℝ)^2-(9803848123728/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 87 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 87-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 87-1-
      ((K*C/young 87)*(87 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 87+
        t 3*tripleHarmonicNeighborCharge K young zeta 87)
  linarith only [hf,hn]

def rowGrid_88 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 195790976138 else
  if aa=35 then 199108788037 else
  if aa=36 then 202410030360 else
  if aa=37 then 205708617628 else
  if aa=38 then 208990099329 else
  if aa=39 then 212277646205 else
  if aa=40 then 215554754677 else
  if aa=41 then 218914476429 else
  if aa=42 then 109738701107 else
  if aa=43 then 110855594249 else
  if aa=44 then 112328185947 else
  if aa=45 then 113201670202 else
  if aa=46 then 113380523399 else
  if aa=47 then 114165253029 else
  if aa=48 then 117911565922 else
  if aa=49 then 117160050301 else
  if aa=50 then 116524257118 else
  if aa=51 then 115789254659 else
  if aa=52 then 115163511853 else
  if aa=53 then 114454854603 else
  if aa=54 then 113822581505 else
  if aa=55 then 112984174565 else
  if aa=56 then 112089469269 else
  if aa=57 then 111236661896 else
  if aa=58 then 114127445620 else
  if aa=59 then 114078406425 else
  if aa=60 then 113743412661 else
  if aa=61 then 113111860219 else
  if aa=62 then 111990324217 else
  if aa=63 then 110321033296 else
  if aa=64 then 108333975515 else
  if aa=65 then 106061128479 else
  if aa=66 then 103540201485 else
  if aa=67 then 100841952499 else
  if aa=68 then 97982282601 else
  if aa=69 then 94979281244 else
  if aa=70 then 91843659482 else
  if aa=71 then 88572821497 else
  if aa=72 then 85244815540 else
  if aa=73 then 81854666531 else
  if aa=74 then 78287790076 else
  if aa=75 then 74523091594 else
  if aa=76 then 70494195636 else
  if aa=77 then 66124218377 else
  if aa=78 then 61300102982 else
  if aa=79 then 55885972830 else
  if aa=80 then 49783894550 else
  if aa=81 then 42964830325 else
  if aa=82 then 35845630942 else
  if aa=83 then 29571833935 else
  if aa=84 then 23951118034 else
  if aa=85 then 18656464317 else
  if aa=86 then 12231054768 else
  if aa=87 then 9547449742 else
  0

theorem raw_first_cost_upper_88 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 88 ≤ (10034766832223/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 87) :
      rawRow 88 aa ≤ rowGrid_88 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 87 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_88,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 88 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 87,rowGrid_88 aa/10000000000)+(0/10000000000 : ℝ)=(10034766832223/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_88]
  change (∑ aa ∈ Finset.Icc 2 87,rawRow 88 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 88 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_88 : c ≤ coefficient profile 88 := by
  have hf := raw_first_cost_upper_88
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 88-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 88-1-
      (K*C/young 88)*(88 : ℝ)^2-(10034766832223/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 88 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 88-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 88-1-
      ((K*C/young 88)*(88 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 88+
        t 3*tripleHarmonicNeighborCharge K young zeta 88)
  linarith only [hf,hn]

def rowGrid_89 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 195790976138 else
  if aa=35 then 199108788037 else
  if aa=36 then 202410030360 else
  if aa=37 then 205708617628 else
  if aa=38 then 208990099329 else
  if aa=39 then 212277646205 else
  if aa=40 then 215554754677 else
  if aa=41 then 218914476429 else
  if aa=42 then 221811525646 else
  if aa=43 then 110085739740 else
  if aa=44 then 114123830099 else
  if aa=45 then 112301020223 else
  if aa=46 then 115898751897 else
  if aa=47 then 113560608104 else
  if aa=48 then 118395058329 else
  if aa=49 then 117911565922 else
  if aa=50 then 117160050301 else
  if aa=51 then 116524257118 else
  if aa=52 then 115789254659 else
  if aa=53 then 115163511853 else
  if aa=54 then 114454854603 else
  if aa=55 then 113822581505 else
  if aa=56 then 112984174565 else
  if aa=57 then 112089469269 else
  if aa=58 then 111236661896 else
  if aa=59 then 114127445620 else
  if aa=60 then 114078406425 else
  if aa=61 then 113743412661 else
  if aa=62 then 113111860219 else
  if aa=63 then 111990324217 else
  if aa=64 then 110321033296 else
  if aa=65 then 108333975515 else
  if aa=66 then 106061128479 else
  if aa=67 then 103540201485 else
  if aa=68 then 100841952499 else
  if aa=69 then 97982282601 else
  if aa=70 then 94979281244 else
  if aa=71 then 91843659482 else
  if aa=72 then 88572821497 else
  if aa=73 then 85244815540 else
  if aa=74 then 81854666531 else
  if aa=75 then 78287790076 else
  if aa=76 then 74523091594 else
  if aa=77 then 70494195636 else
  if aa=78 then 66124218377 else
  if aa=79 then 61300102982 else
  if aa=80 then 55885972830 else
  if aa=81 then 49783894550 else
  if aa=82 then 42964830325 else
  if aa=83 then 35845630942 else
  if aa=84 then 29571833935 else
  if aa=85 then 23951118034 else
  if aa=86 then 18656464317 else
  if aa=87 then 12231054768 else
  if aa=88 then 9547449742 else
  0

theorem raw_first_cost_upper_89 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 89 ≤ (10267273438328/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 88) :
      rawRow 89 aa ≤ rowGrid_89 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 88 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_89,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 89 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 88,rowGrid_89 aa/10000000000)+(0/10000000000 : ℝ)=(10267273438328/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_89]
  change (∑ aa ∈ Finset.Icc 2 88,rawRow 89 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 89 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_89 : c ≤ coefficient profile 89 := by
  have hf := raw_first_cost_upper_89
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 89-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 89-1-
      (K*C/young 89)*(89 : ℝ)^2-(10267273438328/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 89 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 89-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 89-1-
      ((K*C/young 89)*(89 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 89+
        t 3*tripleHarmonicNeighborCharge K young zeta 89)
  linarith only [hf,hn]

def rowGrid_90 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 195790976138 else
  if aa=35 then 199108788037 else
  if aa=36 then 202410030360 else
  if aa=37 then 205708617628 else
  if aa=38 then 208990099329 else
  if aa=39 then 212277646205 else
  if aa=40 then 215554754677 else
  if aa=41 then 218914476429 else
  if aa=42 then 221811525646 else
  if aa=43 then 222512984363 else
  if aa=44 then 113331278800 else
  if aa=45 then 114096230112 else
  if aa=46 then 114976643520 else
  if aa=47 then 116082836358 else
  if aa=48 then 117768011402 else
  if aa=49 then 118395058329 else
  if aa=50 then 117911565922 else
  if aa=51 then 117160050301 else
  if aa=52 then 116524257118 else
  if aa=53 then 115789254659 else
  if aa=54 then 115163511853 else
  if aa=55 then 114454854603 else
  if aa=56 then 113822581505 else
  if aa=57 then 112984174565 else
  if aa=58 then 112089469269 else
  if aa=59 then 111236661896 else
  if aa=60 then 114127445620 else
  if aa=61 then 114078406425 else
  if aa=62 then 113743412661 else
  if aa=63 then 113111860219 else
  if aa=64 then 111990324217 else
  if aa=65 then 110321033296 else
  if aa=66 then 108333975515 else
  if aa=67 then 106061128479 else
  if aa=68 then 103540201485 else
  if aa=69 then 100841952499 else
  if aa=70 then 97982282601 else
  if aa=71 then 94979281244 else
  if aa=72 then 91843659482 else
  if aa=73 then 88572821497 else
  if aa=74 then 85244815540 else
  if aa=75 then 81854666531 else
  if aa=76 then 78287790076 else
  if aa=77 then 74523091594 else
  if aa=78 then 70494195636 else
  if aa=79 then 66124218377 else
  if aa=80 then 61300102982 else
  if aa=81 then 55885972830 else
  if aa=82 then 49783894550 else
  if aa=83 then 42964830325 else
  if aa=84 then 35845630942 else
  if aa=85 then 29571833935 else
  if aa=86 then 23951118034 else
  if aa=87 then 18656464317 else
  if aa=88 then 12231054768 else
  if aa=89 then 9547449742 else
  0

theorem raw_first_cost_upper_90 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 90 ≤ (10500071472820/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 89) :
      rawRow 90 aa ≤ rowGrid_90 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 89 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_90,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 90 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 89,rowGrid_90 aa/10000000000)+(0/10000000000 : ℝ)=(10500071472820/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_90]
  change (∑ aa ∈ Finset.Icc 2 89,rawRow 90 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 90 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_90 : c ≤ coefficient profile 90 := by
  have hf := raw_first_cost_upper_90
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 90-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 90-1-
      (K*C/young 90)*(90 : ℝ)^2-(10500071472820/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 90 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 90-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 90-1-
      ((K*C/young 90)*(90 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 90+
        t 3*tripleHarmonicNeighborCharge K young zeta 90)
  linarith only [hf,hn]

def rowGrid_91 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 195790976138 else
  if aa=35 then 199108788037 else
  if aa=36 then 202410030360 else
  if aa=37 then 205708617628 else
  if aa=38 then 208990099329 else
  if aa=39 then 212277646205 else
  if aa=40 then 215554754677 else
  if aa=41 then 218914476429 else
  if aa=42 then 221811525646 else
  if aa=43 then 222512984363 else
  if aa=44 then 229073094546 else
  if aa=45 then 113303870486 else
  if aa=46 then 116814625107 else
  if aa=47 then 115159263376 else
  if aa=48 then 120383687830 else
  if aa=49 then 117768011402 else
  if aa=50 then 118395058329 else
  if aa=51 then 117911565922 else
  if aa=52 then 117160050301 else
  if aa=53 then 116524257118 else
  if aa=54 then 115789254659 else
  if aa=55 then 115163511853 else
  if aa=56 then 114454854603 else
  if aa=57 then 113822581505 else
  if aa=58 then 112984174565 else
  if aa=59 then 112089469269 else
  if aa=60 then 111236661896 else
  if aa=61 then 114127445620 else
  if aa=62 then 114078406425 else
  if aa=63 then 113743412661 else
  if aa=64 then 113111860219 else
  if aa=65 then 111990324217 else
  if aa=66 then 110321033296 else
  if aa=67 then 108333975515 else
  if aa=68 then 106061128479 else
  if aa=69 then 103540201485 else
  if aa=70 then 100841952499 else
  if aa=71 then 97982282601 else
  if aa=72 then 94979281244 else
  if aa=73 then 91843659482 else
  if aa=74 then 88572821497 else
  if aa=75 then 85244815540 else
  if aa=76 then 81854666531 else
  if aa=77 then 78287790076 else
  if aa=78 then 74523091594 else
  if aa=79 then 70494195636 else
  if aa=80 then 66124218377 else
  if aa=81 then 61300102982 else
  if aa=82 then 55885972830 else
  if aa=83 then 49783894550 else
  if aa=84 then 42964830325 else
  if aa=85 then 35845630942 else
  if aa=86 then 29571833935 else
  if aa=87 then 23951118034 else
  if aa=88 then 18656464317 else
  if aa=89 then 12231054768 else
  if aa=90 then 9547449742 else
  0

theorem raw_first_cost_upper_91 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 91 ≤ (10736319025375/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 90) :
      rawRow 91 aa ≤ rowGrid_91 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 90 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_91,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 91 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 90,rowGrid_91 aa/10000000000)+(0/10000000000 : ℝ)=(10736319025375/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_91]
  change (∑ aa ∈ Finset.Icc 2 90,rawRow 91 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 91 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_91 : c ≤ coefficient profile 91 := by
  have hf := raw_first_cost_upper_91
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 91-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 91-1-
      (K*C/young 91)*(91 : ℝ)^2-(10736319025375/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 91 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 91-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 91-1-
      ((K*C/young 91)*(91 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 91+
        t 3*tripleHarmonicNeighborCharge K young zeta 91)
  linarith only [hf,hn]

def rowGrid_92 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 195790976138 else
  if aa=35 then 199108788037 else
  if aa=36 then 202410030360 else
  if aa=37 then 205708617628 else
  if aa=38 then 208990099329 else
  if aa=39 then 212277646205 else
  if aa=40 then 215554754677 else
  if aa=41 then 218914476429 else
  if aa=42 then 221811525646 else
  if aa=43 then 222512984363 else
  if aa=44 then 229073094546 else
  if aa=45 then 229017694946 else
  if aa=46 then 116003387149 else
  if aa=47 then 117000164269 else
  if aa=48 then 119425896609 else
  if aa=49 then 120383687830 else
  if aa=50 then 117768011402 else
  if aa=51 then 118395058329 else
  if aa=52 then 117911565922 else
  if aa=53 then 117160050301 else
  if aa=54 then 116524257118 else
  if aa=55 then 115789254659 else
  if aa=56 then 115163511853 else
  if aa=57 then 114454854603 else
  if aa=58 then 113822581505 else
  if aa=59 then 112984174565 else
  if aa=60 then 112089469269 else
  if aa=61 then 111236661896 else
  if aa=62 then 114127445620 else
  if aa=63 then 114078406425 else
  if aa=64 then 113743412661 else
  if aa=65 then 113111860219 else
  if aa=66 then 111990324217 else
  if aa=67 then 110321033296 else
  if aa=68 then 108333975515 else
  if aa=69 then 106061128479 else
  if aa=70 then 103540201485 else
  if aa=71 then 100841952499 else
  if aa=72 then 97982282601 else
  if aa=73 then 94979281244 else
  if aa=74 then 91843659482 else
  if aa=75 then 88572821497 else
  if aa=76 then 85244815540 else
  if aa=77 then 81854666531 else
  if aa=78 then 78287790076 else
  if aa=79 then 74523091594 else
  if aa=80 then 70494195636 else
  if aa=81 then 66124218377 else
  if aa=82 then 61300102982 else
  if aa=83 then 55885972830 else
  if aa=84 then 49783894550 else
  if aa=85 then 42964830325 else
  if aa=86 then 35845630942 else
  if aa=87 then 29571833935 else
  if aa=88 then 23951118034 else
  if aa=89 then 18656464317 else
  if aa=90 then 12231054768 else
  if aa=91 then 9547449742 else
  0

theorem raw_first_cost_upper_92 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 92 ≤ (10972488409379/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 91) :
      rawRow 92 aa ≤ rowGrid_92 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 91 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_92,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 92 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 91,rowGrid_92 aa/10000000000)+(0/10000000000 : ℝ)=(10972488409379/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_92]
  change (∑ aa ∈ Finset.Icc 2 91,rawRow 92 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 92 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_92 : c ≤ coefficient profile 92 := by
  have hf := raw_first_cost_upper_92
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 92-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 92-1-
      (K*C/young 92)*(92 : ℝ)^2-(10972488409379/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 92 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 92-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 92-1-
      ((K*C/young 92)*(92 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 92+
        t 3*tripleHarmonicNeighborCharge K young zeta 92)
  linarith only [hf,hn]

def rowGrid_93 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 195790976138 else
  if aa=35 then 199108788037 else
  if aa=36 then 202410030360 else
  if aa=37 then 205708617628 else
  if aa=38 then 208990099329 else
  if aa=39 then 212277646205 else
  if aa=40 then 215554754677 else
  if aa=41 then 218914476429 else
  if aa=42 then 221811525646 else
  if aa=43 then 222512984363 else
  if aa=44 then 229073094546 else
  if aa=45 then 229017694946 else
  if aa=46 then 234474146532 else
  if aa=47 then 116187637805 else
  if aa=48 then 121335002601 else
  if aa=49 then 119425896609 else
  if aa=50 then 120383687830 else
  if aa=51 then 117768011402 else
  if aa=52 then 118395058329 else
  if aa=53 then 117911565922 else
  if aa=54 then 117160050301 else
  if aa=55 then 116524257118 else
  if aa=56 then 115789254659 else
  if aa=57 then 115163511853 else
  if aa=58 then 114454854603 else
  if aa=59 then 113822581505 else
  if aa=60 then 112984174565 else
  if aa=61 then 112089469269 else
  if aa=62 then 111236661896 else
  if aa=63 then 114127445620 else
  if aa=64 then 114078406425 else
  if aa=65 then 113743412661 else
  if aa=66 then 113111860219 else
  if aa=67 then 111990324217 else
  if aa=68 then 110321033296 else
  if aa=69 then 108333975515 else
  if aa=70 then 106061128479 else
  if aa=71 then 103540201485 else
  if aa=72 then 100841952499 else
  if aa=73 then 97982282601 else
  if aa=74 then 94979281244 else
  if aa=75 then 91843659482 else
  if aa=76 then 88572821497 else
  if aa=77 then 85244815540 else
  if aa=78 then 81854666531 else
  if aa=79 then 78287790076 else
  if aa=80 then 74523091594 else
  if aa=81 then 70494195636 else
  if aa=82 then 66124218377 else
  if aa=83 then 61300102982 else
  if aa=84 then 55885972830 else
  if aa=85 then 49783894550 else
  if aa=86 then 42964830325 else
  if aa=87 then 35845630942 else
  if aa=88 then 29571833935 else
  if aa=89 then 23951118034 else
  if aa=90 then 18656464317 else
  if aa=91 then 12231054768 else
  if aa=92 then 9547449742 else
  0

theorem raw_first_cost_upper_93 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 93 ≤ (11211481644899/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 92) :
      rawRow 93 aa ≤ rowGrid_93 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 92 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_93,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 93 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 92,rowGrid_93 aa/10000000000)+(0/10000000000 : ℝ)=(11211481644899/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_93]
  change (∑ aa ∈ Finset.Icc 2 92,rawRow 93 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 93 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_93 : c ≤ coefficient profile 93 := by
  have hf := raw_first_cost_upper_93
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 93-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 93-1-
      (K*C/young 93)*(93 : ℝ)^2-(11211481644899/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 93 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 93-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 93-1-
      ((K*C/young 93)*(93 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 93+
        t 3*tripleHarmonicNeighborCharge K young zeta 93)
  linarith only [hf,hn]

def rowGrid_94 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 195790976138 else
  if aa=35 then 199108788037 else
  if aa=36 then 202410030360 else
  if aa=37 then 205708617628 else
  if aa=38 then 208990099329 else
  if aa=39 then 212277646205 else
  if aa=40 then 215554754677 else
  if aa=41 then 218914476429 else
  if aa=42 then 221811525646 else
  if aa=43 then 222512984363 else
  if aa=44 then 229073094546 else
  if aa=45 then 229017694946 else
  if aa=46 then 234474146532 else
  if aa=47 then 234846566823 else
  if aa=48 then 120492372154 else
  if aa=49 then 121335002601 else
  if aa=50 then 119425896609 else
  if aa=51 then 120383687830 else
  if aa=52 then 117768011402 else
  if aa=53 then 118395058329 else
  if aa=54 then 117911565922 else
  if aa=55 then 117160050301 else
  if aa=56 then 116524257118 else
  if aa=57 then 115789254659 else
  if aa=58 then 115163511853 else
  if aa=59 then 114454854603 else
  if aa=60 then 113822581505 else
  if aa=61 then 112984174565 else
  if aa=62 then 112089469269 else
  if aa=63 then 111236661896 else
  if aa=64 then 114127445620 else
  if aa=65 then 114078406425 else
  if aa=66 then 113743412661 else
  if aa=67 then 113111860219 else
  if aa=68 then 111990324217 else
  if aa=69 then 110321033296 else
  if aa=70 then 108333975515 else
  if aa=71 then 106061128479 else
  if aa=72 then 103540201485 else
  if aa=73 then 100841952499 else
  if aa=74 then 97982282601 else
  if aa=75 then 94979281244 else
  if aa=76 then 91843659482 else
  if aa=77 then 88572821497 else
  if aa=78 then 85244815540 else
  if aa=79 then 81854666531 else
  if aa=80 then 78287790076 else
  if aa=81 then 74523091594 else
  if aa=82 then 70494195636 else
  if aa=83 then 66124218377 else
  if aa=84 then 61300102982 else
  if aa=85 then 55885972830 else
  if aa=86 then 49783894550 else
  if aa=87 then 42964830325 else
  if aa=88 then 35845630942 else
  if aa=89 then 29571833935 else
  if aa=90 then 23951118034 else
  if aa=91 then 18656464317 else
  if aa=92 then 12231054768 else
  if aa=93 then 9547449742 else
  0

theorem raw_first_cost_upper_94 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 94 ≤ (11450632946071/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 93) :
      rawRow 94 aa ≤ rowGrid_94 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 93 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_94,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 94 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 93,rowGrid_94 aa/10000000000)+(0/10000000000 : ℝ)=(11450632946071/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_94]
  change (∑ aa ∈ Finset.Icc 2 93,rawRow 94 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 94 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_94 : c ≤ coefficient profile 94 := by
  have hf := raw_first_cost_upper_94
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 94-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 94-1-
      (K*C/young 94)*(94 : ℝ)^2-(11450632946071/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 94 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 94-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 94-1-
      ((K*C/young 94)*(94 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 94+
        t 3*tripleHarmonicNeighborCharge K young zeta 94)
  linarith only [hf,hn]

def rowGrid_95 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 195790976138 else
  if aa=35 then 199108788037 else
  if aa=36 then 202410030360 else
  if aa=37 then 205708617628 else
  if aa=38 then 208990099329 else
  if aa=39 then 212277646205 else
  if aa=40 then 215554754677 else
  if aa=41 then 218914476429 else
  if aa=42 then 221811525646 else
  if aa=43 then 222512984363 else
  if aa=44 then 229073094546 else
  if aa=45 then 229017694946 else
  if aa=46 then 234474146532 else
  if aa=47 then 234846566823 else
  if aa=48 then 243547596486 else
  if aa=49 then 120492372154 else
  if aa=50 then 121335002601 else
  if aa=51 then 119425896609 else
  if aa=52 then 120383687830 else
  if aa=53 then 117768011402 else
  if aa=54 then 118395058329 else
  if aa=55 then 117911565922 else
  if aa=56 then 117160050301 else
  if aa=57 then 116524257118 else
  if aa=58 then 115789254659 else
  if aa=59 then 115163511853 else
  if aa=60 then 114454854603 else
  if aa=61 then 113822581505 else
  if aa=62 then 112984174565 else
  if aa=63 then 112089469269 else
  if aa=64 then 111236661896 else
  if aa=65 then 114127445620 else
  if aa=66 then 114078406425 else
  if aa=67 then 113743412661 else
  if aa=68 then 113111860219 else
  if aa=69 then 111990324217 else
  if aa=70 then 110321033296 else
  if aa=71 then 108333975515 else
  if aa=72 then 106061128479 else
  if aa=73 then 103540201485 else
  if aa=74 then 100841952499 else
  if aa=75 then 97982282601 else
  if aa=76 then 94979281244 else
  if aa=77 then 91843659482 else
  if aa=78 then 88572821497 else
  if aa=79 then 85244815540 else
  if aa=80 then 81854666531 else
  if aa=81 then 78287790076 else
  if aa=82 then 74523091594 else
  if aa=83 then 70494195636 else
  if aa=84 then 66124218377 else
  if aa=85 then 61300102982 else
  if aa=86 then 55885972830 else
  if aa=87 then 49783894550 else
  if aa=88 then 42964830325 else
  if aa=89 then 35845630942 else
  if aa=90 then 29571833935 else
  if aa=91 then 23951118034 else
  if aa=92 then 18656464317 else
  if aa=93 then 12231054768 else
  if aa=94 then 9547449742 else
  0

theorem raw_first_cost_upper_95 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 95 ≤ (11694180542557/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 94) :
      rawRow 95 aa ≤ rowGrid_95 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 94 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_95,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 95 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 94,rowGrid_95 aa/10000000000)+(0/10000000000 : ℝ)=(11694180542557/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_95]
  change (∑ aa ∈ Finset.Icc 2 94,rawRow 95 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 95 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_95 : c ≤ coefficient profile 95 := by
  have hf := raw_first_cost_upper_95
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 95-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 95-1-
      (K*C/young 95)*(95 : ℝ)^2-(11694180542557/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 95 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 95-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 95-1-
      ((K*C/young 95)*(95 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 95+
        t 3*tripleHarmonicNeighborCharge K young zeta 95)
  linarith only [hf,hn]

def rowGrid_96 (aa : ℕ) : ℝ :=
  if aa=2 then 308462740761 else
  if aa=3 then 48997865699 else
  if aa=4 then 47319169018 else
  if aa=5 then 56523557775 else
  if aa=6 then 65192610166 else
  if aa=7 then 73474013613 else
  if aa=8 then 79763534046 else
  if aa=9 then 85422131662 else
  if aa=10 then 91200455560 else
  if aa=11 then 96988454073 else
  if aa=12 then 102714246533 else
  if aa=13 then 108332674370 else
  if aa=14 then 113815662143 else
  if aa=15 then 119144268028 else
  if aa=16 then 124311394351 else
  if aa=17 then 129312688489 else
  if aa=18 then 134151371393 else
  if aa=19 then 138829718898 else
  if aa=20 then 143351787653 else
  if aa=21 then 147730410757 else
  if aa=22 then 151971106952 else
  if aa=23 then 156080789470 else
  if aa=24 then 160078235637 else
  if aa=25 then 163966304506 else
  if aa=26 then 167753931269 else
  if aa=27 then 171463128978 else
  if aa=28 then 175095374715 else
  if aa=29 then 178659591168 else
  if aa=30 then 182170452625 else
  if aa=31 then 185633853256 else
  if aa=32 then 189057601665 else
  if aa=33 then 192441093148 else
  if aa=34 then 195790976138 else
  if aa=35 then 199108788037 else
  if aa=36 then 202410030360 else
  if aa=37 then 205708617628 else
  if aa=38 then 208990099329 else
  if aa=39 then 212277646205 else
  if aa=40 then 215554754677 else
  if aa=41 then 218914476429 else
  if aa=42 then 221811525646 else
  if aa=43 then 222512984363 else
  if aa=44 then 229073094546 else
  if aa=45 then 229017694946 else
  if aa=46 then 234474146532 else
  if aa=47 then 234846566823 else
  if aa=48 then 243547596486 else
  if aa=49 then 243547596486 else
  if aa=50 then 120492372154 else
  if aa=51 then 121335002601 else
  if aa=52 then 119425896609 else
  if aa=53 then 120383687830 else
  if aa=54 then 117768011402 else
  if aa=55 then 118395058329 else
  if aa=56 then 117911565922 else
  if aa=57 then 117160050301 else
  if aa=58 then 116524257118 else
  if aa=59 then 115789254659 else
  if aa=60 then 115163511853 else
  if aa=61 then 114454854603 else
  if aa=62 then 113822581505 else
  if aa=63 then 112984174565 else
  if aa=64 then 112089469269 else
  if aa=65 then 111236661896 else
  if aa=66 then 114127445620 else
  if aa=67 then 114078406425 else
  if aa=68 then 113743412661 else
  if aa=69 then 113111860219 else
  if aa=70 then 111990324217 else
  if aa=71 then 110321033296 else
  if aa=72 then 108333975515 else
  if aa=73 then 106061128479 else
  if aa=74 then 103540201485 else
  if aa=75 then 100841952499 else
  if aa=76 then 97982282601 else
  if aa=77 then 94979281244 else
  if aa=78 then 91843659482 else
  if aa=79 then 88572821497 else
  if aa=80 then 85244815540 else
  if aa=81 then 81854666531 else
  if aa=82 then 78287790076 else
  if aa=83 then 74523091594 else
  if aa=84 then 70494195636 else
  if aa=85 then 66124218377 else
  if aa=86 then 61300102982 else
  if aa=87 then 55885972830 else
  if aa=88 then 49783894550 else
  if aa=89 then 42964830325 else
  if aa=90 then 35845630942 else
  if aa=91 then 29571833935 else
  if aa=92 then 23951118034 else
  if aa=93 then 18656464317 else
  if aa=94 then 12231054768 else
  if aa=95 then 9547449742 else
  0

theorem raw_first_cost_upper_96 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 96 ≤ (11937728139043/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 95) :
      rawRow 96 aa ≤ rowGrid_96 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 95 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_96,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 96 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 95,rowGrid_96 aa/10000000000)+(0/10000000000 : ℝ)=(11937728139043/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_96]
  change (∑ aa ∈ Finset.Icc 2 95,rawRow 96 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 96 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_96 : c ≤ coefficient profile 96 := by
  have hf := raw_first_cost_upper_96
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 96-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 96-1-
      (K*C/young 96)*(96 : ℝ)^2-(11937728139043/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 96 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 96-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 96-1-
      ((K*C/young 96)*(96 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 96+
        t 3*tripleHarmonicNeighborCharge K young zeta 96)
  linarith only [hf,hn]

theorem coefficient_finite_grid (d : ℕ) (hd : 5 ≤ d) (hD : d<97) : c ≤ coefficient profile d := by
  interval_cases d
  · exact coefficient_grid_5
  · exact coefficient_grid_6
  · exact coefficient_grid_7
  · exact coefficient_grid_8
  · exact coefficient_grid_9
  · exact coefficient_grid_10
  · exact coefficient_grid_11
  · exact coefficient_grid_12
  · exact coefficient_grid_13
  · exact coefficient_grid_14
  · exact coefficient_grid_15
  · exact coefficient_grid_16
  · exact coefficient_grid_17
  · exact coefficient_grid_18
  · exact coefficient_grid_19
  · exact coefficient_grid_20
  · exact coefficient_grid_21
  · exact coefficient_grid_22
  · exact coefficient_grid_23
  · exact coefficient_grid_24
  · exact coefficient_grid_25
  · exact coefficient_grid_26
  · exact coefficient_grid_27
  · exact coefficient_grid_28
  · exact coefficient_grid_29
  · exact coefficient_grid_30
  · exact coefficient_grid_31
  · exact coefficient_grid_32
  · exact coefficient_grid_33
  · exact coefficient_grid_34
  · exact coefficient_grid_35
  · exact coefficient_grid_36
  · exact coefficient_grid_37
  · exact coefficient_grid_38
  · exact coefficient_grid_39
  · exact coefficient_grid_40
  · exact coefficient_grid_41
  · exact coefficient_grid_42
  · exact coefficient_grid_43
  · exact coefficient_grid_44
  · exact coefficient_grid_45
  · exact coefficient_grid_46
  · exact coefficient_grid_47
  · exact coefficient_grid_48
  · exact coefficient_grid_49
  · exact coefficient_grid_50
  · exact coefficient_grid_51
  · exact coefficient_grid_52
  · exact coefficient_grid_53
  · exact coefficient_grid_54
  · exact coefficient_grid_55
  · exact coefficient_grid_56
  · exact coefficient_grid_57
  · exact coefficient_grid_58
  · exact coefficient_grid_59
  · exact coefficient_grid_60
  · exact coefficient_grid_61
  · exact coefficient_grid_62
  · exact coefficient_grid_63
  · exact coefficient_grid_64
  · exact coefficient_grid_65
  · exact coefficient_grid_66
  · exact coefficient_grid_67
  · exact coefficient_grid_68
  · exact coefficient_grid_69
  · exact coefficient_grid_70
  · exact coefficient_grid_71
  · exact coefficient_grid_72
  · exact coefficient_grid_73
  · exact coefficient_grid_74
  · exact coefficient_grid_75
  · exact coefficient_grid_76
  · exact coefficient_grid_77
  · exact coefficient_grid_78
  · exact coefficient_grid_79
  · exact coefficient_grid_80
  · exact coefficient_grid_81
  · exact coefficient_grid_82
  · exact coefficient_grid_83
  · exact coefficient_grid_84
  · exact coefficient_grid_85
  · exact coefficient_grid_86
  · exact coefficient_grid_87
  · exact coefficient_grid_88
  · exact coefficient_grid_89
  · exact coefficient_grid_90
  · exact coefficient_grid_91
  · exact coefficient_grid_92
  · exact coefficient_grid_93
  · exact coefficient_grid_94
  · exact coefficient_grid_95
  · exact coefficient_grid_96

end KLSConstantImprovement.QuarticM48FiniteCostGrid20261020
#print axioms KLSConstantImprovement.QuarticM48FiniteCostGrid20261020.coefficient_finite_grid
