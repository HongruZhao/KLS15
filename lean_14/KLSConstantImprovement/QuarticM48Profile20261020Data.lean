import KLSConstantImprovement.QuarticM48FiniteCostGrid20261020
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
namespace KLSConstantImprovement.QuarticM48Profile20261020Data
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def K : ℝ := 1216280801173157/100000000000000
def C : ℝ := 889110106060429/5000000000000000
def c : ℝ := 2639477099272473/100000000000000
def p : ℝ := 1281094000000000/1216280801173157
def tau : ℝ := 1/2
def alphaTail : ℝ := 42031259312359/100000000000000
def youngTail : ℝ := 154231370380099/5000000000000
def tTail : ℝ := 126653986822869/100000000000000
def tail_J : ℝ := -23037845100045426077435553623772531167291140917384658787842349809249698006296595176587242261036873855492696047609304223627350347769332763656113370341615969864195449785141826322387526091268760806739959117574688084819904662531603752400466569335247298462576417851372072282334255770522452515066835180304561227109082847176155147332857901355153029548468488484193939165320314006154540146768735648278959160676841546357013551245067496369569432558900359174332679941850526177889657057340132611412886973075099860968755584036542541233302426818298570746163000995556540633623632078798368690499686675711182936890963866531571179528293/20132976462024157815308587636827236175454015740784682172916375888564212025670838210213163053711674835175443264895276609927448487548262560173683777397203788346636998909783108115596152457165242642491667818799931393269084847107292602979799173304560847431743827760360269825608781647604273921375103067050654294614823312554042260603477274416915506492916115987772696300120257818203344852613058485013629167115514766551465802099533199272035894299905400479931566548732822959753575252450335148670787400115615556014111468148194414605017737759662180467124486214560523221225877108934699812777530522247545781324725550000000000000
def tail_q : ℝ := 12677303295580737796249666103416493585549555304331767617/89405983154634738648016564590000000000000000000000000000
def tail_b : ℝ := -95986845379919790249199156055381485491642813280022879486279649549744391/3774541404117585325436893885301566075869570000000000000000000000000000
def tail_a : ℝ := 280001066901433342705736464784870458060430761/244732403973026442264148734300000000000000
def tail_z : ℝ := -111688934136407527/100000000000000
def tail_J_upper : ℝ := -715177570223/625000000

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

theorem alpha_eq_tail (d : ℕ) (hd : 96 ≤ d) : alpha d=alphaTail := by
  simp only [alpha,show d≠2 by omega,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,show d≠20 by omega,show d≠21 by omega,show d≠22 by omega,show d≠23 by omega,show d≠24 by omega,show d≠25 by omega,show d≠26 by omega,show d≠27 by omega,show d≠28 by omega,show d≠29 by omega,show d≠30 by omega,show d≠31 by omega,show d≠32 by omega,show d≠33 by omega,show d≠34 by omega,show d≠35 by omega,show d≠36 by omega,show d≠37 by omega,show d≠38 by omega,show d≠39 by omega,show d≠40 by omega,show d≠41 by omega,show d≠42 by omega,show d≠43 by omega,show d≠44 by omega,show d≠45 by omega,show d≠46 by omega,show d≠47 by omega,show d≠48 by omega,show d≠49 by omega,show d≠50 by omega,show d≠51 by omega,show d≠52 by omega,show d≠53 by omega,show d≠54 by omega,show d≠55 by omega,show d≠56 by omega,show d≠57 by omega,show d≠58 by omega,show d≠59 by omega,show d≠60 by omega,show d≠61 by omega,show d≠62 by omega,show d≠63 by omega,show d≠64 by omega,show d≠65 by omega,show d≠66 by omega,show d≠67 by omega,show d≠68 by omega,show d≠69 by omega,show d≠70 by omega,show d≠71 by omega,show d≠72 by omega,show d≠73 by omega,show d≠74 by omega,show d≠75 by omega,show d≠76 by omega,show d≠77 by omega,show d≠78 by omega,show d≠79 by omega,show d≠80 by omega,show d≠81 by omega,show d≠82 by omega,show d≠83 by omega,show d≠84 by omega,show d≠85 by omega,show d≠86 by omega,show d≠87 by omega,show d≠88 by omega,show d≠89 by omega,show d≠90 by omega,show d≠91 by omega,show d≠92 by omega,show d≠93 by omega,show d≠94 by omega,show d≠95 by omega,ite_false]

theorem young_eq_tail (d : ℕ) (hd : 48 ≤ d) : young d=youngTail := by
  simp only [young,show d≠2 by omega,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,show d≠20 by omega,show d≠21 by omega,show d≠22 by omega,show d≠23 by omega,show d≠24 by omega,show d≠25 by omega,show d≠26 by omega,show d≠27 by omega,show d≠28 by omega,show d≠29 by omega,show d≠30 by omega,show d≠31 by omega,show d≠32 by omega,show d≠33 by omega,show d≠34 by omega,show d≠35 by omega,show d≠36 by omega,show d≠37 by omega,show d≠38 by omega,show d≠39 by omega,show d≠40 by omega,show d≠41 by omega,show d≠42 by omega,show d≠43 by omega,show d≠44 by omega,show d≠45 by omega,show d≠46 by omega,show d≠47 by omega,ite_false]

theorem t_eq_tail (d : ℕ) (hd : 48 ≤ d) : t d=tTail := by
  simp only [t,show d≠2 by omega,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,show d≠20 by omega,show d≠21 by omega,show d≠22 by omega,show d≠23 by omega,show d≠24 by omega,show d≠25 by omega,show d≠26 by omega,show d≠27 by omega,show d≠28 by omega,show d≠29 by omega,show d≠30 by omega,show d≠31 by omega,show d≠32 by omega,show d≠33 by omega,show d≠34 by omega,show d≠35 by omega,show d≠36 by omega,show d≠37 by omega,show d≠38 by omega,show d≠39 by omega,show d≠40 by omega,show d≠41 by omega,show d≠42 by omega,show d≠43 by omega,show d≠44 by omega,show d≠45 by omega,show d≠46 by omega,show d≠47 by omega,ite_false]

theorem alpha_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ alpha d := by
  by_cases hs:d ≤ 95
  · interval_cases d <;> norm_num [alpha,alphaTail]
  · rw [alpha_eq_tail d (by omega)];norm_num [alphaTail]

theorem alpha_lt_one (d : ℕ) (hd : 2 ≤ d) : alpha d<1 := by
  by_cases hs:d ≤ 95
  · interval_cases d <;> norm_num [alpha,alphaTail]
  · rw [alpha_eq_tail d (by omega)];norm_num [alphaTail]

theorem young_positive (d : ℕ) (hd : 2 ≤ d) : 0<young d := by
  by_cases hs:d ≤ 47
  · interval_cases d <;> norm_num [young,youngTail]
  · rw [young_eq_tail d (by omega)];norm_num [youngTail]

theorem t_positive (d : ℕ) (hd : 2 ≤ d) : 0<t d := by
  by_cases hs:d ≤ 47
  · interval_cases d <;> norm_num [t,tTail]
  · rw [t_eq_tail d (by omega)];norm_num [tTail]

theorem theta_nonneg (d : ℕ) (_hd : 3 ≤ d) : 0 ≤ theta d := by unfold theta;split_ifs <;> norm_num
theorem theta_le_one (d : ℕ) (_hd : 3 ≤ d) : theta d ≤ 1 := by unfold theta;split_ifs <;> norm_num
theorem lambda_nonneg (d : ℕ) (_hd : 2 ≤ d) : 0 ≤ lambda d := by unfold lambda;split_ifs <;> norm_num
theorem lambda_le_one (d : ℕ) (_hd : 2 ≤ d) : lambda d ≤ 1 := by unfold lambda;split_ifs <;> norm_num
theorem theta_eq_zero (d : ℕ) (hd : 49 ≤ d) : theta d=0 := by simp [theta,show ¬(3 ≤ d ∧ d ≤ 48) by omega]
theorem lambda_eq_zero (d : ℕ) (hd : 48 ≤ d) : lambda d=0 := by simp [lambda,show ¬(2 ≤ d ∧ d ≤ 47) by omega]
theorem zeta_eq_zero (d : ℕ) (hd : 48 ≤ d) : zeta d=0 := by
  simp only [zeta,show d≠3 by omega,show d≠4 by omega,show d≠5 by omega,show d≠6 by omega,show d≠7 by omega,show d≠8 by omega,show d≠9 by omega,show d≠10 by omega,show d≠11 by omega,show d≠12 by omega,show d≠13 by omega,show d≠14 by omega,show d≠15 by omega,show d≠16 by omega,show d≠17 by omega,show d≠18 by omega,show d≠19 by omega,show d≠20 by omega,show d≠21 by omega,show d≠22 by omega,show d≠23 by omega,show d≠24 by omega,show d≠25 by omega,show d≠26 by omega,show d≠27 by omega,show d≠28 by omega,show d≠29 by omega,show d≠30 by omega,show d≠31 by omega,show d≠32 by omega,show d≠33 by omega,show d≠34 by omega,show d≠35 by omega,show d≠36 by omega,show d≠37 by omega,show d≠38 by omega,show d≠39 by omega,show d≠40 by omega,show d≠41 by omega,show d≠42 by omega,show d≠43 by omega,show d≠44 by omega,show d≠45 by omega,show d≠46 by omega,show d≠47 by omega,ite_false]

theorem zeta_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ zeta d := by
  by_cases hs:d ≤ 47
  · interval_cases d <;> norm_num [zeta]
  · rw [zeta_eq_zero d (by omega)]

theorem zeta_cap (d : ℕ) (hd : 2 ≤ d) : tripleHarmonicRatio (d : ℝ)*zeta d<1 := by
  by_cases hs:d ≤ 47
  · interval_cases d <;> norm_num [tripleHarmonicRatio,TripleCreation.chargeRatio,zeta]
  · rw [zeta_eq_zero d (by omega)];norm_num

theorem lambda_boundary (d : ℕ) (hd : 2 ≤ d) (he : lambda d=1) : theta (d+1)=1 := by
  by_cases hs:d ≤ 47
  · have hh:3 ≤ d+1 ∧ d+1 ≤ 48:=by omega
    simp [theta,hh]
  · rw [lambda_eq_zero d (by omega)] at he
    norm_num at he

theorem t_floor (d : ℕ) (hd : 2 ≤ d) : tau ≤ t d := by
  by_cases hs:d ≤ 47
  · interval_cases d <;> norm_num [tau,t,tTail]
  · rw [t_eq_tail d (by omega)];norm_num [tau,tTail]

theorem terminal_payment (d : ℕ) (hd : 3 ≤ d) :
    ((d : ℝ)+PositiveEnergyWeightedDrift.kappa K young t lambda d)*(1-alpha d) ≤ (d : ℝ) := by
  by_cases hs:d ≤ 47
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


/- Exact table evaluations reused from the independent finite-grid certificate. -/
@[simp] theorem young_grid_eval_2 : young 2=(47737248705847/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_2
@[simp] theorem young_grid_eval_3 : young 3=(96249719816831/12500000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_3
@[simp] theorem young_grid_eval_4 : young 4=(1216171846541689/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_4
@[simp] theorem young_grid_eval_5 : young 5=(16338381295407/1250000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_5
@[simp] theorem young_grid_eval_6 : young 6=(279841807881177/20000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_6
@[simp] theorem young_grid_eval_7 : young 7=(1504891460389121/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_7
@[simp] theorem young_grid_eval_8 : young 8=(830771196175613/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_8
@[simp] theorem young_grid_eval_9 : young 9=(112357273956177/6250000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_9
@[simp] theorem young_grid_eval_10 : young 10=(1890203315662349/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_10
@[simp] theorem young_grid_eval_11 : young 11=(194959265566391/10000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_11
@[simp] theorem young_grid_eval_12 : young 12=(496446654664141/25000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_12
@[simp] theorem young_grid_eval_13 : young 13=(2007227544228853/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_13
@[simp] theorem young_grid_eval_14 : young 14=(1009860886017099/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_14
@[simp] theorem young_grid_eval_15 : young 15=(2026859260159927/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_15
@[simp] theorem young_grid_eval_16 : young 16=(2031118298854151/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_16
@[simp] theorem young_grid_eval_17 : young 17=(127089468869131/6250000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_17
@[simp] theorem young_grid_eval_18 : young 18=(2036610956108543/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_18
@[simp] theorem young_grid_eval_19 : young 19=(31885224159629/1562500000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_19
@[simp] theorem young_grid_eval_20 : young 20=(408750666979887/20000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_20
@[simp] theorem young_grid_eval_21 : young 21=(511470239643023/25000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_21
@[simp] theorem young_grid_eval_22 : young 22=(2046835459413187/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_22
@[simp] theorem young_grid_eval_23 : young 23=(2046266836386981/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_23
@[simp] theorem young_grid_eval_24 : young 24=(1021872406592839/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_24
@[simp] theorem young_grid_eval_25 : young 25=(2038040383073763/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_25
@[simp] theorem young_grid_eval_26 : young 26=(507140548610257/25000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_26
@[simp] theorem young_grid_eval_27 : young 27=(251838708359177/12500000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_27
@[simp] theorem young_grid_eval_28 : young 28=(996336838490147/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_28
@[simp] theorem young_grid_eval_29 : young 29=(1963824308746343/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_29
@[simp] theorem young_grid_eval_30 : young 30=(965824517646929/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_30
@[simp] theorem young_grid_eval_31 : young 31=(474106204961681/25000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_31
@[simp] theorem young_grid_eval_32 : young 32=(907457973106727/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_32
@[simp] theorem young_grid_eval_33 : young 33=(449168942240509/25000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_33
@[simp] theorem young_grid_eval_34 : young 34=(178003138020571/10000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_34
@[simp] theorem young_grid_eval_35 : young 35=(440839726333011/25000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_35
@[simp] theorem young_grid_eval_36 : young 36=(174423461531569/10000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_36
@[simp] theorem young_grid_eval_37 : young 37=(345378360046151/20000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_37
@[simp] theorem young_grid_eval_38 : young 38=(1709012577972521/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_38
@[simp] theorem young_grid_eval_39 : young 39=(16932254694907/1000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_39
@[simp] theorem young_grid_eval_40 : young 40=(838290722874359/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_40
@[simp] theorem young_grid_eval_41 : young 41=(332287981907409/20000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_41
@[simp] theorem young_grid_eval_42 : young 42=(1646463774965093/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_42
@[simp] theorem young_grid_eval_43 : young 43=(816290421765723/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_43
@[simp] theorem young_grid_eval_44 : young 44=(16210494892167/1000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_44
@[simp] theorem young_grid_eval_45 : young 45=(1608541182563541/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_45
@[simp] theorem young_grid_eval_46 : young 46=(199528007702663/12500000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_46
@[simp] theorem young_grid_eval_47 : young 47=(791312554790569/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.young_eval_47
@[simp] theorem t_grid_eval_2 : t 2=(1 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_2
@[simp] theorem t_grid_eval_3 : t 3=(314771609294857/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_3
@[simp] theorem t_grid_eval_4 : t 4=(81484614789271/12500000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_4
@[simp] theorem t_grid_eval_5 : t 5=(136431053220889/25000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_5
@[simp] theorem t_grid_eval_6 : t 6=(236577995555449/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_6
@[simp] theorem t_grid_eval_7 : t 7=(41982563030853/10000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_7
@[simp] theorem t_grid_eval_8 : t 8=(96680376706541/25000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_8
@[simp] theorem t_grid_eval_9 : t 9=(45138000943411/12500000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_9
@[simp] theorem t_grid_eval_10 : t 10=(5284765624029/1562500000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_10
@[simp] theorem t_grid_eval_11 : t 11=(19877542622767/6250000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_11
@[simp] theorem t_grid_eval_12 : t 12=(1876947156631/625000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_12
@[simp] theorem t_grid_eval_13 : t 13=(142368284802563/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_13
@[simp] theorem t_grid_eval_14 : t 14=(271019589882751/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_14
@[simp] theorem t_grid_eval_15 : t 15=(258898515108441/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_15
@[simp] theorem t_grid_eval_16 : t 16=(248137141709843/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_16
@[simp] theorem t_grid_eval_17 : t 17=(14908762259003/6250000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_17
@[simp] theorem t_grid_eval_18 : t 18=(229936330547581/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_18
@[simp] theorem t_grid_eval_19 : t 19=(13886739417639/6250000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_19
@[simp] theorem t_grid_eval_20 : t 20=(53794714703629/25000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_20
@[simp] theorem t_grid_eval_21 : t 21=(208801112228601/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_21
@[simp] theorem t_grid_eval_22 : t 22=(25371824532013/12500000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_22
@[simp] theorem t_grid_eval_23 : t 23=(197630177172593/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_23
@[simp] theorem t_grid_eval_24 : t 24=(19269499038047/10000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_24
@[simp] theorem t_grid_eval_25 : t 25=(47031422353803/25000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_25
@[simp] theorem t_grid_eval_26 : t 26=(183878099564141/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_26
@[simp] theorem t_grid_eval_27 : t 27=(35980066688253/20000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_27
@[simp] theorem t_grid_eval_28 : t 28=(176168411794857/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_28
@[simp] theorem t_grid_eval_29 : t 29=(10790868361169/6250000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_29
@[simp] theorem t_grid_eval_30 : t 30=(21165804903837/12500000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_30
@[simp] theorem t_grid_eval_31 : t 31=(83083644321913/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_31
@[simp] theorem t_grid_eval_32 : t 32=(81579036770849/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_32
@[simp] theorem t_grid_eval_33 : t 33=(40072358730117/25000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_33
@[simp] theorem t_grid_eval_34 : t 34=(157546965056723/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_34
@[simp] theorem t_grid_eval_35 : t 35=(154921710790449/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_35
@[simp] theorem t_grid_eval_36 : t 36=(19049373455707/12500000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_36
@[simp] theorem t_grid_eval_37 : t 37=(149951297285469/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_37
@[simp] theorem t_grid_eval_38 : t 38=(36899205004317/25000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_38
@[simp] theorem t_grid_eval_39 : t 39=(145310986001539/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_39
@[simp] theorem t_grid_eval_40 : t 40=(35775450792419/25000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_40
@[simp] theorem t_grid_eval_41 : t 41=(140905592810501/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_41
@[simp] theorem t_grid_eval_42 : t 42=(139065244631929/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_42
@[simp] theorem t_grid_eval_43 : t 43=(138626849864259/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_43
@[simp] theorem t_grid_eval_44 : t 44=(134656905636521/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_44
@[simp] theorem t_grid_eval_45 : t 45=(67344739635293/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_45
@[simp] theorem t_grid_eval_46 : t 46=(65777559130353/50000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_46
@[simp] theorem t_grid_eval_47 : t 47=(131346497814977/100000000000000 : ℝ) := QuarticM48FiniteCostGrid20261020.t_eval_47

def interceptGridOne (b : ℕ) : ℝ :=
  if b=2 then 9547449742 else
  if b=3 then 12231054768 else
  if b=4 then 18656464317 else
  if b=5 then 23951118034 else
  if b=6 then 29571833935 else
  if b=7 then 35845630942 else
  if b=8 then 42964830325 else
  if b=9 then 49783894550 else
  if b=10 then 55885972830 else
  if b=11 then 61300102982 else
  if b=12 then 66124218377 else
  if b=13 then 70494195636 else
  if b=14 then 74523091594 else
  if b=15 then 78287790076 else
  if b=16 then 81854666531 else
  if b=17 then 85244815540 else
  if b=18 then 88572821497 else
  if b=19 then 91843659482 else
  if b=20 then 94979281244 else
  if b=21 then 97982282601 else
  if b=22 then 100841952499 else
  if b=23 then 103540201485 else
  if b=24 then 106061128479 else
  if b=25 then 108333975515 else
  if b=26 then 110321033296 else
  if b=27 then 111990324217 else
  if b=28 then 113111860219 else
  if b=29 then 113743412661 else
  if b=30 then 114078406425 else
  if b=31 then 114127445620 else
  if b=32 then 111236661896 else
  if b=33 then 112089469269 else
  if b=34 then 112984174565 else
  if b=35 then 113822581505 else
  if b=36 then 114454854603 else
  if b=37 then 115163511853 else
  if b=38 then 115789254659 else
  if b=39 then 116524257118 else
  if b=40 then 117160050301 else
  if b=41 then 117911565922 else
  if b=42 then 118395058329 else
  if b=43 then 117768011402 else
  if b=44 then 120383687830 else
  if b=45 then 119425896609 else
  if b=46 then 121335002601 else
  if b=47 then 120492372154 else
  0

def interceptGridTwo (b : ℕ) : ℝ :=
  if b=2 then 308462740761 else
  if b=3 then 48997865699 else
  if b=4 then 47319169018 else
  if b=5 then 56523557775 else
  if b=6 then 65192610166 else
  if b=7 then 73474013613 else
  if b=8 then 79763534046 else
  if b=9 then 85422131662 else
  if b=10 then 91200455560 else
  if b=11 then 96988454073 else
  if b=12 then 102714246533 else
  if b=13 then 108332674370 else
  if b=14 then 113815662143 else
  if b=15 then 119144268028 else
  if b=16 then 124311394351 else
  if b=17 then 129312688489 else
  if b=18 then 134151371393 else
  if b=19 then 138829718898 else
  if b=20 then 143351787653 else
  if b=21 then 147730410757 else
  if b=22 then 151971106952 else
  if b=23 then 156080789470 else
  if b=24 then 160078235637 else
  if b=25 then 163966304506 else
  if b=26 then 167753931269 else
  if b=27 then 171463128978 else
  if b=28 then 175095374715 else
  if b=29 then 178659591168 else
  if b=30 then 182170452625 else
  if b=31 then 185633853256 else
  if b=32 then 189057601665 else
  if b=33 then 192441093148 else
  if b=34 then 195790976138 else
  if b=35 then 199108788037 else
  if b=36 then 202410030360 else
  if b=37 then 205708617628 else
  if b=38 then 208990099329 else
  if b=39 then 212277646205 else
  if b=40 then 215554754677 else
  if b=41 then 218914476429 else
  if b=42 then 221811525646 else
  if b=43 then 222512984363 else
  if b=44 then 229073094546 else
  if b=45 then 229017694946 else
  if b=46 then 234474146532 else
  if b=47 then 234846566823 else
  0

def tail_intercept_expression : ℝ :=
  PositiveEnergyWeightTail.ratioPrefix young t 48+
    (∑ b ∈ Finset.Icc 2 47,youngTail/t b)-94*(youngTail/tTail)

theorem tail_intercept_upper : tail_intercept_expression ≤ tail_J_upper := by
  have h1 (j : ℕ) (hj : j ∈ Finset.Icc 2 47) :
      young j/t j ≤ interceptGridOne j/10000000000 := by
    have hlo : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have hhi : j ≤ 47 := (Finset.mem_Icc.mp hj).2
    interval_cases j <;> norm_num [interceptGridOne]
  have h2 (j : ℕ) (hj : j ∈ Finset.Icc 2 47) :
      youngTail/t j ≤ interceptGridTwo j/10000000000 := by
    have hlo : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have hhi : j ≤ 47 := (Finset.mem_Icc.mp hj).2
    interval_cases j <;> norm_num [interceptGridTwo,youngTail]
  have hs1 := Finset.sum_le_sum h1
  have hs2 := Finset.sum_le_sum h2
  have hn : -94*(youngTail/tTail) ≤ (-22893474069639/10000000000 : ℝ) := by
    norm_num [youngTail,tTail]
  have hg : (∑ j ∈ Finset.Icc 2 47,interceptGridOne j/10000000000)+
      (∑ j ∈ Finset.Icc 2 47,interceptGridTwo j/10000000000)+
        (-22893474069639/10000000000 : ℝ)=tail_J_upper := by
    norm_num [sum_interval_two,Finset.sum_range_succ,interceptGridOne,interceptGridTwo,tail_J_upper]
  unfold tail_intercept_expression PositiveEnergyWeightTail.ratioPrefix
  linarith only [hs1,hs2,hn,hg]

theorem first_cost_tail_upper (d : ℕ) (hd : 97 ≤ d) :
    PositiveEnergyWeightedDrift.firstCost young t theta lambda d ≤
      (youngTail/tTail)*(d : ℝ)+tail_J_upper := by
  have hh:=PositiveEnergyWeightTailPrefix.firstCost_tail young t theta lambda youngTail tTail
    (by norm_num [tTail]) 48 48 (by norm_num) (by norm_num) (by norm_num)
    young_eq_tail (fun j hj=>t_eq_tail j (by omega)) d (by omega)
    (theta_eq_zero d (by omega)) (lambda_eq_zero (d-1) (by omega))
  have he : PositiveEnergyWeightedDrift.firstCost young t theta lambda d=
      (youngTail/tTail)*(d : ℝ)+tail_intercept_expression := by
    convert hh using 1
    norm_num only [tail_intercept_expression,PositiveEnergyWeightTailPrefix.ratioPrefix]
  rw [he]
  exact add_le_add (le_refl _) tail_intercept_upper

theorem raw_first_cost_tail_upper (d : ℕ) (hd : 97 ≤ d) :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta d ≤
      (youngTail/tTail)*(d : ℝ)+tail_J_upper := by
  rw [TriplePositiveEnergyFirstCostTail.rawFirstCost_eq_of_zero young t theta lambda zeta d
    (by omega) (zeta_eq_zero (d-2) (by omega))]
  exact first_cost_tail_upper d hd

theorem tail_noise_loss (d : ℕ) (hd : 97 ≤ d) :
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda d=generalResidualGeneratorLoss alphaTail d := by
  have hd3:3 ≤ d:=by omega
  have hd2:d≠2:=by omega
  have hr:(97:ℝ) ≤ d:=by exact_mod_cast hd
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

theorem coefficient_finite (d : ℕ) (hd : 5 ≤ d) (hD : d<97) : c ≤ coefficient profile d := by
  exact QuarticM48FiniteCostGrid20261020.coefficient_finite_grid d hd hD

theorem coefficient_tail_lower (d : ℕ) (hd : 97 ≤ d) :
    tail_q*(d : ℝ)^3+tail_b*(d : ℝ)^2+tail_a*(d : ℝ)+tail_z ≤
      ((d : ℝ)-1)*(coefficient profile d-c) := by
  have hr : (97 : ℝ) ≤ d := by exact_mod_cast hd
  have hm : (d : ℝ)-1≠0 := by linarith
  let lowerValue : ℝ := K*alphaTail*(d : ℝ)^2-
    generalResidualGeneratorLoss alphaTail d-1-(K*C/youngTail)*(d : ℝ)^2-
      ((youngTail/tTail)*(d : ℝ)+tail_J_upper)
  have hbound : lowerValue ≤ coefficient profile d := by
    have hf := raw_first_cost_tail_upper d hd
    change lowerValue ≤ TriplePositiveEnergyWeightedGenerator.coefficient K C young t alpha theta lambda zeta d
    unfold TriplePositiveEnergyWeightedGenerator.coefficient PositiveEnergyWeightedGenerator.incoming
      TriplePositiveEnergyWeightedGenerator.cost
    rw [t_eq_tail d (by omega),t_eq_tail (d-1) (by omega),
      alpha_eq_tail (d-1) (by omega),tail_noise_loss d hd,young_eq_tail d (by omega),
      ite_eq_left (by omega : 3 ≤ d)]
    rw [show tripleHarmonicNeighborCharge K young zeta d=0 by
      simp [tripleHarmonicNeighborCharge,zeta_eq_zero d (by omega)]]
    have ht : tTail≠0 := by norm_num [tTail]
    simp only [div_self ht,mul_one,mul_zero,add_zero]
    dsimp only [lowerValue]
    linarith only [hf]
  have hid : ((d : ℝ)-1)*(lowerValue-c)=
      tail_q*(d : ℝ)^3+tail_b*(d : ℝ)^2+tail_a*(d : ℝ)+tail_z := by
    dsimp only [lowerValue]
    norm_num [generalResidualGeneratorLoss,generalResidualA,K,C,c,alphaTail,
      youngTail,tTail,tail_J_upper,tail_q,tail_b,tail_a,tail_z]
    field_simp [hm] <;> ring
  rw [←hid]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hbound c) (by linarith)

theorem tail_Taylor_positive :
    0 < tail_q*(97 : ℝ)^3+tail_b*97^2+tail_a*97+tail_z ∧
      0 < 3*tail_q*97^2+2*tail_b*97+tail_a ∧
      0 < 3*tail_q*97+tail_b ∧ 0 < tail_q := by
  norm_num [tail_q,tail_b,tail_a,tail_z]

theorem coefficient_lower (d : ℕ) (hd : 5 ≤ d) : c ≤ coefficient profile d := by
  by_cases hs:d<97
  · exact coefficient_finite d hd hs
  · have hdt : 97 ≤ d := by omega
    have hr : (97 : ℝ) ≤ d := by exact_mod_cast hdt
    have hp:=ParameterizedWeightedBudget.cubic_nonneg_on_tail tail_q tail_b tail_a tail_z 97 d hr
      (by norm_num [tail_q]) (by norm_num [tail_q,tail_b]) (by norm_num [tail_q,tail_b,tail_a])
      (by norm_num [tail_q,tail_b,tail_a,tail_z])
    have hn : 0 ≤ ((d : ℝ)-1)*(coefficient profile d-c) :=
      hp.trans (coefficient_tail_lower d hdt)
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by linarith : 0 < (d : ℝ)-1)).mp hn)

theorem head_value : head profile=(46288351338985068018613960294247008943171681721201028732367873/1588940396035004289648636596949642935823525817500000000000000 : ℝ) := by
  norm_num [head,profile,TriplePositiveEnergyWeightedGenerator.head,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]
theorem coefficient_three : coefficient profile 3=(-761442672217555193363796541984650023584756315340128268148743881497609008534352685355074952640463863710233/14295150629013296663290894058702708620257255226475790110762115727219561061996686440015960000000000000000 : ℝ) := by
  norm_num [coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]

theorem coefficient_four : coefficient profile 4=(-239873884541710510277618369631252760413914441466378675284688872856225578747652741339273946642640567146272498507486337182499622363/66652388106119072107803078851308361336917530797766256893480696051547579673738873835779665545818989391250000000000000000000000000 : ℝ) := by
  norm_num [sum_interval_two,Finset.sum_range_succ,coefficient,profile,TriplePositiveEnergyWeightedGenerator.coefficient,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,TriplePositiveEnergyWeightedGenerator.cost,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedDrift.firstCost,selectiveTriangleFraction,thetaTriangleCoefficient,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,SignedQuadraticReservedNoise.quadraticNoiseLoss,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,K,C,c,young,youngTail,t,tTail,alpha,alphaTail,theta,lambda,TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost,TriplePositiveEnergyWeightedBudgetDrift.extra,TriplePositiveEnergyWeightedDrift.selectedFirstCost,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,selectedHarmonicLambda,tripleHarmonicRatio,tripleHarmonicNeighborCharge,TripleCreation.chargeRatio,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier,zeta]


end KLSConstantImprovement.QuarticM48Profile20261020Data
#print axioms KLSConstantImprovement.QuarticM48Profile20261020Data.coefficient_lower
#print axioms KLSConstantImprovement.QuarticM48Profile20261020Data.head_value
#print axioms KLSConstantImprovement.QuarticM48Profile20261020Data.coefficient_three

#print axioms KLSConstantImprovement.QuarticM48Profile20261020Data.coefficient_four
