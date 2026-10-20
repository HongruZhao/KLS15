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
namespace KLSConstantImprovement.QuarticM32FiniteCostGrid20261020
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def K : ℝ := 122144150200807/10000000000000

def C : ℝ := 702609291531669/5000000000000000

def c : ℝ := 526963084307017/20000000000000

def alphaTail : ℝ := 8347532273131/20000000000000

def youngTail : ℝ := 567235711520317/25000000000000

def tTail : ℝ := 16487388560167/12500000000000

def alpha (d : ℕ) : ℝ :=
  if d=2 then 1/3 else
  if d=3 then 24724140004971/50000000000000 else
  if d=4 then 23208570349273/50000000000000 else
  if d=5 then 8897796536719/20000000000000 else
  if d=6 then 43445526853969/100000000000000 else
  if d=7 then 21454036847499/50000000000000 else
  if d=8 then 41711757634379/100000000000000 else
  if d=9 then 1276211093843/3125000000000 else
  if d=10 then 20174999447269/50000000000000 else
  if d=11 then 10021927507097/25000000000000 else
  if d=12 then 19980414351471/50000000000000 else
  if d=13 then 19957642282881/50000000000000 else
  if d=14 then 39918352219317/100000000000000 else
  if d=15 then 39950123731977/100000000000000 else
  if d=16 then 39998240094149/100000000000000 else
  if d=17 then 20027655436007/50000000000000 else
  if d=18 then 40120336653817/100000000000000 else
  if d=19 then 20095534968541/50000000000000 else
  if d=20 then 20133437734939/50000000000000 else
  if d=21 then 4034843395603/10000000000000 else
  if d=22 then 10109384148453/25000000000000 else
  if d=23 then 810739799393/2000000000000 else
  if d=24 then 20325220819999/50000000000000 else
  if d=25 then 40783498742711/100000000000000 else
  if d=26 then 40942449853857/100000000000000 else
  if d=27 then 1645368717449/4000000000000 else
  if d=28 then 20618258463193/50000000000000 else
  if d=29 then 8238662236523/20000000000000 else
  if d=30 then 41147561933571/100000000000000 else
  if d=31 then 41101368037837/100000000000000 else
  if d=32 then 43334275391403/100000000000000 else
  if d=33 then 8642495915899/20000000000000 else
  if d=34 then 21551804594659/50000000000000 else
  if d=35 then 8601511366129/20000000000000 else
  if d=36 then 42921061208959/100000000000000 else
  if d=37 then 10710411360813/25000000000000 else
  if d=38 then 85534823171/200000000000 else
  if d=39 then 21348692622077/50000000000000 else
  if d=40 then 213154441107/500000000000 else
  if d=41 then 42567375477447/100000000000000 else
  if d=42 then 8501285832589/20000000000000 else
  if d=43 then 10611936289459/25000000000000 else
  if d=44 then 10597779053483/25000000000000 else
  if d=45 then 42336415215163/100000000000000 else
  if d=46 then 5285447497169/12500000000000 else
  if d=47 then 42232596955241/100000000000000 else
  if d=48 then 42183494588123/100000000000000 else
  if d=49 then 21068166838533/50000000000000 else
  if d=50 then 42091198846833/100000000000000 else
  if d=51 then 42048191434409/100000000000000 else
  if d=52 then 4200742369061/10000000000000 else
  if d=53 then 41969014095011/100000000000000 else
  if d=54 then 10483270872801/25000000000000 else
  if d=55 then 10474938008313/25000000000000 else
  if d=56 then 41869135633079/100000000000000 else
  if d=57 then 41841343687007/100000000000000 else
  if d=58 then 10454119035609/25000000000000 else
  if d=59 then 20897340389713/50000000000000 else
  if d=60 then 20888088415413/50000000000000 else
  if d=61 then 41761184177999/100000000000000 else
  if d=62 then 20874961535823/50000000000000 else
  if d=63 then 8348382435197/20000000000000 else
  alphaTail


def young (d : ℕ) : ℝ :=
  if d=2 then 95193002405431/100000000000000 else
  if d=3 then 60361814752637/10000000000000 else
  if d=4 then 470159457903553/50000000000000 else
  if d=5 then 25554367557219/2500000000000 else
  if d=6 then 1102479731580301/100000000000000 else
  if d=7 then 236553062568137/20000000000000 else
  if d=8 then 1289045379687367/100000000000000 else
  if d=9 then 342542283954801/25000000000000 else
  if d=10 then 1423515181452149/100000000000000 else
  if d=11 then 291069320793913/20000000000000 else
  if d=12 then 294134663816097/20000000000000 else
  if d=13 then 368578410409753/25000000000000 else
  if d=14 then 1469572893548997/100000000000000 else
  if d=15 then 58346416357919/4000000000000 else
  if d=16 then 289522585659173/20000000000000 else
  if d=17 then 358078859792039/25000000000000 else
  if d=18 then 282652980140789/20000000000000 else
  if d=19 then 1391207860065547/100000000000000 else
  if d=20 then 1366859091679337/100000000000000 else
  if d=21 then 1340887630262589/100000000000000 else
  if d=22 then 10511216169161/800000000000 else
  if d=23 then 257290325235787/20000000000000 else
  if d=24 then 629434388586049/50000000000000 else
  if d=25 then 1232730784495239/100000000000000 else
  if d=26 then 241565644342809/20000000000000 else
  if d=27 then 59227088301033/5000000000000 else
  if d=28 then 1868227441031/160000000000 else
  if d=29 then 1154889676470491/100000000000000 else
  if d=30 then 1140451378078667/100000000000000 else
  if d=31 then 561957391821949/50000000000000 else
  youngTail


def t (d : ℕ) : ℝ :=
  if d=2 then 1 else
  if d=3 then 495074302387353/100000000000000 else
  if d=4 then 256475451648929/50000000000000 else
  if d=5 then 431455417410153/100000000000000 else
  if d=6 then 375828697065803/100000000000000 else
  if d=7 then 167508622498929/50000000000000 else
  if d=8 then 62143078345047/20000000000000 else
  if d=9 then 290967381044679/100000000000000 else
  if d=10 then 273378191508407/100000000000000 else
  if d=11 then 4029599321999/1562500000000 else
  if d=12 then 244317269912887/100000000000000 else
  if d=13 then 232405484198257/100000000000000 else
  if d=14 then 110960691530321/50000000000000 else
  if d=15 then 42529996329769/20000000000000 else
  if d=16 then 204404356722221/100000000000000 else
  if d=17 then 2462815971153/1250000000000 else
  if d=18 then 190378247442463/100000000000000 else
  if d=19 then 92174058101813/50000000000000 else
  if d=20 then 35767508206187/20000000000000 else
  if d=21 then 34752780389999/20000000000000 else
  if d=22 then 6762262568989/4000000000000 else
  if d=23 then 82327279289743/50000000000000 else
  if d=24 then 160504653539363/100000000000000 else
  if d=25 then 156559758366081/100000000000000 else
  if d=26 then 19097158953083/12500000000000 else
  if d=27 then 149117946189779/100000000000000 else
  if d=28 then 145991502813431/100000000000000 else
  if d=29 then 143530679528699/100000000000000 else
  if d=30 then 141197070597487/100000000000000 else
  if d=31 then 17372454819443/12500000000000 else
  tTail


def theta (d : ℕ) : ℝ := if 3 ≤ d ∧ d ≤ 32 then 1 else 0

def lambda (d : ℕ) : ℝ := if 2 ≤ d ∧ d ≤ 31 then 1 else 0


def zeta (d : ℕ) : ℝ :=
  if d=3 then 142857/100000 else
  if d=4 then 92256280166883/50000000000000 else
  if d=5 then 208323806383/208000000000 else
  if d=6 then 148419367937533/200000000000000 else
  if d=7 then 143702293408233/237500000000000 else
  if d=8 then 13602854301207/27500000000000 else
  if d=9 then 200642343932019/500000000000000 else
  if d=10 then 44869228225019/140000000000000 else
  if d=11 then 191782300934939/775000000000000 else
  if d=12 then 152362441384517/850000000000000 else
  if d=13 then 535605283941/4625000000000 else
  if d=14 then 1413368152147/25000000000000 else
  if d=15 then 24149122319/21500000000000 else
  if d=16 then 0 else
  if d=17 then 0 else
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
@[simp] theorem alpha_eval_3 : alpha 3=(24724140004971/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_4 : alpha 4=(23208570349273/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_5 : alpha 5=(8897796536719/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_6 : alpha 6=(43445526853969/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_7 : alpha 7=(21454036847499/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_8 : alpha 8=(41711757634379/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_9 : alpha 9=(1276211093843/3125000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_10 : alpha 10=(20174999447269/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_11 : alpha 11=(10021927507097/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_12 : alpha 12=(19980414351471/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_13 : alpha 13=(19957642282881/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_14 : alpha 14=(39918352219317/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_15 : alpha 15=(39950123731977/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_16 : alpha 16=(39998240094149/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_17 : alpha 17=(20027655436007/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_18 : alpha 18=(40120336653817/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_19 : alpha 19=(20095534968541/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_20 : alpha 20=(20133437734939/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_21 : alpha 21=(4034843395603/10000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_22 : alpha 22=(10109384148453/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_23 : alpha 23=(810739799393/2000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_24 : alpha 24=(20325220819999/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_25 : alpha 25=(40783498742711/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_26 : alpha 26=(40942449853857/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_27 : alpha 27=(1645368717449/4000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_28 : alpha 28=(20618258463193/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_29 : alpha 29=(8238662236523/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_30 : alpha 30=(41147561933571/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_31 : alpha 31=(41101368037837/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_32 : alpha 32=(43334275391403/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_33 : alpha 33=(8642495915899/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_34 : alpha 34=(21551804594659/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_35 : alpha 35=(8601511366129/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_36 : alpha 36=(42921061208959/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_37 : alpha 37=(10710411360813/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_38 : alpha 38=(85534823171/200000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_39 : alpha 39=(21348692622077/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_40 : alpha 40=(213154441107/500000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_41 : alpha 41=(42567375477447/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_42 : alpha 42=(8501285832589/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_43 : alpha 43=(10611936289459/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_44 : alpha 44=(10597779053483/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_45 : alpha 45=(42336415215163/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_46 : alpha 46=(5285447497169/12500000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_47 : alpha 47=(42232596955241/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_48 : alpha 48=(42183494588123/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_49 : alpha 49=(21068166838533/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_50 : alpha 50=(42091198846833/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_51 : alpha 51=(42048191434409/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_52 : alpha 52=(4200742369061/10000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_53 : alpha 53=(41969014095011/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_54 : alpha 54=(10483270872801/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_55 : alpha 55=(10474938008313/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_56 : alpha 56=(41869135633079/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_57 : alpha 57=(41841343687007/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_58 : alpha 58=(10454119035609/25000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_59 : alpha 59=(20897340389713/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_60 : alpha 60=(20888088415413/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_61 : alpha 61=(41761184177999/100000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_62 : alpha 62=(20874961535823/50000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_63 : alpha 63=(8348382435197/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_64 : alpha 64=(8347532273131/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_65 : alpha 65=(8347532273131/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem alpha_eval_66 : alpha 66=(8347532273131/20000000000000 : ℝ) := by norm_num [alpha,alphaTail]
@[simp] theorem young_eval_2 : young 2=(95193002405431/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_3 : young 3=(60361814752637/10000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_4 : young 4=(470159457903553/50000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_5 : young 5=(25554367557219/2500000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_6 : young 6=(1102479731580301/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_7 : young 7=(236553062568137/20000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_8 : young 8=(1289045379687367/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_9 : young 9=(342542283954801/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_10 : young 10=(1423515181452149/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_11 : young 11=(291069320793913/20000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_12 : young 12=(294134663816097/20000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_13 : young 13=(368578410409753/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_14 : young 14=(1469572893548997/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_15 : young 15=(58346416357919/4000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_16 : young 16=(289522585659173/20000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_17 : young 17=(358078859792039/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_18 : young 18=(282652980140789/20000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_19 : young 19=(1391207860065547/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_20 : young 20=(1366859091679337/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_21 : young 21=(1340887630262589/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_22 : young 22=(10511216169161/800000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_23 : young 23=(257290325235787/20000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_24 : young 24=(629434388586049/50000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_25 : young 25=(1232730784495239/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_26 : young 26=(241565644342809/20000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_27 : young 27=(59227088301033/5000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_28 : young 28=(1868227441031/160000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_29 : young 29=(1154889676470491/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_30 : young 30=(1140451378078667/100000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_31 : young 31=(561957391821949/50000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_32 : young 32=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_33 : young 33=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_34 : young 34=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_35 : young 35=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_36 : young 36=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_37 : young 37=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_38 : young 38=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_39 : young 39=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_40 : young 40=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_41 : young 41=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_42 : young 42=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_43 : young 43=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_44 : young 44=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_45 : young 45=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_46 : young 46=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_47 : young 47=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_48 : young 48=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_49 : young 49=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_50 : young 50=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_51 : young 51=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_52 : young 52=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_53 : young 53=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_54 : young 54=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_55 : young 55=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_56 : young 56=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_57 : young 57=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_58 : young 58=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_59 : young 59=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_60 : young 60=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_61 : young 61=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_62 : young 62=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_63 : young 63=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_64 : young 64=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_65 : young 65=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem young_eval_66 : young 66=(567235711520317/25000000000000 : ℝ) := by norm_num [young,youngTail]
@[simp] theorem t_eval_2 : t 2=(1 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_3 : t 3=(495074302387353/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_4 : t 4=(256475451648929/50000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_5 : t 5=(431455417410153/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_6 : t 6=(375828697065803/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_7 : t 7=(167508622498929/50000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_8 : t 8=(62143078345047/20000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_9 : t 9=(290967381044679/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_10 : t 10=(273378191508407/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_11 : t 11=(4029599321999/1562500000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_12 : t 12=(244317269912887/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_13 : t 13=(232405484198257/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_14 : t 14=(110960691530321/50000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_15 : t 15=(42529996329769/20000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_16 : t 16=(204404356722221/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_17 : t 17=(2462815971153/1250000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_18 : t 18=(190378247442463/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_19 : t 19=(92174058101813/50000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_20 : t 20=(35767508206187/20000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_21 : t 21=(34752780389999/20000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_22 : t 22=(6762262568989/4000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_23 : t 23=(82327279289743/50000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_24 : t 24=(160504653539363/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_25 : t 25=(156559758366081/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_26 : t 26=(19097158953083/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_27 : t 27=(149117946189779/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_28 : t 28=(145991502813431/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_29 : t 29=(143530679528699/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_30 : t 30=(141197070597487/100000000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_31 : t 31=(17372454819443/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_32 : t 32=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_33 : t 33=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_34 : t 34=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_35 : t 35=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_36 : t 36=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_37 : t 37=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_38 : t 38=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_39 : t 39=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_40 : t 40=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_41 : t 41=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_42 : t 42=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_43 : t 43=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_44 : t 44=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_45 : t 45=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_46 : t 46=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_47 : t 47=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_48 : t 48=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_49 : t 49=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_50 : t 50=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_51 : t 51=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_52 : t 52=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_53 : t 53=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_54 : t 54=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_55 : t 55=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_56 : t 56=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_57 : t 57=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_58 : t 58=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_59 : t 59=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_60 : t 60=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_61 : t 61=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_62 : t 62=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_63 : t 63=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_64 : t 64=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_65 : t 65=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem t_eval_66 : t 66=(16487388560167/12500000000000 : ℝ) := by norm_num [t,tTail]
@[simp] theorem zeta_eval_2 : zeta 2=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_3 : zeta 3=(142857/100000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_4 : zeta 4=(92256280166883/50000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_5 : zeta 5=(208323806383/208000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_6 : zeta 6=(148419367937533/200000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_7 : zeta 7=(143702293408233/237500000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_8 : zeta 8=(13602854301207/27500000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_9 : zeta 9=(200642343932019/500000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_10 : zeta 10=(44869228225019/140000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_11 : zeta 11=(191782300934939/775000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_12 : zeta 12=(152362441384517/850000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_13 : zeta 13=(535605283941/4625000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_14 : zeta 14=(1413368152147/25000000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_15 : zeta 15=(24149122319/21500000000000 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_16 : zeta 16=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_17 : zeta 17=(0 : ℝ) := by norm_num [zeta]
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
@[simp] theorem zeta_eval_38 : zeta 38=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_39 : zeta 39=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_40 : zeta 40=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_41 : zeta 41=(0 : ℝ) := by norm_num [zeta]
@[simp] theorem zeta_eval_42 : zeta 42=(0 : ℝ) := by norm_num [zeta]
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
@[simp] theorem theta_eval_33 : theta 33=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_34 : theta 34=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_35 : theta 35=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_36 : theta 36=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_37 : theta 37=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_38 : theta 38=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_39 : theta 39=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_40 : theta 40=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_41 : theta 41=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_42 : theta 42=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_43 : theta 43=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_44 : theta 44=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_45 : theta 45=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_46 : theta 46=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_47 : theta 47=(0 : ℝ) := by norm_num [theta]
@[simp] theorem theta_eval_48 : theta 48=(0 : ℝ) := by norm_num [theta]
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
@[simp] theorem lambda_eval_32 : lambda 32=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_33 : lambda 33=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_34 : lambda 34=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_35 : lambda 35=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_36 : lambda 36=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_37 : lambda 37=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_38 : lambda 38=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_39 : lambda 39=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_40 : lambda 40=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_41 : lambda 41=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_42 : lambda 42=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_43 : lambda 43=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_44 : lambda 44=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_45 : lambda 45=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_46 : lambda 46=(0 : ℝ) := by norm_num [lambda]
@[simp] theorem lambda_eval_47 : lambda 47=(0 : ℝ) := by norm_num [lambda]
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
  if aa=3 then 5207 else
  if aa=4 then 8006913786 else
  0

theorem raw_first_cost_upper_5 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 5 ≤ (15444904239/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 4) :
      rawRow 5 aa ≤ rowGrid_5 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 4 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_5,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 5 ≤ (7437985246/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 4,rowGrid_5 aa/10000000000)+(7437985246/10000000000 : ℝ)=(15444904239/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_5]
  change (∑ aa ∈ Finset.Icc 2 4,rawRow 5 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 5 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_5 : c ≤ coefficient profile 5 := by
  have hf := raw_first_cost_upper_5
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 5-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 5-1-
      (K*C/young 5)*(5 : ℝ)^2-(15444904239/10000000000 : ℝ)-
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
  if aa=3 then 291546270 else
  if aa=4 then 8933179147 else
  if aa=5 then 8291995099 else
  0

theorem raw_first_cost_upper_6 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 6 ≤ (24463504475/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 5) :
      rawRow 6 aa ≤ rowGrid_6 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 5 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_6,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 6 ≤ (6946783959/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 5,rowGrid_6 aa/10000000000)+(6946783959/10000000000 : ℝ)=(24463504475/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_6]
  change (∑ aa ∈ Finset.Icc 2 5,rawRow 6 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 6 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_6 : c ≤ coefficient profile 6 := by
  have hf := raw_first_cost_upper_6
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 6-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 6-1-
      (K*C/young 6)*(6 : ℝ)^2-(24463504475/10000000000 : ℝ)-
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
  if aa=3 then 3791451996 else
  if aa=4 then 11972662429 else
  if aa=5 then 9467234630 else
  if aa=6 then 8485594011 else
  0

theorem raw_first_cost_upper_7 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 7 ≤ (39763751161/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 6) :
      rawRow 7 aa ≤ rowGrid_7 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 6 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_7,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 7 ≤ (6046808095/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 6,rowGrid_7 aa/10000000000)+(6046808095/10000000000 : ℝ)=(39763751161/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_7]
  change (∑ aa ∈ Finset.Icc 2 6,rawRow 7 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 7 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_7 : c ≤ coefficient profile 7 := by
  have hf := raw_first_cost_upper_7
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 7-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 7-1-
      (K*C/young 7)*(7 : ℝ)^2-(39763751161/10000000000 : ℝ)-
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
  if aa=3 then 6196720347 else
  if aa=4 then 14350801928 else
  if aa=5 then 13201589199 else
  if aa=6 then 10080097500 else
  if aa=7 then 8828778660 else
  0

theorem raw_first_cost_upper_8 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 8 ≤ (58493936946/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 7) :
      rawRow 8 aa ≤ rowGrid_8 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 7 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_8,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 8 ≤ (5835949312/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 7,rowGrid_8 aa/10000000000)+(5835949312/10000000000 : ℝ)=(58493936946/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_8]
  change (∑ aa ∈ Finset.Icc 2 7,rawRow 8 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 8 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_8 : c ≤ coefficient profile 8 := by
  have hf := raw_first_cost_upper_8
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 8-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 8-1-
      (K*C/young 8)*(8 : ℝ)^2-(58493936946/10000000000 : ℝ)-
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
  if aa=3 then 8308348942 else
  if aa=4 then 16639841368 else
  if aa=5 then 15977086286 else
  if aa=6 then 14192331293 else
  if aa=7 then 10589343741 else
  if aa=8 then 8914285981 else
  0

theorem raw_first_cost_upper_9 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 9 ≤ (80445396729/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 8) :
      rawRow 9 aa ≤ rowGrid_9 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 8 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_9,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 9 ≤ (5824159118/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 8,rowGrid_9 aa/10000000000)+(5824159118/10000000000 : ℝ)=(80445396729/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_9]
  change (∑ aa ∈ Finset.Icc 2 8,rawRow 9 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 9 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_9 : c ≤ coefficient profile 9 := by
  have hf := raw_first_cost_upper_9
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 9-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 9-1-
      (K*C/young 9)*(9 : ℝ)^2-(80445396729/10000000000 : ℝ)-
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
  if aa=3 then 10568206190 else
  if aa=4 then 18815661171 else
  if aa=5 then 18586970745 else
  if aa=6 then 17233088957 else
  if aa=7 then 14958776623 else
  if aa=8 then 10727363647 else
  if aa=9 then 8943851627 else
  0

theorem raw_first_cost_upper_10 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 10 ≤ (105582817015/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 9) :
      rawRow 10 aa ≤ rowGrid_10 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 9 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_10,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 10 ≤ (5748898055/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 9,rowGrid_10 aa/10000000000)+(5748898055/10000000000 : ℝ)=(105582817015/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_10]
  change (∑ aa ∈ Finset.Icc 2 9,rawRow 10 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 10 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_10 : c ≤ coefficient profile 10 := by
  have hf := raw_first_cost_upper_10
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 10-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 10-1-
      (K*C/young 10)*(10 : ℝ)^2-(105582817015/10000000000 : ℝ)-
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
  if aa=3 then 12821411257 else
  if aa=4 then 20857943141 else
  if aa=5 then 21102666176 else
  if aa=6 then 20129480928 else
  if aa=7 then 18237440075 else
  if aa=8 then 15215227322 else
  if aa=9 then 10806608986 else
  if aa=10 then 8980137726 else
  0

theorem raw_first_cost_upper_11 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 11 ≤ (133629024540/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 10) :
      rawRow 11 aa ≤ rowGrid_11 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 10 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_11,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 11 ≤ (5478108929/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 10,rowGrid_11 aa/10000000000)+(5478108929/10000000000 : ℝ)=(133629024540/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_11]
  change (∑ aa ∈ Finset.Icc 2 10,rawRow 11 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 11 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_11 : c ≤ coefficient profile 11 := by
  have hf := raw_first_cost_upper_11
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 11-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 11-1-
      (K*C/young 11)*(11 : ℝ)^2-(133629024540/10000000000 : ℝ)-
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
  if aa=3 then 15051382015 else
  if aa=4 then 22428913874 else
  if aa=5 then 23492199471 else
  if aa=6 then 22950684612 else
  if aa=7 then 21392802390 else
  if aa=8 then 18628616478 else
  if aa=9 then 15392502593 else
  if aa=10 then 10896379102 else
  if aa=11 then 9018147884 else
  0

theorem raw_first_cost_upper_12 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 12 ≤ (164280648139/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 11) :
      rawRow 12 aa ≤ rowGrid_12 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 11 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_12,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 12 ≤ (5029019720/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 11,rowGrid_12 aa/10000000000)+(5029019720/10000000000 : ℝ)=(164280648139/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_12]
  change (∑ aa ∈ Finset.Icc 2 11,rawRow 12 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 12 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_12 : c ≤ coefficient profile 12 := by
  have hf := raw_first_cost_upper_12
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 12-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 12-1-
      (K*C/young 12)*(12 : ℝ)^2-(164280648139/10000000000 : ℝ)-
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
  if aa=3 then 17302886014 else
  if aa=4 then 23592220042 else
  if aa=5 then 25365318571 else
  if aa=6 then 25654400665 else
  if aa=7 then 24491231630 else
  if aa=8 then 21941397257 else
  if aa=9 then 18923055761 else
  if aa=10 then 15584105502 else
  if aa=11 then 10987437998 else
  if aa=12 then 9055182970 else
  0

theorem raw_first_cost_upper_13 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 13 ≤ (197297041104/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 12) :
      rawRow 13 aa ≤ rowGrid_13 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 12 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_13,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 13 ≤ (4399804694/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 12,rowGrid_13 aa/10000000000)+(4399804694/10000000000 : ℝ)=(197297041104/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_13]
  change (∑ aa ∈ Finset.Icc 2 12,rawRow 13 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 13 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_13 : c ≤ coefficient profile 13 := by
  have hf := raw_first_cost_upper_13
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 13-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 13-1-
      (K*C/young 13)*(13 : ℝ)^2-(197297041104/10000000000 : ℝ)-
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
  if aa=3 then 19632101755 else
  if aa=4 then 24414506462 else
  if aa=5 then 26783138118 else
  if aa=6 then 27806036430 else
  if aa=7 then 27481309727 else
  if aa=8 then 25215512510 else
  if aa=9 then 22373582048 else
  if aa=10 then 19232001589 else
  if aa=11 then 15774539332 else
  if aa=12 then 11074825388 else
  if aa=13 then 9089872739 else
  0

theorem raw_first_cost_upper_14 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 14 ≤ (232456402230/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 13) :
      rawRow 14 aa ≤ rowGrid_14 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 13 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_14,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 14 ≤ (3578976132/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 13,rowGrid_14 aa/10000000000)+(3578976132/10000000000 : ℝ)=(232456402230/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_14]
  change (∑ aa ∈ Finset.Icc 2 13,rawRow 14 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 14 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_14 : c ≤ coefficient profile 14 := by
  have hf := raw_first_cost_upper_14
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 14-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 14-1-
      (K*C/young 14)*(14 : ℝ)^2-(232456402230/10000000000 : ℝ)-
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
  if aa=3 then 22050238991 else
  if aa=4 then 24954656569 else
  if aa=5 then 27813396127 else
  if aa=6 then 29462774934 else
  if aa=7 then 29890147769 else
  if aa=8 then 28392786829 else
  if aa=9 then 25801945945 else
  if aa=10 then 22818240806 else
  if aa=11 then 19534968391 else
  if aa=12 then 15955505077 else
  if aa=13 then 11156061031 else
  if aa=14 then 9121604208 else
  0

theorem raw_first_cost_upper_15 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 15 ≤ (269530164845/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 14) :
      rawRow 15 aa ≤ rowGrid_15 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 14 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_15,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 15 ≤ (2577838168/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 14,rowGrid_15 aa/10000000000)+(2577838168/10000000000 : ℝ)=(269530164845/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_15]
  change (∑ aa ∈ Finset.Icc 2 14,rawRow 15 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 15 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_15 : c ≤ coefficient profile 15 := by
  have hf := raw_first_cost_upper_15
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 15-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 15-1-
      (K*C/young 15)*(15 : ℝ)^2-(269530164845/10000000000 : ℝ)-
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
  if aa=3 then 24581766199 else
  if aa=4 then 25278881915 else
  if aa=5 then 28517816393 else
  if aa=6 then 30691973031 else
  if aa=7 then 31770293161 else
  if aa=8 then 30978276833 else
  if aa=9 then 29144142557 else
  if aa=10 then 26397190012 else
  if aa=11 then 23250322704 else
  if aa=12 then 19820982745 else
  if aa=13 then 16122899608 else
  if aa=14 then 11230081340 else
  if aa=15 then 9150183918 else
  0

theorem raw_first_cost_upper_16 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 16 ≤ (308330168563/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 15) :
      rawRow 16 aa ≤ rowGrid_16 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 15 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_16,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 16 ≤ (1395358147/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 15,rowGrid_16 aa/10000000000)+(1395358147/10000000000 : ℝ)=(308330168563/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_16]
  change (∑ aa ∈ Finset.Icc 2 15,rawRow 16 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 16 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_16 : c ≤ coefficient profile 16 := by
  have hf := raw_first_cost_upper_16
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 16-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 16-1-
      (K*C/young 16)*(16 : ℝ)^2-(308330168563/10000000000 : ℝ)-
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
  if aa=3 then 27239311352 else
  if aa=4 then 25435374229 else
  if aa=5 then 28968735189 else
  if aa=6 then 31556879878 else
  if aa=7 then 33187870243 else
  if aa=8 then 33018505954 else
  if aa=9 then 31886548960 else
  if aa=10 then 29899472165 else
  if aa=11 then 26971899081 else
  if aa=12 then 23656389224 else
  if aa=13 then 20084673594 else
  if aa=14 then 16275044010 else
  if aa=15 then 11296619550 else
  if aa=16 then 9175649695 else
  0

theorem raw_first_cost_upper_17 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 17 ≤ (348683570901/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 16) :
      rawRow 17 aa ≤ rowGrid_17 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 16 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_17,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 17 ≤ (30597777/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 16,rowGrid_17 aa/10000000000)+(30597777/10000000000 : ℝ)=(348683570901/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_17]
  change (∑ aa ∈ Finset.Icc 2 16,rawRow 17 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 17 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_17 : c ≤ coefficient profile 17 := by
  have hf := raw_first_cost_upper_17
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 17-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 17-1-
      (K*C/young 17)*(17 : ℝ)^2-(348683570901/10000000000 : ℝ)-
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
  if aa=3 then 27233862798 else
  if aa=4 then 25458356955 else
  if aa=5 then 29219540399 else
  if aa=6 then 32134451997 else
  if aa=7 then 34206781094 else
  if aa=8 then 34576350771 else
  if aa=9 then 34069931193 else
  if aa=10 then 32793164968 else
  if aa=11 then 30625340442 else
  if aa=12 then 27510252357 else
  if aa=13 then 24029881439 else
  if aa=14 then 20323915295 else
  if aa=15 then 16411616072 else
  if aa=16 then 11355835176 else
  if aa=17 then 9198148167 else
  0

theorem raw_first_cost_upper_18 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 18 ≤ (389147429123/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 17) :
      rawRow 18 aa ≤ rowGrid_18 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 17 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_18,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 18 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 17,rowGrid_18 aa/10000000000)+(0/10000000000 : ℝ)=(389147429123/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_18]
  change (∑ aa ∈ Finset.Icc 2 17,rawRow 18 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 18 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_18 : c ≤ coefficient profile 18 := by
  have hf := raw_first_cost_upper_18
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 18-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 18-1-
      (K*C/young 18)*(18 : ℝ)^2-(389147429123/10000000000 : ℝ)-
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
  if aa=3 then 27069799862 else
  if aa=4 then 25452193127 else
  if aa=5 then 29308367161 else
  if aa=6 then 32481849374 else
  if aa=7 then 34907203116 else
  if aa=8 then 35713958006 else
  if aa=9 then 35753535783 else
  if aa=10 then 35113415443 else
  if aa=11 then 33660978830 else
  if aa=12 then 31303289426 else
  if aa=13 then 28004237259 else
  if aa=14 then 24368019264 else
  if aa=15 then 20538208409 else
  if aa=16 then 16532857768 else
  if aa=17 then 11407977601 else
  if aa=18 then 9217781394 else
  0

theorem raw_first_cost_upper_19 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 19 ≤ (430833671823/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 18) :
      rawRow 19 aa ≤ rowGrid_19 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 18 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_19,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 19 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 18,rowGrid_19 aa/10000000000)+(0/10000000000 : ℝ)=(430833671823/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_19]
  change (∑ aa ∈ Finset.Icc 2 18,rawRow 19 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 19 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_19 : c ≤ coefficient profile 19 := by
  have hf := raw_first_cost_upper_19
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 19-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 19-1-
      (K*C/young 19)*(19 : ℝ)^2-(430833671823/10000000000 : ℝ)-
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
  if aa=3 then 26816034409 else
  if aa=4 then 25345427210 else
  if aa=5 then 29355201663 else
  if aa=6 then 32640559714 else
  if aa=7 then 35349519047 else
  if aa=8 then 36512320467 else
  if aa=9 then 36997845247 else
  if aa=10 then 36916406684 else
  if aa=11 then 36108968967 else
  if aa=12 then 34469453543 else
  if aa=13 then 31924033442 else
  if aa=14 then 28450568963 else
  if aa=15 then 24670276434 else
  if aa=16 then 20728016401 else
  if aa=17 then 16639340737 else
  if aa=18 then 11453369433 else
  if aa=19 then 9234747186 else
  0

theorem raw_first_cost_upper_20 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 20 ≤ (473612089547/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 19) :
      rawRow 20 aa ≤ rowGrid_20 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 19 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_20,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 20 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 19,rowGrid_20 aa/10000000000)+(0/10000000000 : ℝ)=(473612089547/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_20]
  change (∑ aa ∈ Finset.Icc 2 19,rawRow 20 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 20 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_20 : c ≤ coefficient profile 20 := by
  have hf := raw_first_cost_upper_20
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 20-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 20-1-
      (K*C/young 20)*(20 : ℝ)^2-(473612089547/10000000000 : ℝ)-
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
  if aa=3 then 26487593013 else
  if aa=4 then 25147221664 else
  if aa=5 then 29277929379 else
  if aa=6 then 32744014713 else
  if aa=7 then 35577976450 else
  if aa=8 then 37032989799 else
  if aa=9 then 37884256393 else
  if aa=10 then 38261125472 else
  if aa=11 then 38022644548 else
  if aa=12 then 37034256529 else
  if aa=13 then 35208138470 else
  if aa=14 then 32483726807 else
  if aa=15 then 28848658802 else
  if aa=16 then 24937337769 else
  if aa=17 then 20894251314 else
  if aa=18 then 16731759346 else
  if aa=19 then 11492453634 else
  if aa=20 then 9249236733 else
  0

theorem raw_first_cost_upper_21 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 21 ≤ (517315570835/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 20) :
      rawRow 21 aa ≤ rowGrid_21 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 20 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_21,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 21 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 20,rowGrid_21 aa/10000000000)+(0/10000000000 : ℝ)=(517315570835/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_21]
  change (∑ aa ∈ Finset.Icc 2 20,rawRow 21 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 21 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_21 : c ≤ coefficient profile 21 := by
  have hf := raw_first_cost_upper_21
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 21-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 21-1-
      (K*C/young 21)*(21 : ℝ)^2-(517315570835/10000000000 : ℝ)-
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
  if aa=3 then 26099170848 else
  if aa=4 then 24871934090 else
  if aa=5 then 29087229708 else
  if aa=6 then 32700833706 else
  if aa=7 then 35737747856 else
  if aa=8 then 37321416376 else
  if aa=9 then 38475096328 else
  if aa=10 then 39229401662 else
  if aa=11 then 39459560744 else
  if aa=12 then 39048330433 else
  if aa=13 then 37877726454 else
  if aa=14 then 35872592451 else
  if aa=15 then 32981630986 else
  if aa=16 then 29199358266 else
  if aa=17 then 25170437587 else
  if aa=18 then 21037974093 else
  if aa=19 then 16810967483 else
  if aa=20 then 11525645368 else
  if aa=21 then 9261418364 else
  0

theorem raw_first_cost_upper_22 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 22 ≤ (561768472803/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 21) :
      rawRow 22 aa ≤ rowGrid_22 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 21 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_22,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 22 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 21,rowGrid_22 aa/10000000000)+(0/10000000000 : ℝ)=(561768472803/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_22]
  change (∑ aa ∈ Finset.Icc 2 21,rawRow 22 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 22 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_22 : c ≤ coefficient profile 22 := by
  have hf := raw_first_cost_upper_22
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 22-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 22-1-
      (K*C/young 22)*(22 : ℝ)^2-(561768472803/10000000000 : ℝ)-
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
  if aa=3 then 25664700404 else
  if aa=4 then 24533698062 else
  if aa=5 then 28799911367 else
  if aa=6 then 32522960315 else
  if aa=7 then 35729202377 else
  if aa=8 then 37529544781 else
  if aa=9 then 38816672179 else
  if aa=10 then 39884290904 else
  if aa=11 then 40501903271 else
  if aa=12 then 40567817046 else
  if aa=13 then 39980846487 else
  if aa=14 then 38634282009 else
  if aa=15 then 36461815134 else
  if aa=16 then 33418661409 else
  if aa=17 then 29504158143 else
  if aa=18 then 25370972236 else
  if aa=19 then 21160418707 else
  if aa=20 then 16877745850 else
  if aa=21 then 11553301385 else
  if aa=22 then 9271430461 else
  0

theorem raw_first_cost_upper_23 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 23 ≤ (606784332527/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 22) :
      rawRow 23 aa ≤ rowGrid_23 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 22 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_23,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 23 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 22,rowGrid_23 aa/10000000000)+(0/10000000000 : ℝ)=(606784332527/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_23]
  change (∑ aa ∈ Finset.Icc 2 22,rawRow 23 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 23 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_23 : c ≤ coefficient profile 23 := by
  have hf := raw_first_cost_upper_23
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 23-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 23-1-
      (K*C/young 23)*(23 : ℝ)^2-(606784332527/10000000000 : ℝ)-
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
  if aa=3 then 25196962322 else
  if aa=4 then 24145969831 else
  if aa=5 then 28432611971 else
  if aa=6 then 32229310076 else
  if aa=7 then 35565319473 else
  if aa=8 then 37552736191 else
  if aa=9 then 39066601119 else
  if aa=10 then 40272872598 else
  if aa=11 then 41213336225 else
  if aa=12 then 41675130998 else
  if aa=13 then 41572228254 else
  if aa=14 then 40814368023 else
  if aa=15 then 39302530728 else
  if aa=16 then 36976632391 else
  if aa=17 then 33796452763 else
  if aa=18 then 29764714451 else
  if aa=19 then 25540512056 else
  if aa=20 then 21262686735 else
  if aa=21 then 16932747876 else
  if aa=22 then 11575706161 else
  if aa=23 then 9279378599 else
  0

theorem raw_first_cost_upper_24 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 24 ≤ (652168808841/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 23) :
      rawRow 24 aa ≤ rowGrid_24 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 23 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_24,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 24 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 23,rowGrid_24 aa/10000000000)+(0/10000000000 : ℝ)=(652168808841/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_24]
  change (∑ aa ∈ Finset.Icc 2 23,rawRow 24 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 24 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_24 : c ≤ coefficient profile 24 := by
  have hf := raw_first_cost_upper_24
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 24-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 24-1-
      (K*C/young 24)*(24 : ℝ)^2-(652168808841/10000000000 : ℝ)-
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
  if aa=3 then 24707537291 else
  if aa=4 then 23721125197 else
  if aa=5 then 28001225564 else
  if aa=6 then 31838695104 else
  if aa=7 then 35266819748 else
  if aa=8 then 37404480194 else
  if aa=9 then 39115831111 else
  if aa=10 then 40558191459 else
  if aa=11 then 41641575204 else
  if aa=12 then 42434389460 else
  if aa=13 then 42734367666 else
  if aa=14 then 42466164601 else
  if aa=15 then 41546973295 else
  if aa=16 then 39883037893 else
  if aa=17 then 37418646092 else
  if aa=18 then 34116797459 else
  if aa=19 then 29982846050 else
  if aa=20 then 25680420349 else
  if aa=21 then 21345669659 else
  if aa=22 then 16976473411 else
  if aa=23 then 11593065442 else
  if aa=24 then 9285334180 else
  0

theorem raw_first_cost_upper_25 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 25 ≤ (697719666429/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 24) :
      rawRow 25 aa ≤ rowGrid_25 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 24 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_25,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 25 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 24,rowGrid_25 aa/10000000000)+(0/10000000000 : ℝ)=(697719666429/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_25]
  change (∑ aa ∈ Finset.Icc 2 24,rawRow 25 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 25 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_25 : c ≤ coefficient profile 25 := by
  have hf := raw_first_cost_upper_25
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 25-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 25-1-
      (K*C/young 25)*(25 : ℝ)^2-(697719666429/10000000000 : ℝ)-
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
  if aa=3 then 24203668686 else
  if aa=4 then 23270335903 else
  if aa=5 then 27520338140 else
  if aa=6 then 31369069445 else
  if aa=7 then 34854322317 else
  if aa=8 then 37106440969 else
  if aa=9 then 38978102511 else
  if aa=10 then 40626705760 else
  if aa=11 then 41954564366 else
  if aa=12 then 42893692004 else
  if aa=13 then 43531572966 else
  if aa=14 then 43672003034 else
  if aa=15 then 43246946307 else
  if aa=16 then 42178700935 else
  if aa=17 then 40377092113 else
  if aa=18 then 37789513493 else
  if aa=19 then 34381552649 else
  if aa=20 then 30160009682 else
  if aa=21 then 25791693861 else
  if aa=22 then 21409962838 else
  if aa=23 then 17009218677 else
  if aa=24 then 11605477807 else
  if aa=25 then 9289313766 else
  0

theorem raw_first_cost_upper_26 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 26 ≤ (743220298229/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 25) :
      rawRow 26 aa ≤ rowGrid_26 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 25 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_26,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 26 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 25,rowGrid_26 aa/10000000000)+(0/10000000000 : ℝ)=(743220298229/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_26]
  change (∑ aa ∈ Finset.Icc 2 25,rawRow 26 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 26 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_26 : c ≤ coefficient profile 26 := by
  have hf := raw_first_cost_upper_26
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 26-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 26-1-
      (K*C/young 26)*(26 : ℝ)^2-(743220298229/10000000000 : ℝ)-
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
  if aa=3 then 23716337855 else
  if aa=4 then 22800635311 else
  if aa=5 then 27003103958 else
  if aa=6 then 30836914553 else
  if aa=7 then 34347534996 else
  if aa=8 then 36680242849 else
  if aa=9 then 38675766279 else
  if aa=10 then 40492286025 else
  if aa=11 then 42034394876 else
  if aa=12 then 43225303524 else
  if aa=13 then 44012130019 else
  if aa=14 then 44496181760 else
  if aa=15 then 44484434682 else
  if aa=16 then 43913880126 else
  if aa=17 then 42710294227 else
  if aa=18 then 40785972863 else
  if aa=19 then 38090886905 else
  if aa=20 then 34592078919 else
  if aa=21 then 30297149484 else
  if aa=22 then 25874892292 else
  if aa=23 then 21455831831 else
  if aa=24 then 17031059205 else
  if aa=25 then 11612926442 else
  if aa=26 then 9291293698 else
  0

theorem raw_first_cost_upper_27 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 27 ≤ (788461532679/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 26) :
      rawRow 27 aa ≤ rowGrid_27 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 26 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_27,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 27 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 26,rowGrid_27 aa/10000000000)+(0/10000000000 : ℝ)=(788461532679/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_27]
  change (∑ aa ∈ Finset.Icc 2 26,rawRow 27 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 27 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_27 : c ≤ coefficient profile 27 := by
  have hf := raw_first_cost_upper_27
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 27-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 27-1-
      (K*C/young 27)*(27 : ℝ)^2-(788461532679/10000000000 : ℝ)-
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
  if aa=3 then 23313292793 else
  if aa=4 then 22409897980 else
  if aa=5 then 26538995843 else
  if aa=6 then 30349905428 else
  if aa=7 then 33868140948 else
  if aa=8 then 36257481670 else
  if aa=9 then 38348495491 else
  if aa=10 then 40301112198 else
  if aa=11 then 42023477593 else
  if aa=12 then 43440032087 else
  if aa=13 then 44488064514 else
  if aa=14 then 45125006212 else
  if aa=15 then 45462593996 else
  if aa=16 then 45308631279 else
  if aa=17 then 44603370475 else
  if aa=18 then 43274778403 else
  if aa=19 then 41237004685 else
  if aa=20 then 38441361839 else
  if aa=21 then 34855671848 else
  if aa=22 then 30487861103 else
  if aa=23 then 26009649262 else
  if aa=24 then 21549100801 else
  if aa=25 then 17094122445 else
  if aa=26 then 11650933764 else
  if aa=27 then 9319716261 else
  0

theorem raw_first_cost_upper_28 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 28 ≤ (835758698918/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 27) :
      rawRow 28 aa ≤ rowGrid_28 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 27 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_28,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 28 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 27,rowGrid_28 aa/10000000000)+(0/10000000000 : ℝ)=(835758698918/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_28]
  change (∑ aa ∈ Finset.Icc 2 27,rawRow 28 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 28 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_28 : c ≤ coefficient profile 28 := by
  have hf := raw_first_cost_upper_28
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 28-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 28-1-
      (K*C/young 28)*(28 : ℝ)^2-(835758698918/10000000000 : ℝ)-
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
  if aa=3 then 23030046854 else
  if aa=4 then 22121540399 else
  if aa=5 then 26193703897 else
  if aa=6 then 29953504157 else
  if aa=7 then 33473203622 else
  if aa=8 then 35901526605 else
  if aa=9 then 38065650871 else
  if aa=10 then 40127853643 else
  if aa=11 then 42000670240 else
  if aa=12 then 43611078088 else
  if aa=13 then 44896769596 else
  if aa=14 then 45804473494 else
  if aa=15 then 46298640350 else
  if aa=16 then 46499317141 else
  if aa=17 then 46213227946 else
  if aa=18 then 45382609395 else
  if aa=19 then 43937023757 else
  if aa=20 then 41791146731 else
  if aa=21 then 38896905886 else
  if aa=22 then 35222334884 else
  if aa=23 then 30775307325 else
  if aa=24 then 26232385632 else
  if aa=25 then 21719698915 else
  if aa=26 then 17222070581 else
  if aa=27 then 11735638724 else
  if aa=28 then 9358843535 else
  0

theorem raw_first_cost_upper_29 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 29 ≤ (886465172268/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 28) :
      rawRow 29 aa ≤ rowGrid_29 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 28 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_29,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 29 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 28,rowGrid_29 aa/10000000000)+(0/10000000000 : ℝ)=(886465172268/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_29]
  change (∑ aa ∈ Finset.Icc 2 28,rawRow 29 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 29 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_29 : c ≤ coefficient profile 29 := by
  have hf := raw_first_cost_upper_29
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 29-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 29-1-
      (K*C/young 29)*(29 : ℝ)^2-(886465172268/10000000000 : ℝ)-
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
  if aa=3 then 22810640888 else
  if aa=4 then 21866050780 else
  if aa=5 then 25872368198 else
  if aa=6 then 29581748975 else
  if aa=7 then 33056080490 else
  if aa=8 then 35504436210 else
  if aa=9 then 37714844700 else
  if aa=10 then 39856085741 else
  if aa=11 then 41845513714 else
  if aa=12 then 43613891458 else
  if aa=13 then 45100936824 else
  if aa=14 then 46253357269 else
  if aa=15 then 47024332743 else
  if aa=16 then 47383199672 else
  if aa=17 then 47456501703 else
  if aa=18 then 47049159982 else
  if aa=19 then 46105106468 else
  if aa=20 then 44554502103 else
  if aa=21 then 42312078839 else
  if aa=22 then 39329961700 else
  if aa=23 then 35576020523 else
  if aa=24 then 31057713156 else
  if aa=25 then 26456124144 else
  if aa=26 then 21895564109 else
  if aa=27 then 17357818654 else
  if aa=28 then 11792068991 else
  if aa=29 then 9364529678 else
  0

theorem raw_first_cost_upper_30 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 30 ≤ (937790637712/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 29) :
      rawRow 30 aa ≤ rowGrid_30 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 29 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_30,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 30 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 29,rowGrid_30 aa/10000000000)+(0/10000000000 : ℝ)=(937790637712/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_30]
  change (∑ aa ∈ Finset.Icc 2 29,rawRow 30 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 30 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_30 : c ≤ coefficient profile 30 := by
  have hf := raw_first_cost_upper_30
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 30-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 30-1-
      (K*C/young 30)*(30 : ℝ)^2-(937790637712/10000000000 : ℝ)-
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
  if aa=3 then 22587936177 else
  if aa=4 then 21669932771 else
  if aa=5 then 25587963126 else
  if aa=6 then 29235307260 else
  if aa=7 then 32664206628 else
  if aa=8 then 35081749598 else
  if aa=9 then 37318705800 else
  if aa=10 then 39511021142 else
  if aa=11 then 41585522566 else
  if aa=12 then 43477250061 else
  if aa=13 then 45129250866 else
  if aa=14 then 46489864043 else
  if aa=15 then 47511916969 else
  if aa=16 then 48152998339 else
  if aa=17 then 48385816658 else
  if aa=18 then 48342135992 else
  if aa=19 then 47825110897 else
  if aa=20 then 46779387898 else
  if aa=21 then 45135287757 else
  if aa=22 then 42807254670 else
  if aa=23 then 39747269027 else
  if aa=24 then 35922701437 else
  if aa=25 then 31340249678 else
  if aa=26 then 26685362307 else
  if aa=27 then 22080579462 else
  if aa=28 then 17451106641 else
  if aa=29 then 11805879358 else
  if aa=30 then 9369804212 else
  0

theorem raw_first_cost_upper_31 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 31 ≤ (989681571340/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 30) :
      rawRow 31 aa ≤ rowGrid_31 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 30 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_31,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 31 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 30,rowGrid_31 aa/10000000000)+(0/10000000000 : ℝ)=(989681571340/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_31]
  change (∑ aa ∈ Finset.Icc 2 30,rawRow 31 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 31 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_31 : c ≤ coefficient profile 31 := by
  have hf := raw_first_cost_upper_31
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 31-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 31-1-
      (K*C/young 31)*(31 : ℝ)^2-(989681571340/10000000000 : ℝ)-
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
  if aa=3 then 21519023694 else
  if aa=4 then 20690063303 else
  if aa=5 then 24450521061 else
  if aa=6 then 27878691527 else
  if aa=7 then 31125842840 else
  if aa=8 then 33424674924 else
  if aa=9 then 35554157239 else
  if aa=10 then 37696210616 else
  if aa=11 then 39749435333 else
  if aa=12 then 41660120084 else
  if aa=13 then 43377103034 else
  if aa=14 then 44853468079 else
  if aa=15 then 46045029881 else
  if aa=16 then 46910324472 else
  if aa=17 then 47411338535 else
  if aa=18 then 47524043145 else
  if aa=19 then 47380008957 else
  if aa=20 then 46787159794 else
  if aa=21 then 45692439615 else
  if aa=22 then 44028553721 else
  if aa=23 then 41712511379 else
  if aa=24 then 38697606758 else
  if aa=25 then 34951607699 else
  if aa=26 then 30479969405 else
  if aa=27 then 25947326834 else
  if aa=28 then 21404420928 else
  if aa=29 then 16845988227 else
  if aa=30 then 11389589656 else
  if aa=31 then 9034324943 else
  0

theorem raw_first_cost_upper_32 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 32 ≤ (1004221555683/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 31) :
      rawRow 32 aa ≤ rowGrid_32 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 31 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_32,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 32 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 31,rowGrid_32 aa/10000000000)+(0/10000000000 : ℝ)=(1004221555683/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_32]
  change (∑ aa ∈ Finset.Icc 2 31,rawRow 32 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 32 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_32 : c ≤ coefficient profile 32 := by
  have hf := raw_first_cost_upper_32
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 32-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 32-1-
      (K*C/young 32)*(32 : ℝ)^2-(1004221555683/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 32 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 32-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 32-1-
      ((K*C/young 32)*(32 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 32+
        t 3*tripleHarmonicNeighborCharge K young zeta 32)
  linarith only [hf,hn]

def rowGrid_33 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 21545356370 else
  if aa=4 then 20769074730 else
  if aa=5 then 24598107319 else
  if aa=6 then 28069463169 else
  if aa=7 then 31274844710 else
  if aa=8 then 33560275397 else
  if aa=9 then 35693213875 else
  if aa=10 then 37841716488 else
  if aa=11 then 39959470306 else
  if aa=12 then 41958372630 else
  if aa=13 then 43795381328 else
  if aa=14 then 45426341954 else
  if aa=15 then 46809050224 else
  if aa=16 then 47902475838 else
  if aa=17 then 48667230974 else
  if aa=18 then 49066698880 else
  if aa=19 then 49078581499 else
  if aa=20 then 48839943484 else
  if aa=21 then 48153273007 else
  if aa=22 then 46964734162 else
  if aa=23 then 45205648019 else
  if aa=24 then 42791003232 else
  if aa=25 then 39672684924 else
  if aa=26 then 35816945791 else
  if aa=27 then 31227941934 else
  if aa=28 then 26502995120 else
  if aa=29 then 21771398202 else
  if aa=30 then 17124407237 else
  if aa=31 then 11571311535 else
  if aa=32 then 9519300241 else
  0

theorem raw_first_cost_upper_33 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 33 ≤ (1298071527188/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 32) :
      rawRow 33 aa ≤ rowGrid_33 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 32 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_33,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 33 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 32,rowGrid_33 aa/10000000000)+(0/10000000000 : ℝ)=(1298071527188/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_33]
  change (∑ aa ∈ Finset.Icc 2 32,rawRow 33 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 33 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_33 : c ≤ coefficient profile 33 := by
  have hf := raw_first_cost_upper_33
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 33-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 33-1-
      (K*C/young 33)*(33 : ℝ)^2-(1298071527188/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 33 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 33-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 33-1-
      ((K*C/young 33)*(33 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 33+
        t 3*tripleHarmonicNeighborCharge K young zeta 33)
  linarith only [hf,hn]

def rowGrid_34 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 20794489699 else
  if aa=5 then 24692042824 else
  if aa=6 then 28238893793 else
  if aa=7 then 31488855955 else
  if aa=8 then 33720931088 else
  if aa=9 then 35838017578 else
  if aa=10 then 37989720047 else
  if aa=11 then 40113712270 else
  if aa=12 then 42180079569 else
  if aa=13 then 44108920606 else
  if aa=14 then 45864380722 else
  if aa=15 then 47406901029 else
  if aa=16 then 48697316587 else
  if aa=17 then 49696540839 else
  if aa=18 then 50366440631 else
  if aa=19 then 50671698377 else
  if aa=20 then 50590854656 else
  if aa=21 then 50265994829 else
  if aa=22 then 49494088844 else
  if aa=23 then 48220326638 else
  if aa=24 then 46374456165 else
  if aa=25 then 43869224250 else
  if aa=26 then 40654908282 else
  if aa=27 then 36695886684 else
  if aa=28 then 31896695870 else
  if aa=29 then 26957387085 else
  if aa=30 then 22131221030 else
  if aa=31 then 17397628622 else
  if aa=32 then 12192475849 else
  if aa=33 then 9519300241 else
  0

theorem raw_first_cost_upper_34 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 34 ≤ (1390854025079/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 33) :
      rawRow 34 aa ≤ rowGrid_34 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 33 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_34,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 34 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 33,rowGrid_34 aa/10000000000)+(0/10000000000 : ℝ)=(1390854025079/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_34]
  change (∑ aa ∈ Finset.Icc 2 33,rawRow 34 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 34 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_34 : c ≤ coefficient profile 34 := by
  have hf := raw_first_cost_upper_34
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 34-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 34-1-
      (K*C/young 34)*(34 : ℝ)^2-(1390854025079/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 34 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 34-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 34-1-
      ((K*C/young 34)*(34 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 34+
        t 3*tripleHarmonicNeighborCharge K young zeta 34)
  linarith only [hf,hn]

def rowGrid_35 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 24722258301 else
  if aa=6 then 28346732770 else
  if aa=7 then 31678926441 else
  if aa=8 then 33951680705 else
  if aa=9 then 36009577000 else
  if aa=10 then 38143840439 else
  if aa=11 then 40270601881 else
  if aa=12 then 42342892996 else
  if aa=13 then 44341990984 else
  if aa=14 then 46192732352 else
  if aa=15 then 47864038004 else
  if aa=16 then 49319284557 else
  if aa=17 then 50521150320 else
  if aa=18 then 51431688708 else
  if aa=19 then 52013955416 else
  if aa=20 then 52233060725 else
  if aa=21 then 52068029917 else
  if aa=22 then 51665638876 else
  if aa=23 then 50817303096 else
  if aa=24 then 49467080375 else
  if aa=25 then 47542970796 else
  if aa=26 then 44955346272 else
  if aa=27 then 41652571834 else
  if aa=28 then 37481737981 else
  if aa=29 then 32443562451 else
  if aa=30 then 27402920402 else
  if aa=31 then 22484326558 else
  if aa=32 then 18331557851 else
  if aa=33 then 12192475849 else
  if aa=34 then 9519300241 else
  0

theorem raw_first_cost_upper_35 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 35 ≤ (1484367007236/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 34) :
      rawRow 35 aa ≤ rowGrid_35 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 34 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_35,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 35 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 34,rowGrid_35 aa/10000000000)+(0/10000000000 : ℝ)=(1484367007236/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_35]
  change (∑ aa ∈ Finset.Icc 2 34,rawRow 35 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 35 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_35 : c ≤ coefficient profile 35 := by
  have hf := raw_first_cost_upper_35
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 35-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 35-1-
      (K*C/young 35)*(35 : ℝ)^2-(1484367007236/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 35 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 35-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 35-1-
      ((K*C/young 35)*(35 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 35+
        t 3*tripleHarmonicNeighborCharge K young zeta 35)
  linarith only [hf,hn]

def rowGrid_36 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 28381420466 else
  if aa=7 then 31799902250 else
  if aa=8 then 34156617095 else
  if aa=9 then 36255987637 else
  if aa=10 then 38326438018 else
  if aa=11 then 40433975577 else
  if aa=12 then 42508501204 else
  if aa=13 then 44513149303 else
  if aa=14 then 46436813537 else
  if aa=15 then 48206705551 else
  if aa=16 then 49794862332 else
  if aa=17 then 51166412513 else
  if aa=18 then 52285089315 else
  if aa=19 then 53114048360 else
  if aa=20 then 53616677136 else
  if aa=21 then 53758185882 else
  if aa=22 then 53517851180 else
  if aa=23 then 53046909069 else
  if aa=24 then 52131202584 else
  if aa=25 then 50713521023 else
  if aa=26 then 48720048085 else
  if aa=27 then 46058541737 else
  if aa=28 then 42544571744 else
  if aa=29 then 38124359711 else
  if aa=30 then 32979767534 else
  if aa=31 then 27840136345 else
  if aa=32 then 23691316902 else
  if aa=33 then 18331557851 else
  if aa=34 then 12192475849 else
  if aa=35 then 9519300241 else
  0

theorem raw_first_cost_upper_36 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 36 ≤ (1583712237305/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 35) :
      rawRow 36 aa ≤ rowGrid_36 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 35 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_36,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 36 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 35,rowGrid_36 aa/10000000000)+(0/10000000000 : ℝ)=(1583712237305/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_36]
  change (∑ aa ∈ Finset.Icc 2 35,rawRow 36 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 36 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_36 : c ≤ coefficient profile 36 := by
  have hf := raw_first_cost_upper_36
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 36-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 36-1-
      (K*C/young 36)*(36 : ℝ)^2-(1583712237305/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 36 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 36-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 36-1-
      ((K*C/young 36)*(36 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 36+
        t 3*tripleHarmonicNeighborCharge K young zeta 36)
  linarith only [hf,hn]

def rowGrid_37 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 31838815565 else
  if aa=8 then 34287054735 else
  if aa=9 then 36474833098 else
  if aa=10 then 38588702748 else
  if aa=11 then 40627536213 else
  if aa=12 then 42680953828 else
  if aa=13 then 44687245648 else
  if aa=14 then 46616057787 else
  if aa=15 then 48461428518 else
  if aa=16 then 50151353010 else
  if aa=17 then 51659801840 else
  if aa=18 then 52952880748 else
  if aa=19 then 53995364184 else
  if aa=20 then 54750667576 else
  if aa=21 then 55182201767 else
  if aa=22 then 55255069115 else
  if aa=23 then 54948639888 else
  if aa=24 then 54418455816 else
  if aa=25 then 53444772122 else
  if aa=26 then 51969095355 else
  if aa=27 then 49915628602 else
  if aa=28 then 47044896559 else
  if aa=29 then 43273995398 else
  if aa=30 then 38754453139 else
  if aa=31 then 33505962551 else
  if aa=32 then 29334634109 else
  if aa=33 then 23691316902 else
  if aa=34 then 18331557851 else
  if aa=35 then 12192475849 else
  if aa=36 then 9519300241 else
  0

theorem raw_first_cost_upper_37 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 37 ≤ (1688472771598/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 36) :
      rawRow 37 aa ≤ rowGrid_37 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 36 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_37,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 37 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 36,rowGrid_37 aa/10000000000)+(0/10000000000 : ℝ)=(1688472771598/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_37]
  change (∑ aa ∈ Finset.Icc 2 36,rawRow 37 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 37 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_37 : c ≤ coefficient profile 37 := by
  have hf := raw_first_cost_upper_37
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 37-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 37-1-
      (K*C/young 37)*(37 : ℝ)^2-(1688472771598/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 37 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 37-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 37-1-
      ((K*C/young 37)*(37 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 37+
        t 3*tripleHarmonicNeighborCharge K young zeta 37)
  linarith only [hf,hn]

def rowGrid_38 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 34329011560 else
  if aa=9 then 36614123565 else
  if aa=10 then 38821628756 else
  if aa=11 then 40905547174 else
  if aa=12 then 42885270927 else
  if aa=13 then 44868537214 else
  if aa=14 then 46798378863 else
  if aa=15 then 48648487702 else
  if aa=16 then 50416351443 else
  if aa=17 then 52029643967 else
  if aa=18 then 53463496696 else
  if aa=19 then 54684999453 else
  if aa=20 then 55659139651 else
  if aa=21 then 56349302987 else
  if aa=22 then 56718736366 else
  if aa=23 then 56732301986 else
  if aa=24 then 56369356562 else
  if aa=25 then 55789658134 else
  if aa=26 then 54767967253 else
  if aa=27 then 53244406861 else
  if aa=28 then 50984583872 else
  if aa=29 then 47851477962 else
  if aa=30 then 43989198495 else
  if aa=31 then 39372783760 else
  if aa=32 then 35304609853 else
  if aa=33 then 29334634109 else
  if aa=34 then 23691316902 else
  if aa=35 then 18331557851 else
  if aa=36 then 12192475849 else
  if aa=37 then 9519300241 else
  0

theorem raw_first_cost_upper_38 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 38 ≤ (1798312057667/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 37) :
      rawRow 38 aa ≤ rowGrid_38 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 37 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_38,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 38 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 37,rowGrid_38 aa/10000000000)+(0/10000000000 : ℝ)=(1798312057667/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_38]
  change (∑ aa ∈ Finset.Icc 2 37,rawRow 38 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 38 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_38 : c ≤ coefficient profile 38 := by
  have hf := raw_first_cost_upper_38
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 38-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 38-1-
      (K*C/young 38)*(38 : ℝ)^2-(1798312057667/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 38 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 38-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 38-1-
      ((K*C/young 38)*(38 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 38+
        t 3*tripleHarmonicNeighborCharge K young zeta 38)
  linarith only [hf,hn]

def rowGrid_39 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 36658928008 else
  if aa=10 then 38969881190 else
  if aa=11 then 41152457930 else
  if aa=12 then 43178731384 else
  if aa=13 then 45083326448 else
  if aa=14 then 46988235080 else
  if aa=15 then 48838757858 else
  if aa=16 then 50610956551 else
  if aa=17 then 52304567240 else
  if aa=18 then 53846251809 else
  if aa=19 then 55212317938 else
  if aa=20 then 56370024860 else
  if aa=21 then 57284301051 else
  if aa=22 then 57918335227 else
  if aa=23 then 58235100078 else
  if aa=24 then 58199135880 else
  if aa=25 then 57789716461 else
  if aa=26 then 57170908368 else
  if aa=27 then 56111962532 else
  if aa=28 then 54384648724 else
  if aa=29 then 51858710934 else
  if aa=30 then 48642334570 else
  if aa=31 then 44691049926 else
  if aa=32 then 41486370294 else
  if aa=33 then 35304609853 else
  if aa=34 then 29334634109 else
  if aa=35 then 23691316902 else
  if aa=36 then 18331557851 else
  if aa=37 then 12192475849 else
  if aa=38 then 9519300241 else
  0

theorem raw_first_cost_upper_39 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 39 ≤ (1912027864788/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 38) :
      rawRow 39 aa ≤ rowGrid_39 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 38 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_39,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 39 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 38,rowGrid_39 aa/10000000000)+(0/10000000000 : ℝ)=(1912027864788/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_39]
  change (∑ aa ∈ Finset.Icc 2 38,rawRow 39 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 39 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_39 : c ≤ coefficient profile 39 := by
  have hf := raw_first_cost_upper_39
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 39-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 39-1-
      (K*C/young 39)*(39 : ℝ)^2-(1912027864788/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 39 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 39-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 39-1-
      ((K*C/young 39)*(39 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 39+
        t 3*tripleHarmonicNeighborCharge K young zeta 39)
  linarith only [hf,hn]

def rowGrid_40 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 39017568357 else
  if aa=11 then 41309611359 else
  if aa=12 then 43439363351 else
  if aa=13 then 45391828022 else
  if aa=14 then 47213171475 else
  if aa=15 then 49036891683 else
  if aa=16 then 50808902162 else
  if aa=17 then 52506460786 else
  if aa=18 then 54130773990 else
  if aa=19 then 55607593188 else
  if aa=20 then 56913591768 else
  if aa=21 then 58015943016 else
  if aa=22 then 58879368079 else
  if aa=23 then 59466769968 else
  if aa=24 then 59740789353 else
  if aa=25 then 59665601417 else
  if aa=26 then 59220484494 else
  if aa=27 then 58573871355 else
  if aa=28 then 57313613794 else
  if aa=29 then 55317069655 else
  if aa=30 then 52715796357 else
  if aa=31 then 49418427186 else
  if aa=32 then 47090128485 else
  if aa=33 then 41486370294 else
  if aa=34 then 35304609853 else
  if aa=35 then 29334634109 else
  if aa=36 then 23691316902 else
  if aa=37 then 18331557851 else
  if aa=38 then 12192475849 else
  if aa=39 then 9519300241 else
  0

theorem raw_first_cost_upper_40 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 40 ≤ (2029300129484/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 39) :
      rawRow 40 aa ≤ rowGrid_40 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 39 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_40,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 40 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 39,rowGrid_40 aa/10000000000)+(0/10000000000 : ℝ)=(2029300129484/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_40]
  change (∑ aa ∈ Finset.Icc 2 39,rawRow 40 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 40 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_40 : c ≤ coefficient profile 40 := by
  have hf := raw_first_cost_upper_40
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 40-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 40-1-
      (K*C/young 40)*(40 : ℝ)^2-(2029300129484/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 40 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 40-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 40-1-
      ((K*C/young 40)*(40 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 40+
        t 3*tripleHarmonicNeighborCharge K young zeta 40)
  linarith only [hf,hn]

def rowGrid_41 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 41360161636 else
  if aa=12 then 43605250038 else
  if aa=13 then 45665818503 else
  if aa=14 then 47536247407 else
  if aa=15 then 49271635159 else
  if aa=16 then 51015028660 else
  if aa=17 then 52711819944 else
  if aa=18 then 54339716622 else
  if aa=19 then 55901422250 else
  if aa=20 then 57321046754 else
  if aa=21 then 58575381243 else
  if aa=22 then 59631382431 else
  if aa=23 then 60453495834 else
  if aa=24 then 61004304506 else
  if aa=25 then 61246100513 else
  if aa=26 then 61142812941 else
  if aa=27 then 60673743680 else
  if aa=28 then 59828244990 else
  if aa=29 then 58296251623 else
  if aa=30 then 56231312474 else
  if aa=31 then 53556881405 else
  if aa=32 then 52071278020 else
  if aa=33 then 47090128485 else
  if aa=34 then 41486370294 else
  if aa=35 then 35304609853 else
  if aa=36 then 29334634109 else
  if aa=37 then 23691316902 else
  if aa=38 then 18331557851 else
  if aa=39 then 12192475849 else
  if aa=40 then 9519300241 else
  0

theorem raw_first_cost_upper_41 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 41 ≤ (2150032458437/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 40) :
      rawRow 41 aa ≤ rowGrid_41 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 40 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_41,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 41 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 40,rowGrid_41 aa/10000000000)+(0/10000000000 : ℝ)=(2150032458437/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_41]
  change (∑ aa ∈ Finset.Icc 2 40,rawRow 41 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 41 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_41 : c ≤ coefficient profile 41 := by
  have hf := raw_first_cost_upper_41
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 41-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 41-1-
      (K*C/young 41)*(41 : ℝ)^2-(2150032458437/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 41 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 41-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 41-1-
      ((K*C/young 41)*(41 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 41+
        t 3*tripleHarmonicNeighborCharge K young zeta 41)
  linarith only [hf,hn]

def rowGrid_42 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 43658609472 else
  if aa=13 then 45840207600 else
  if aa=14 then 47823181859 else
  if aa=15 then 49608796992 else
  if aa=16 then 51259241634 else
  if aa=17 then 52925666384 else
  if aa=18 then 54552245867 else
  if aa=19 then 56117199514 else
  if aa=20 then 57623929660 else
  if aa=21 then 58994733289 else
  if aa=22 then 60206398076 else
  if aa=23 then 61225615135 else
  if aa=24 then 62016542521 else
  if aa=25 then 62541452934 else
  if aa=26 then 62762442314 else
  if aa=27 then 62643245695 else
  if aa=28 then 61973086590 else
  if aa=29 then 60853995992 else
  if aa=30 then 59259732330 else
  if aa=31 then 57128487883 else
  if aa=32 then 56431890295 else
  if aa=33 then 52071278020 else
  if aa=34 then 47090128485 else
  if aa=35 then 41486370294 else
  if aa=36 then 35304609853 else
  if aa=37 then 29334634109 else
  if aa=38 then 23691316902 else
  if aa=39 then 18331557851 else
  if aa=40 then 12192475849 else
  if aa=41 then 9519300241 else
  0

theorem raw_first_cost_upper_42 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 42 ≤ (2274090648056/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 41) :
      rawRow 42 aa ≤ rowGrid_42 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 41 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_42,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 42 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 41,rowGrid_42 aa/10000000000)+(0/10000000000 : ℝ)=(2274090648056/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_42]
  change (∑ aa ∈ Finset.Icc 2 41,rawRow 42 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 42 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_42 : c ≤ coefficient profile 42 := by
  have hf := raw_first_cost_upper_42
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 42-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 42-1-
      (K*C/young 42)*(42 : ℝ)^2-(2274090648056/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 42 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 42-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 42-1-
      ((K*C/young 42)*(42 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 42+
        t 3*tripleHarmonicNeighborCharge K young zeta 42)
  linarith only [hf,hn]

def rowGrid_43 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 45896301936 else
  if aa=14 then 48005809517 else
  if aa=15 then 49908241601 else
  if aa=16 then 51610004499 else
  if aa=17 then 53179025732 else
  if aa=18 then 54773558726 else
  if aa=19 then 56336680711 else
  if aa=20 then 57846355733 else
  if aa=21 then 59306459911 else
  if aa=22 then 60637426874 else
  if aa=23 then 61816003704 else
  if aa=24 then 62808625242 else
  if aa=25 then 63579196691 else
  if aa=26 then 64089865299 else
  if aa=27 then 64302620457 else
  if aa=28 then 63984765967 else
  if aa=29 then 63035610749 else
  if aa=30 then 61859749355 else
  if aa=31 then 60205226437 else
  if aa=32 then 60195225643 else
  if aa=33 then 56431890295 else
  if aa=34 then 52071278020 else
  if aa=35 then 47090128485 else
  if aa=36 then 41486370294 else
  if aa=37 then 35304609853 else
  if aa=38 then 29334634109 else
  if aa=39 then 23691316902 else
  if aa=40 then 18331557851 else
  if aa=41 then 12192475849 else
  if aa=42 then 9519300241 else
  0

theorem raw_first_cost_upper_43 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 43 ≤ (2401321296078/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 42) :
      rawRow 43 aa ≤ rowGrid_43 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 42 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_43,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 43 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 42,rowGrid_43 aa/10000000000)+(0/10000000000 : ℝ)=(2401321296078/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_43]
  change (∑ aa ∈ Finset.Icc 2 42,rawRow 43 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 43 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_43 : c ≤ coefficient profile 43 := by
  have hf := raw_first_cost_upper_43
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 43-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 43-1-
      (K*C/young 43)*(43 : ℝ)^2-(2401321296078/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 43 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 43-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 43-1-
      ((K*C/young 43)*(43 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 43+
        t 3*tripleHarmonicNeighborCharge K young zeta 43)
  linarith only [hf,hn]

def rowGrid_44 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 48064553885 else
  if aa=15 then 50098831707 else
  if aa=16 then 51921528635 else
  if aa=17 then 53542925525 else
  if aa=18 then 55035764081 else
  if aa=19 then 56565232839 else
  if aa=20 then 58072599871 else
  if aa=21 then 59535380484 else
  if aa=22 then 60957833446 else
  if aa=23 then 62258555969 else
  if aa=24 then 63414278519 else
  if aa=25 then 64391237819 else
  if aa=26 then 65153301700 else
  if aa=27 then 65662618144 else
  if aa=28 then 65679676642 else
  if aa=29 then 65081780225 else
  if aa=30 then 64077420353 else
  if aa=31 then 62846726957 else
  if aa=32 then 63437127860 else
  if aa=33 then 60195225643 else
  if aa=34 then 56431890295 else
  if aa=35 then 52071278020 else
  if aa=36 then 47090128485 else
  if aa=37 then 41486370294 else
  if aa=38 then 35304609853 else
  if aa=39 then 29334634109 else
  if aa=40 then 23691316902 else
  if aa=41 then 18331557851 else
  if aa=42 then 12192475849 else
  if aa=43 then 9519300241 else
  0

theorem raw_first_cost_upper_44 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 44 ≤ (2531565769163/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 43) :
      rawRow 44 aa ≤ rowGrid_44 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 43 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_44,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 44 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 43,rowGrid_44 aa/10000000000)+(0/10000000000 : ℝ)=(2531565769163/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_44]
  change (∑ aa ∈ Finset.Icc 2 43,rawRow 44 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 44 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_44 : c ≤ coefficient profile 44 := by
  have hf := raw_first_cost_upper_44
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 44-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 44-1-
      (K*C/young 44)*(44 : ℝ)^2-(2531565769163/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 44 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 44-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 44-1-
      ((K*C/young 44)*(44 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 44+
        t 3*tripleHarmonicNeighborCharge K young zeta 44)
  linarith only [hf,hn]

def rowGrid_45 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 50160137291 else
  if aa=16 then 52119807101 else
  if aa=17 then 53866117002 else
  if aa=18 then 55412369384 else
  if aa=19 then 56836015079 else
  if aa=20 then 58308194444 else
  if aa=21 then 59768230603 else
  if aa=22 then 61193128255 else
  if aa=23 then 62587528544 else
  if aa=24 then 63868273129 else
  if aa=25 then 65012151969 else
  if aa=26 then 65985447486 else
  if aa=27 then 66752151069 else
  if aa=28 then 67068799008 else
  if aa=29 then 66805750023 else
  if aa=30 then 66157407523 else
  if aa=31 then 65099781085 else
  if aa=32 then 66220427851 else
  if aa=33 then 63437127860 else
  if aa=34 then 60195225643 else
  if aa=35 then 56431890295 else
  if aa=36 then 52071278020 else
  if aa=37 then 47090128485 else
  if aa=38 then 41486370294 else
  if aa=39 then 35304609853 else
  if aa=40 then 29334634109 else
  if aa=41 then 23691316902 else
  if aa=42 then 18331557851 else
  if aa=43 then 12192475849 else
  if aa=44 then 9519300241 else
  0

theorem raw_first_cost_upper_45 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 45 ≤ (2664668078500/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 44) :
      rawRow 45 aa ≤ rowGrid_45 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 44 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_45,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 45 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 44,rowGrid_45 aa/10000000000)+(0/10000000000 : ℝ)=(2664668078500/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_45]
  change (∑ aa ∈ Finset.Icc 2 44,rawRow 45 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 45 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_45 : c ≤ coefficient profile 45 := by
  have hf := raw_first_cost_upper_45
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 45-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 45-1-
      (K*C/young 45)*(45 : ℝ)^2-(2664668078500/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 45 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 45-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 45-1-
      ((K*C/young 45)*(45 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 45+
        t 3*tripleHarmonicNeighborCharge K young zeta 45)
  linarith only [hf,hn]

def rowGrid_46 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 52183585739 else
  if aa=17 then 54071821483 else
  if aa=18 then 55746845047 else
  if aa=19 then 57224939355 else
  if aa=20 then 58587320380 else
  if aa=21 then 60010704176 else
  if aa=22 then 61432462027 else
  if aa=23 then 62829113911 else
  if aa=24 then 64205751408 else
  if aa=25 then 65477586053 else
  if aa=26 then 66621734338 else
  if aa=27 then 67604717550 else
  if aa=28 then 68181664544 else
  if aa=29 then 68218688794 else
  if aa=30 then 67909869919 else
  if aa=31 then 67212954629 else
  if aa=32 then 68594429101 else
  if aa=33 then 66220427851 else
  if aa=34 then 63437127860 else
  if aa=35 then 60195225643 else
  if aa=36 then 56431890295 else
  if aa=37 then 52071278020 else
  if aa=38 then 47090128485 else
  if aa=39 then 41486370294 else
  if aa=40 then 35304609853 else
  if aa=41 then 29334634109 else
  if aa=42 then 23691316902 else
  if aa=43 then 18331557851 else
  if aa=44 then 12192475849 else
  if aa=45 then 9519300241 else
  0

theorem raw_first_cost_upper_46 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 46 ≤ (2800479451596/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 45) :
      rawRow 46 aa ≤ rowGrid_46 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 45 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_46,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 46 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 45,rowGrid_46 aa/10000000000)+(0/10000000000 : ℝ)=(2800479451596/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_46]
  change (∑ aa ∈ Finset.Icc 2 45,rawRow 46 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 46 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_46 : c ≤ coefficient profile 46 := by
  have hf := raw_first_cost_upper_46
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 46-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 46-1-
      (K*C/young 46)*(46 : ℝ)^2-(2800479451596/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 46 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 46-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 46-1-
      ((K*C/young 46)*(46 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 46+
        t 3*tripleHarmonicNeighborCharge K young zeta 46)
  linarith only [hf,hn]

def rowGrid_47 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 54137988787 else
  if aa=18 then 55959731672 else
  if aa=19 then 57570355907 else
  if aa=20 then 58988228697 else
  if aa=21 then 60297980160 else
  if aa=22 then 61681687216 else
  if aa=23 then 63074846222 else
  if aa=24 then 64453583051 else
  if aa=25 then 65823567898 else
  if aa=26 then 67098691721 else
  if aa=27 then 68256618758 else
  if aa=28 then 69052488943 else
  if aa=29 then 69350634330 else
  if aa=30 then 69346160779 else
  if aa=31 then 68993377712 else
  if aa=32 then 70821040780 else
  if aa=33 then 68594429101 else
  if aa=34 then 66220427851 else
  if aa=35 then 63437127860 else
  if aa=36 then 60195225643 else
  if aa=37 then 56431890295 else
  if aa=38 then 52071278020 else
  if aa=39 then 47090128485 else
  if aa=40 then 41486370294 else
  if aa=41 then 35304609853 else
  if aa=42 then 29334634109 else
  if aa=43 then 23691316902 else
  if aa=44 then 18331557851 else
  if aa=45 then 12192475849 else
  if aa=46 then 9519300241 else
  0

theorem raw_first_cost_upper_47 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 47 ≤ (2938869340498/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 46) :
      rawRow 47 aa ≤ rowGrid_47 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 46 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_47,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 47 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 46,rowGrid_47 aa/10000000000)+(0/10000000000 : ℝ)=(2938869340498/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_47]
  change (∑ aa ∈ Finset.Icc 2 46,rawRow 47 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 47 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_47 : c ≤ coefficient profile 47 := by
  have hf := raw_first_cost_upper_47
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 47-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 47-1-
      (K*C/young 47)*(47 : ℝ)^2-(2938869340498/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 47 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 47-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 47-1-
      ((K*C/young 47)*(47 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 47+
        t 3*tripleHarmonicNeighborCharge K young zeta 47)
  linarith only [hf,hn]

def rowGrid_48 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 56028209198 else
  if aa=19 then 57790206173 else
  if aa=20 then 59344288673 else
  if aa=21 then 60710594385 else
  if aa=22 then 61976962328 else
  if aa=23 then 63330734395 else
  if aa=24 then 64705668859 else
  if aa=25 then 66077644249 else
  if aa=26 then 67453239447 else
  if aa=27 then 68745280583 else
  if aa=28 then 69718350773 else
  if aa=29 then 70236388951 else
  if aa=30 then 70496814339 else
  if aa=31 then 70452584716 else
  if aa=32 then 72697039484 else
  if aa=33 then 70821040780 else
  if aa=34 then 68594429101 else
  if aa=35 then 66220427851 else
  if aa=36 then 63437127860 else
  if aa=37 then 60195225643 else
  if aa=38 then 56431890295 else
  if aa=39 then 52071278020 else
  if aa=40 then 47090128485 else
  if aa=41 then 41486370294 else
  if aa=42 then 35304609853 else
  if aa=43 then 29334634109 else
  if aa=44 then 23691316902 else
  if aa=45 then 18331557851 else
  if aa=46 then 12192475849 else
  if aa=47 then 9519300241 else
  0

theorem raw_first_cost_upper_48 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 48 ≤ (3079707392417/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 47) :
      rawRow 48 aa ≤ rowGrid_48 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 47 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_48,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 48 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 47,rowGrid_48 aa/10000000000)+(0/10000000000 : ℝ)=(3079707392417/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_48]
  change (∑ aa ∈ Finset.Icc 2 47,rawRow 48 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 48 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_48 : c ≤ coefficient profile 48 := by
  have hf := raw_first_cost_upper_48
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 48-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 48-1-
      (K*C/young 48)*(48 : ℝ)^2-(3079707392417/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 48 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 48-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 48-1-
      ((K*C/young 48)*(48 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 48+
        t 3*tripleHarmonicNeighborCharge K young zeta 48)
  linarith only [hf,hn]

def rowGrid_49 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 119180782289 else
  if aa=19 then 57860923638 else
  if aa=20 then 59570913252 else
  if aa=21 then 61077050765 else
  if aa=22 then 62401065693 else
  if aa=23 then 63633903626 else
  if aa=24 then 64968173112 else
  if aa=25 then 66336081957 else
  if aa=26 then 67713606265 else
  if aa=27 then 69108528841 else
  if aa=28 then 70217477410 else
  if aa=29 then 70913666935 else
  if aa=30 then 71397208109 else
  if aa=31 then 71621597052 else
  if aa=32 then 74234578777 else
  if aa=33 then 72697039484 else
  if aa=34 then 70821040780 else
  if aa=35 then 68594429101 else
  if aa=36 then 66220427851 else
  if aa=37 then 63437127860 else
  if aa=38 then 60195225643 else
  if aa=39 then 56431890295 else
  if aa=40 then 52071278020 else
  if aa=41 then 47090128485 else
  if aa=42 then 41486370294 else
  if aa=43 then 35304609853 else
  if aa=44 then 29334634109 else
  if aa=45 then 23691316902 else
  if aa=46 then 18331557851 else
  if aa=47 then 12192475849 else
  if aa=48 then 9519300241 else
  0

theorem raw_first_cost_upper_49 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 49 ≤ (3222875983069/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 48) :
      rawRow 49 aa ≤ rowGrid_49 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 48 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_49,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 49 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 48,rowGrid_49 aa/10000000000)+(0/10000000000 : ℝ)=(3222875983069/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_49]
  change (∑ aa ∈ Finset.Icc 2 48,rawRow 49 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 49 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_49 : c ≤ coefficient profile 49 := by
  have hf := raw_first_cost_upper_49
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 49-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 49-1-
      (K*C/young 49)*(49 : ℝ)^2-(3222875983069/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 49 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 49-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 49-1-
      ((K*C/young 49)*(49 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 49+
        t 3*tripleHarmonicNeighborCharge K young zeta 49)
  linarith only [hf,hn]

def rowGrid_50 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 119180782289 else
  if aa=19 then 123079253144 else
  if aa=20 then 59643809756 else
  if aa=21 then 61310292434 else
  if aa=22 then 62777725960 else
  if aa=23 then 64069345307 else
  if aa=24 then 65279180891 else
  if aa=25 then 66605200629 else
  if aa=26 then 67978442420 else
  if aa=27 then 69375285010 else
  if aa=28 then 70588504717 else
  if aa=29 then 71421351062 else
  if aa=30 then 72085679681 else
  if aa=31 then 72536356682 else
  if aa=32 then 75466345343 else
  if aa=33 then 74234578777 else
  if aa=34 then 72697039484 else
  if aa=35 then 70821040780 else
  if aa=36 then 68594429101 else
  if aa=37 then 66220427851 else
  if aa=38 then 63437127860 else
  if aa=39 then 60195225643 else
  if aa=40 then 56431890295 else
  if aa=41 then 52071278020 else
  if aa=42 then 47090128485 else
  if aa=43 then 41486370294 else
  if aa=44 then 35304609853 else
  if aa=45 then 29334634109 else
  if aa=46 then 23691316902 else
  if aa=47 then 18331557851 else
  if aa=48 then 12192475849 else
  if aa=49 then 9519300241 else
  0

theorem raw_first_cost_upper_50 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 50 ≤ (3368272559450/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 49) :
      rawRow 50 aa ≤ rowGrid_50 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 49 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_50,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 50 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 49,rowGrid_50 aa/10000000000)+(0/10000000000 : ℝ)=(3368272559450/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_50]
  change (∑ aa ∈ Finset.Icc 2 49,rawRow 50 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 50 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_50 : c ≤ coefficient profile 50 := by
  have hf := raw_first_cost_upper_50
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 50-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 50-1-
      (K*C/young 50)*(50 : ℝ)^2-(3368272559450/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 50 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 50-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 50-1-
      ((K*C/young 50)*(50 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 50+
        t 3*tripleHarmonicNeighborCharge K young zeta 50)
  linarith only [hf,hn]

def rowGrid_51 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 119180782289 else
  if aa=19 then 123079253144 else
  if aa=20 then 126871731350 else
  if aa=21 then 61385317403 else
  if aa=22 then 63017462184 else
  if aa=23 then 64456075508 else
  if aa=24 then 65725881072 else
  if aa=25 then 66924044989 else
  if aa=26 then 68254223979 else
  if aa=27 then 69646620193 else
  if aa=28 then 70860973533 else
  if aa=29 then 71798739606 else
  if aa=30 then 72601754466 else
  if aa=31 then 73235812878 else
  if aa=32 then 76430210559 else
  if aa=33 then 75466345343 else
  if aa=34 then 74234578777 else
  if aa=35 then 72697039484 else
  if aa=36 then 70821040780 else
  if aa=37 then 68594429101 else
  if aa=38 then 66220427851 else
  if aa=39 then 63437127860 else
  if aa=40 then 60195225643 else
  if aa=41 then 56431890295 else
  if aa=42 then 52071278020 else
  if aa=43 then 47090128485 else
  if aa=44 then 41486370294 else
  if aa=45 then 35304609853 else
  if aa=46 then 29334634109 else
  if aa=47 then 23691316902 else
  if aa=48 then 18331557851 else
  if aa=49 then 12192475849 else
  if aa=50 then 9519300241 else
  0

theorem raw_first_cost_upper_51 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 51 ≤ (3515810232621/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 50) :
      rawRow 51 aa ≤ rowGrid_51 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 50 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_51,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 51 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 50,rowGrid_51 aa/10000000000)+(0/10000000000 : ℝ)=(3515810232621/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_51]
  change (∑ aa ∈ Finset.Icc 2 50,rawRow 51 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 51 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_51 : c ≤ coefficient profile 51 := by
  have hf := raw_first_cost_upper_51
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 51-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 51-1-
      (K*C/young 51)*(51 : ℝ)^2-(3515810232621/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 51 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 51-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 51-1-
      ((K*C/young 51)*(51 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 51+
        t 3*tripleHarmonicNeighborCharge K young zeta 51)
  linarith only [hf,hn]

def rowGrid_52 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 119180782289 else
  if aa=19 then 123079253144 else
  if aa=20 then 126871731350 else
  if aa=21 then 130576191063 else
  if aa=22 then 63094576205 else
  if aa=23 then 64702221031 else
  if aa=24 then 66122610320 else
  if aa=25 then 67382000842 else
  if aa=26 then 68580962344 else
  if aa=27 then 69929169378 else
  if aa=28 then 71138119425 else
  if aa=29 then 72075879881 else
  if aa=30 then 72985380230 else
  if aa=31 then 73760121679 else
  if aa=32 then 77167214549 else
  if aa=33 then 76430210559 else
  if aa=34 then 75466345343 else
  if aa=35 then 74234578777 else
  if aa=36 then 72697039484 else
  if aa=37 then 70821040780 else
  if aa=38 then 68594429101 else
  if aa=39 then 66220427851 else
  if aa=40 then 63437127860 else
  if aa=41 then 60195225643 else
  if aa=42 then 56431890295 else
  if aa=43 then 52071278020 else
  if aa=44 then 47090128485 else
  if aa=45 then 41486370294 else
  if aa=46 then 35304609853 else
  if aa=47 then 29334634109 else
  if aa=48 then 23691316902 else
  if aa=49 then 18331557851 else
  if aa=50 then 12192475849 else
  if aa=51 then 9519300241 else
  0

theorem raw_first_cost_upper_52 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 52 ≤ (3665417773757/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 51) :
      rawRow 52 aa ≤ rowGrid_52 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 51 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_52,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 52 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 51,rowGrid_52 aa/10000000000)+(0/10000000000 : ℝ)=(3665417773757/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_52]
  change (∑ aa ∈ Finset.Icc 2 51,rawRow 52 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 52 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_52 : c ≤ coefficient profile 52 := by
  have hf := raw_first_cost_upper_52
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 52-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 52-1-
      (K*C/young 52)*(52 : ℝ)^2-(3665417773757/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 52 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 52-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 52-1-
      ((K*C/young 52)*(52 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 52+
        t 3*tripleHarmonicNeighborCharge K young zeta 52)
  linarith only [hf,hn]

def rowGrid_53 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 119180782289 else
  if aa=19 then 123079253144 else
  if aa=20 then 126871731350 else
  if aa=21 then 130576191063 else
  if aa=22 then 134212052427 else
  if aa=23 then 64781396679 else
  if aa=24 then 66375120024 else
  if aa=25 then 67788726626 else
  if aa=26 then 69050256349 else
  if aa=27 then 70263925839 else
  if aa=28 then 71426719469 else
  if aa=29 then 72357777419 else
  if aa=30 then 73267100891 else
  if aa=31 then 74149868226 else
  if aa=32 then 77719668986 else
  if aa=33 then 77167214549 else
  if aa=34 then 76430210559 else
  if aa=35 then 75466345343 else
  if aa=36 then 74234578777 else
  if aa=37 then 72697039484 else
  if aa=38 then 70821040780 else
  if aa=39 then 68594429101 else
  if aa=40 then 66220427851 else
  if aa=41 then 63437127860 else
  if aa=42 then 60195225643 else
  if aa=43 then 56431890295 else
  if aa=44 then 52071278020 else
  if aa=45 then 47090128485 else
  if aa=46 then 41486370294 else
  if aa=47 then 35304609853 else
  if aa=48 then 29334634109 else
  if aa=49 then 23691316902 else
  if aa=50 then 18331557851 else
  if aa=51 then 12192475849 else
  if aa=52 then 9519300241 else
  0

theorem raw_first_cost_upper_53 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 53 ≤ (3817039345357/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 52) :
      rawRow 53 aa ≤ rowGrid_53 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 52 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_53,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 53 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 52,rowGrid_53 aa/10000000000)+(0/10000000000 : ℝ)=(3817039345357/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_53]
  change (∑ aa ∈ Finset.Icc 2 52,rawRow 53 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 53 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_53 : c ≤ coefficient profile 53 := by
  have hf := raw_first_cost_upper_53
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 53-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 53-1-
      (K*C/young 53)*(53 : ℝ)^2-(3817039345357/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 53 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 53-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 53-1-
      ((K*C/young 53)*(53 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 53+
        t 3*tripleHarmonicNeighborCharge K young zeta 53)
  linarith only [hf,hn]

def rowGrid_54 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 119180782289 else
  if aa=19 then 123079253144 else
  if aa=20 then 126871731350 else
  if aa=21 then 130576191063 else
  if aa=22 then 134212052427 else
  if aa=23 then 137800183953 else
  if aa=24 then 66456342786 else
  if aa=25 then 68047598912 else
  if aa=26 then 69467051923 else
  if aa=27 then 70744736227 else
  if aa=28 then 71768644821 else
  if aa=29 then 72651325491 else
  if aa=30 then 73553657439 else
  if aa=31 then 74436083764 else
  if aa=32 then 78130337677 else
  if aa=33 then 77719668986 else
  if aa=34 then 77167214549 else
  if aa=35 then 76430210559 else
  if aa=36 then 75466345343 else
  if aa=37 then 74234578777 else
  if aa=38 then 72697039484 else
  if aa=39 then 70821040780 else
  if aa=40 then 68594429101 else
  if aa=41 then 66220427851 else
  if aa=42 then 63437127860 else
  if aa=43 then 60195225643 else
  if aa=44 then 56431890295 else
  if aa=45 then 52071278020 else
  if aa=46 then 47090128485 else
  if aa=47 then 41486370294 else
  if aa=48 then 35304609853 else
  if aa=49 then 29334634109 else
  if aa=50 then 23691316902 else
  if aa=51 then 18331557851 else
  if aa=52 then 12192475849 else
  if aa=53 then 9519300241 else
  0

theorem raw_first_cost_upper_54 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 54 ≤ (3970634416828/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 53) :
      rawRow 54 aa ≤ rowGrid_54 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 53 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_54,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 54 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 53,rowGrid_54 aa/10000000000)+(0/10000000000 : ℝ)=(3970634416828/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_54]
  change (∑ aa ∈ Finset.Icc 2 53,rawRow 54 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 54 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_54 : c ≤ coefficient profile 54 := by
  have hf := raw_first_cost_upper_54
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 54-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 54-1-
      (K*C/young 54)*(54 : ℝ)^2-(3970634416828/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 54 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 54-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 54-1-
      ((K*C/young 54)*(54 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 54+
        t 3*tripleHarmonicNeighborCharge K young zeta 54)
  linarith only [hf,hn]

def rowGrid_55 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 119180782289 else
  if aa=19 then 123079253144 else
  if aa=20 then 126871731350 else
  if aa=21 then 130576191063 else
  if aa=22 then 134212052427 else
  if aa=23 then 137800183953 else
  if aa=24 then 141363056837 else
  if aa=25 then 68130868275 else
  if aa=26 then 69732333414 else
  if aa=27 then 71171759884 else
  if aa=28 then 72259751881 else
  if aa=29 then 72999113128 else
  if aa=30 then 73852057074 else
  if aa=31 then 74727212346 else
  if aa=32 then 78431917668 else
  if aa=33 then 78130337677 else
  if aa=34 then 77719668986 else
  if aa=35 then 77167214549 else
  if aa=36 then 76430210559 else
  if aa=37 then 75466345343 else
  if aa=38 then 74234578777 else
  if aa=39 then 72697039484 else
  if aa=40 then 70821040780 else
  if aa=41 then 68594429101 else
  if aa=42 then 66220427851 else
  if aa=43 then 63437127860 else
  if aa=44 then 60195225643 else
  if aa=45 then 56431890295 else
  if aa=46 then 52071278020 else
  if aa=47 then 47090128485 else
  if aa=48 then 41486370294 else
  if aa=49 then 35304609853 else
  if aa=50 then 29334634109 else
  if aa=51 then 23691316902 else
  if aa=52 then 18331557851 else
  if aa=53 then 12192475849 else
  if aa=54 then 9519300241 else
  0

theorem raw_first_cost_upper_55 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 55 ≤ (4126177045972/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 54) :
      rawRow 55 aa ≤ rowGrid_55 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 54 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_55,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 55 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 54,rowGrid_55 aa/10000000000)+(0/10000000000 : ℝ)=(4126177045972/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_55]
  change (∑ aa ∈ Finset.Icc 2 54,rawRow 55 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 55 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_55 : c ≤ coefficient profile 55 := by
  have hf := raw_first_cost_upper_55
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 55-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 55-1-
      (K*C/young 55)*(55 : ℝ)^2-(4126177045972/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 55 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 55-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 55-1-
      ((K*C/young 55)*(55 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 55+
        t 3*tripleHarmonicNeighborCharge K young zeta 55)
  linarith only [hf,hn]

def rowGrid_56 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 119180782289 else
  if aa=19 then 123079253144 else
  if aa=20 then 126871731350 else
  if aa=21 then 130576191063 else
  if aa=22 then 134212052427 else
  if aa=23 then 137800183953 else
  if aa=24 then 141363056837 else
  if aa=25 then 144925035001 else
  if aa=26 then 69817664375 else
  if aa=27 then 71443551331 else
  if aa=28 then 72695920352 else
  if aa=29 then 73498640183 else
  if aa=30 then 74205592708 else
  if aa=31 then 75030372972 else
  if aa=32 then 78738674444 else
  if aa=33 then 78431917668 else
  if aa=34 then 78130337677 else
  if aa=35 then 77719668986 else
  if aa=36 then 77167214549 else
  if aa=37 then 76430210559 else
  if aa=38 then 75466345343 else
  if aa=39 then 74234578777 else
  if aa=40 then 72697039484 else
  if aa=41 then 70821040780 else
  if aa=42 then 68594429101 else
  if aa=43 then 66220427851 else
  if aa=44 then 63437127860 else
  if aa=45 then 60195225643 else
  if aa=46 then 56431890295 else
  if aa=47 then 52071278020 else
  if aa=48 then 47090128485 else
  if aa=49 then 41486370294 else
  if aa=50 then 35304609853 else
  if aa=51 then 29334634109 else
  if aa=52 then 23691316902 else
  if aa=53 then 18331557851 else
  if aa=54 then 12192475849 else
  if aa=55 then 9519300241 else
  0

theorem raw_first_cost_upper_56 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 56 ≤ (4283659401336/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 55) :
      rawRow 56 aa ≤ rowGrid_56 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 55 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_56,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 56 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 55,rowGrid_56 aa/10000000000)+(0/10000000000 : ℝ)=(4283659401336/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_56]
  change (∑ aa ∈ Finset.Icc 2 55,rawRow 56 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 56 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_56 : c ≤ coefficient profile 56 := by
  have hf := raw_first_cost_upper_56
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 56-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 56-1-
      (K*C/young 56)*(56 : ℝ)^2-(4283659401336/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 56 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 56-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 56-1-
      ((K*C/young 56)*(56 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 56+
        t 3*tripleHarmonicNeighborCharge K young zeta 56)
  linarith only [hf,hn]

def rowGrid_57 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 119180782289 else
  if aa=19 then 123079253144 else
  if aa=20 then 126871731350 else
  if aa=21 then 130576191063 else
  if aa=22 then 134212052427 else
  if aa=23 then 137800183953 else
  if aa=24 then 141363056837 else
  if aa=25 then 144925035001 else
  if aa=26 then 148513114677 else
  if aa=27 then 71530976297 else
  if aa=28 then 72973532279 else
  if aa=29 then 73942286732 else
  if aa=30 then 74713375606 else
  if aa=31 then 75389549298 else
  if aa=32 then 79058109160 else
  if aa=33 then 78738674444 else
  if aa=34 then 78431917668 else
  if aa=35 then 78130337677 else
  if aa=36 then 77719668986 else
  if aa=37 then 77167214549 else
  if aa=38 then 76430210559 else
  if aa=39 then 75466345343 else
  if aa=40 then 74234578777 else
  if aa=41 then 72697039484 else
  if aa=42 then 70821040780 else
  if aa=43 then 68594429101 else
  if aa=44 then 66220427851 else
  if aa=45 then 63437127860 else
  if aa=46 then 60195225643 else
  if aa=47 then 56431890295 else
  if aa=48 then 52071278020 else
  if aa=49 then 47090128485 else
  if aa=50 then 41486370294 else
  if aa=51 then 35304609853 else
  if aa=52 then 29334634109 else
  if aa=53 then 23691316902 else
  if aa=54 then 18331557851 else
  if aa=55 then 12192475849 else
  if aa=56 then 9519300241 else
  0

theorem raw_first_cost_upper_57 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 57 ≤ (4443088603464/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 56) :
      rawRow 57 aa ≤ rowGrid_57 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 56 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_57,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 57 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 56,rowGrid_57 aa/10000000000)+(0/10000000000 : ℝ)=(4443088603464/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_57]
  change (∑ aa ∈ Finset.Icc 2 56,rawRow 57 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 57 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_57 : c ≤ coefficient profile 57 := by
  have hf := raw_first_cost_upper_57
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 57-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 57-1-
      (K*C/young 57)*(57 : ℝ)^2-(4443088603464/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 57 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 57-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 57-1-
      ((K*C/young 57)*(57 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 57+
        t 3*tripleHarmonicNeighborCharge K young zeta 57)
  linarith only [hf,hn]

def rowGrid_58 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 119180782289 else
  if aa=19 then 123079253144 else
  if aa=20 then 126871731350 else
  if aa=21 then 130576191063 else
  if aa=22 then 134212052427 else
  if aa=23 then 137800183953 else
  if aa=24 then 141363056837 else
  if aa=25 then 144925035001 else
  if aa=26 then 148513114677 else
  if aa=27 then 152157597664 else
  if aa=28 then 73062829472 else
  if aa=29 then 74224658296 else
  if aa=30 then 75164354442 else
  if aa=31 then 75905433915 else
  if aa=32 then 79436566577 else
  if aa=33 then 79058109160 else
  if aa=34 then 78738674444 else
  if aa=35 then 78431917668 else
  if aa=36 then 78130337677 else
  if aa=37 then 77719668986 else
  if aa=38 then 77167214549 else
  if aa=39 then 76430210559 else
  if aa=40 then 75466345343 else
  if aa=41 then 74234578777 else
  if aa=42 then 72697039484 else
  if aa=43 then 70821040780 else
  if aa=44 then 68594429101 else
  if aa=45 then 66220427851 else
  if aa=46 then 63437127860 else
  if aa=47 then 60195225643 else
  if aa=48 then 56431890295 else
  if aa=49 then 52071278020 else
  if aa=50 then 47090128485 else
  if aa=51 then 41486370294 else
  if aa=52 then 35304609853 else
  if aa=53 then 29334634109 else
  if aa=54 then 23691316902 else
  if aa=55 then 18331557851 else
  if aa=56 then 12192475849 else
  if aa=57 then 9519300241 else
  0

theorem raw_first_cost_upper_58 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 58 ≤ (4604490323618/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 57) :
      rawRow 58 aa ≤ rowGrid_58 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 57 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_58,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 58 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 57,rowGrid_58 aa/10000000000)+(0/10000000000 : ℝ)=(4604490323618/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_58]
  change (∑ aa ∈ Finset.Icc 2 57,rawRow 58 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 58 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_58 : c ≤ coefficient profile 58 := by
  have hf := raw_first_cost_upper_58
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 58-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 58-1-
      (K*C/young 58)*(58 : ℝ)^2-(4604490323618/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 58 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 58-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 58-1-
      ((K*C/young 58)*(58 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 58+
        t 3*tripleHarmonicNeighborCharge K young zeta 58)
  linarith only [hf,hn]

def rowGrid_59 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 119180782289 else
  if aa=19 then 123079253144 else
  if aa=20 then 126871731350 else
  if aa=21 then 130576191063 else
  if aa=22 then 134212052427 else
  if aa=23 then 137800183953 else
  if aa=24 then 141363056837 else
  if aa=25 then 144925035001 else
  if aa=26 then 148513114677 else
  if aa=27 then 152157597664 else
  if aa=28 then 155416089455 else
  if aa=29 then 74315486483 else
  if aa=30 then 75451392851 else
  if aa=31 then 76363608158 else
  if aa=32 then 79980144608 else
  if aa=33 then 79436566577 else
  if aa=34 then 79058109160 else
  if aa=35 then 78738674444 else
  if aa=36 then 78431917668 else
  if aa=37 then 78130337677 else
  if aa=38 then 77719668986 else
  if aa=39 then 77167214549 else
  if aa=40 then 76430210559 else
  if aa=41 then 75466345343 else
  if aa=42 then 74234578777 else
  if aa=43 then 72697039484 else
  if aa=44 then 70821040780 else
  if aa=45 then 68594429101 else
  if aa=46 then 66220427851 else
  if aa=47 then 63437127860 else
  if aa=48 then 60195225643 else
  if aa=49 then 56431890295 else
  if aa=50 then 52071278020 else
  if aa=51 then 47090128485 else
  if aa=52 then 41486370294 else
  if aa=53 then 35304609853 else
  if aa=54 then 29334634109 else
  if aa=55 then 23691316902 else
  if aa=56 then 18331557851 else
  if aa=57 then 12192475849 else
  if aa=58 then 9519300241 else
  0

theorem raw_first_cost_upper_59 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 59 ≤ (4767659769048/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 58) :
      rawRow 59 aa ≤ rowGrid_59 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 58 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_59,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 59 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 58,rowGrid_59 aa/10000000000)+(0/10000000000 : ℝ)=(4767659769048/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_59]
  change (∑ aa ∈ Finset.Icc 2 58,rawRow 59 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 59 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_59 : c ≤ coefficient profile 59 := by
  have hf := raw_first_cost_upper_59
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 59-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 59-1-
      (K*C/young 59)*(59 : ℝ)^2-(4767659769048/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 59 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 59-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 59-1-
      ((K*C/young 59)*(59 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 59+
        t 3*tripleHarmonicNeighborCharge K young zeta 59)
  linarith only [hf,hn]

def rowGrid_60 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 119180782289 else
  if aa=19 then 123079253144 else
  if aa=20 then 126871731350 else
  if aa=21 then 130576191063 else
  if aa=22 then 134212052427 else
  if aa=23 then 137800183953 else
  if aa=24 then 141363056837 else
  if aa=25 then 144925035001 else
  if aa=26 then 148513114677 else
  if aa=27 then 152157597664 else
  if aa=28 then 155416089455 else
  if aa=29 then 158080687247 else
  if aa=30 then 75543722184 else
  if aa=31 then 76655226289 else
  if aa=32 then 80462914289 else
  if aa=33 then 79980144608 else
  if aa=34 then 79436566577 else
  if aa=35 then 79058109160 else
  if aa=36 then 78738674444 else
  if aa=37 then 78431917668 else
  if aa=38 then 78130337677 else
  if aa=39 then 77719668986 else
  if aa=40 then 77167214549 else
  if aa=41 then 76430210559 else
  if aa=42 then 75466345343 else
  if aa=43 then 74234578777 else
  if aa=44 then 72697039484 else
  if aa=45 then 70821040780 else
  if aa=46 then 68594429101 else
  if aa=47 then 66220427851 else
  if aa=48 then 63437127860 else
  if aa=49 then 60195225643 else
  if aa=50 then 56431890295 else
  if aa=51 then 52071278020 else
  if aa=52 then 47090128485 else
  if aa=53 then 41486370294 else
  if aa=54 then 35304609853 else
  if aa=55 then 29334634109 else
  if aa=56 then 23691316902 else
  if aa=57 then 18331557851 else
  if aa=58 then 12192475849 else
  if aa=59 then 9519300241 else
  0

theorem raw_first_cost_upper_60 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 60 ≤ (4932271831565/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 59) :
      rawRow 60 aa ≤ rowGrid_60 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 59 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_60,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 60 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 59,rowGrid_60 aa/10000000000)+(0/10000000000 : ℝ)=(4932271831565/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_60]
  change (∑ aa ∈ Finset.Icc 2 59,rawRow 60 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 60 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_60 : c ≤ coefficient profile 60 := by
  have hf := raw_first_cost_upper_60
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 60-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 60-1-
      (K*C/young 60)*(60 : ℝ)^2-(4932271831565/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 60 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 60-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 60-1-
      ((K*C/young 60)*(60 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 60+
        t 3*tripleHarmonicNeighborCharge K young zeta 60)
  linarith only [hf,hn]

def rowGrid_61 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 119180782289 else
  if aa=19 then 123079253144 else
  if aa=20 then 126871731350 else
  if aa=21 then 130576191063 else
  if aa=22 then 134212052427 else
  if aa=23 then 137800183953 else
  if aa=24 then 141363056837 else
  if aa=25 then 144925035001 else
  if aa=26 then 148513114677 else
  if aa=27 then 152157597664 else
  if aa=28 then 155416089455 else
  if aa=29 then 158080687247 else
  if aa=30 then 160693337085 else
  if aa=31 then 76749028744 else
  if aa=32 then 80770186893 else
  if aa=33 then 80462914289 else
  if aa=34 then 79980144608 else
  if aa=35 then 79436566577 else
  if aa=36 then 79058109160 else
  if aa=37 then 78738674444 else
  if aa=38 then 78431917668 else
  if aa=39 then 78130337677 else
  if aa=40 then 77719668986 else
  if aa=41 then 77167214549 else
  if aa=42 then 76430210559 else
  if aa=43 then 75466345343 else
  if aa=44 then 74234578777 else
  if aa=45 then 72697039484 else
  if aa=46 then 70821040780 else
  if aa=47 then 68594429101 else
  if aa=48 then 66220427851 else
  if aa=49 then 63437127860 else
  if aa=50 then 60195225643 else
  if aa=51 then 56431890295 else
  if aa=52 then 52071278020 else
  if aa=53 then 47090128485 else
  if aa=54 then 41486370294 else
  if aa=55 then 35304609853 else
  if aa=56 then 29334634109 else
  if aa=57 then 23691316902 else
  if aa=58 then 18331557851 else
  if aa=59 then 12192475849 else
  if aa=60 then 9519300241 else
  0

theorem raw_first_cost_upper_61 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 61 ≤ (5098285435814/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 60) :
      rawRow 61 aa ≤ rowGrid_61 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 60 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_61,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 61 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 60,rowGrid_61 aa/10000000000)+(0/10000000000 : ℝ)=(5098285435814/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_61]
  change (∑ aa ∈ Finset.Icc 2 60,rawRow 61 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 61 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_61 : c ≤ coefficient profile 61 := by
  have hf := raw_first_cost_upper_61
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 61-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 61-1-
      (K*C/young 61)*(61 : ℝ)^2-(5098285435814/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 61 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 61-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 61-1-
      ((K*C/young 61)*(61 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 61+
        t 3*tripleHarmonicNeighborCharge K young zeta 61)
  linarith only [hf,hn]

def rowGrid_62 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 119180782289 else
  if aa=19 then 123079253144 else
  if aa=20 then 126871731350 else
  if aa=21 then 130576191063 else
  if aa=22 then 134212052427 else
  if aa=23 then 137800183953 else
  if aa=24 then 141363056837 else
  if aa=25 then 144925035001 else
  if aa=26 then 148513114677 else
  if aa=27 then 152157597664 else
  if aa=28 then 155416089455 else
  if aa=29 then 158080687247 else
  if aa=30 then 160693337085 else
  if aa=31 then 163257213047 else
  if aa=32 then 80869024796 else
  if aa=33 then 80770186893 else
  if aa=34 then 80462914289 else
  if aa=35 then 79980144608 else
  if aa=36 then 79436566577 else
  if aa=37 then 79058109160 else
  if aa=38 then 78738674444 else
  if aa=39 then 78431917668 else
  if aa=40 then 78130337677 else
  if aa=41 then 77719668986 else
  if aa=42 then 77167214549 else
  if aa=43 then 76430210559 else
  if aa=44 then 75466345343 else
  if aa=45 then 74234578777 else
  if aa=46 then 72697039484 else
  if aa=47 then 70821040780 else
  if aa=48 then 68594429101 else
  if aa=49 then 66220427851 else
  if aa=50 then 63437127860 else
  if aa=51 then 60195225643 else
  if aa=52 then 56431890295 else
  if aa=53 then 52071278020 else
  if aa=54 then 47090128485 else
  if aa=55 then 41486370294 else
  if aa=56 then 35304609853 else
  if aa=57 then 29334634109 else
  if aa=58 then 23691316902 else
  if aa=59 then 18331557851 else
  if aa=60 then 12192475849 else
  if aa=61 then 9519300241 else
  0

theorem raw_first_cost_upper_62 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 62 ≤ (5265662644913/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 61) :
      rawRow 62 aa ≤ rowGrid_62 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 61 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_62,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 62 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 61,rowGrid_62 aa/10000000000)+(0/10000000000 : ℝ)=(5265662644913/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_62]
  change (∑ aa ∈ Finset.Icc 2 61,rawRow 62 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 62 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_62 : c ≤ coefficient profile 62 := by
  have hf := raw_first_cost_upper_62
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 62-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 62-1-
      (K*C/young 62)*(62 : ℝ)^2-(5265662644913/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 62 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 62-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 62-1-
      ((K*C/young 62)*(62 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 62+
        t 3*tripleHarmonicNeighborCharge K young zeta 62)
  linarith only [hf,hn]

def rowGrid_63 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 119180782289 else
  if aa=19 then 123079253144 else
  if aa=20 then 126871731350 else
  if aa=21 then 130576191063 else
  if aa=22 then 134212052427 else
  if aa=23 then 137800183953 else
  if aa=24 then 141363056837 else
  if aa=25 then 144925035001 else
  if aa=26 then 148513114677 else
  if aa=27 then 152157597664 else
  if aa=28 then 155416089455 else
  if aa=29 then 158080687247 else
  if aa=30 then 160693337085 else
  if aa=31 then 163257213047 else
  if aa=32 then 172021090378 else
  if aa=33 then 80869024796 else
  if aa=34 then 80770186893 else
  if aa=35 then 80462914289 else
  if aa=36 then 79980144608 else
  if aa=37 then 79436566577 else
  if aa=38 then 79058109160 else
  if aa=39 then 78738674444 else
  if aa=40 then 78431917668 else
  if aa=41 then 78130337677 else
  if aa=42 then 77719668986 else
  if aa=43 then 77167214549 else
  if aa=44 then 76430210559 else
  if aa=45 then 75466345343 else
  if aa=46 then 74234578777 else
  if aa=47 then 72697039484 else
  if aa=48 then 70821040780 else
  if aa=49 then 68594429101 else
  if aa=50 then 66220427851 else
  if aa=51 then 63437127860 else
  if aa=52 then 60195225643 else
  if aa=53 then 56431890295 else
  if aa=54 then 52071278020 else
  if aa=55 then 47090128485 else
  if aa=56 then 41486370294 else
  if aa=57 then 35304609853 else
  if aa=58 then 29334634109 else
  if aa=59 then 23691316902 else
  if aa=60 then 18331557851 else
  if aa=61 then 12192475849 else
  if aa=62 then 9519300241 else
  0

theorem raw_first_cost_upper_63 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 63 ≤ (5437683735291/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 62) :
      rawRow 63 aa ≤ rowGrid_63 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 62 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_63,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 63 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 62,rowGrid_63 aa/10000000000)+(0/10000000000 : ℝ)=(5437683735291/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_63]
  change (∑ aa ∈ Finset.Icc 2 62,rawRow 63 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 63 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_63 : c ≤ coefficient profile 63 := by
  have hf := raw_first_cost_upper_63
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 63-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 63-1-
      (K*C/young 63)*(63 : ℝ)^2-(5437683735291/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 63 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 63-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 63-1-
      ((K*C/young 63)*(63 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 63+
        t 3*tripleHarmonicNeighborCharge K young zeta 63)
  linarith only [hf,hn]

def rowGrid_64 (aa : ℕ) : ℝ :=
  if aa=2 then 226894284609 else
  if aa=3 then 45830349811 else
  if aa=4 then 44233138718 else
  if aa=5 then 52588118136 else
  if aa=6 then 60371729562 else
  if aa=7 then 67726150817 else
  if aa=8 then 73023187989 else
  if aa=9 then 77979285443 else
  if aa=10 then 82996483135 else
  if aa=11 then 87979546196 else
  if aa=12 then 92868704979 else
  if aa=13 then 97628627565 else
  if aa=14 then 102240839292 else
  if aa=15 then 106698473637 else
  if aa=16 then 111002665622 else
  if aa=17 then 115159987219 else
  if aa=18 then 119180782289 else
  if aa=19 then 123079253144 else
  if aa=20 then 126871731350 else
  if aa=21 then 130576191063 else
  if aa=22 then 134212052427 else
  if aa=23 then 137800183953 else
  if aa=24 then 141363056837 else
  if aa=25 then 144925035001 else
  if aa=26 then 148513114677 else
  if aa=27 then 152157597664 else
  if aa=28 then 155416089455 else
  if aa=29 then 158080687247 else
  if aa=30 then 160693337085 else
  if aa=31 then 163257213047 else
  if aa=32 then 172021090378 else
  if aa=33 then 172021090378 else
  if aa=34 then 80869024796 else
  if aa=35 then 80770186893 else
  if aa=36 then 80462914289 else
  if aa=37 then 79980144608 else
  if aa=38 then 79436566577 else
  if aa=39 then 79058109160 else
  if aa=40 then 78738674444 else
  if aa=41 then 78431917668 else
  if aa=42 then 78130337677 else
  if aa=43 then 77719668986 else
  if aa=44 then 77167214549 else
  if aa=45 then 76430210559 else
  if aa=46 then 75466345343 else
  if aa=47 then 74234578777 else
  if aa=48 then 72697039484 else
  if aa=49 then 70821040780 else
  if aa=50 then 68594429101 else
  if aa=51 then 66220427851 else
  if aa=52 then 63437127860 else
  if aa=53 then 60195225643 else
  if aa=54 then 56431890295 else
  if aa=55 then 52071278020 else
  if aa=56 then 47090128485 else
  if aa=57 then 41486370294 else
  if aa=58 then 35304609853 else
  if aa=59 then 29334634109 else
  if aa=60 then 23691316902 else
  if aa=61 then 18331557851 else
  if aa=62 then 12192475849 else
  if aa=63 then 9519300241 else
  0

theorem raw_first_cost_upper_64 :
    TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 64 ≤ (5609704825669/10000000000 : ℝ) := by
  have hrow (aa : ℕ) (ha : aa ∈ Finset.Icc 2 63) :
      rawRow 64 aa ≤ rowGrid_64 aa/10000000000 := by
    have hlo : 2 ≤ aa := (Finset.mem_Icc.mp ha).1
    have hhi : aa ≤ 63 := (Finset.mem_Icc.mp ha).2
    interval_cases aa <;> norm_num [rowGrid_64,rawRow,twoRowsProfile,twoRowsLambda,tripleHarmonicThetaProfile,tripleHarmonicLambdaProfile,harmonicRatioTheta,harmonicRatioLambda,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicLambda,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hsum := Finset.sum_le_sum hrow
  have he : TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 64 ≤ (0/10000000000 : ℝ) := by
    norm_num [TriplePositiveEnergyWeightedBudgetDrift.extra,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,harmonicRatioTheta,harmonicRatioEta,harmonicRatioDenom,selectedHarmonicDenom,selectedHarmonicTheta,selectedHarmonicEta,tripleHarmonicRatio,TripleCreation.chargeRatio]
  have hg : (∑ aa ∈ Finset.Icc 2 63,rowGrid_64 aa/10000000000)+(0/10000000000 : ℝ)=(5609704825669/10000000000 : ℝ) := by
    norm_num [grid_sum_interval_two,Finset.sum_range_succ,rowGrid_64]
  change (∑ aa ∈ Finset.Icc 2 63,rawRow 64 aa)+
    TriplePositiveEnergyWeightedBudgetDrift.extra young t zeta 64 ≤ _
  linarith only [hsum,he,hg]

theorem coefficient_grid_64 : c ≤ coefficient profile 64 := by
  have hf := raw_first_cost_upper_64
  have hn : c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 64-
      PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 64-1-
      (K*C/young 64)*(64 : ℝ)^2-(5609704825669/10000000000 : ℝ)-
      t 3*tripleHarmonicNeighborCharge K young zeta 64 := by
    norm_num [K,C,c,PositiveEnergyWeightedGenerator.incoming,PositiveEnergyWeightedGenerator.generatorLoss,PositiveEnergyWeightedGenerator.degreeLoss,PositiveEnergyWeightedGenerator.gamma,PositiveEnergyWeightedDrift.kappa,SignedRowReservedNoise.reservedNoiseLoss,SignedRowReservedNoise.lowRefund,SignedRowNoiseHigh.highLeading,SignedRowNoiseHigh.highPositive,PairProjection.leadingNoiseCoefficient,PairProjection.positiveNoiseCoefficient,tripleHarmonicNeighborCharge,TripleCreation.affineRest,TripleCreation.forcing,TripleCreation.recurrenceMultiplier]
  change c ≤ PositiveEnergyWeightedGenerator.incoming K t alpha 64-
    PositiveEnergyWeightedGenerator.generatorLoss K young t alpha theta lambda 64-1-
      ((K*C/young 64)*(64 : ℝ)^2+
        TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost young t theta lambda zeta 64+
        t 3*tripleHarmonicNeighborCharge K young zeta 64)
  linarith only [hf,hn]

theorem coefficient_finite_grid (d : ℕ) (hd : 5 ≤ d) (hD : d<65) : c ≤ coefficient profile d := by
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

end KLSConstantImprovement.QuarticM32FiniteCostGrid20261020
#print axioms KLSConstantImprovement.QuarticM32FiniteCostGrid20261020.coefficient_finite_grid
