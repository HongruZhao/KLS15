import KLSConstantImprovement.ProductionYoung4047255

/-! Exact payoff from the coupled-center response estimate. This finite
module retains that estimate explicitly; original-law construction follows
only after its actual source binding is proved. -/
noncomputable section
namespace KLSConstantImprovement.ProductionCoupled403145
open ProductionYoung4047255 SourceMatchedMeanResponseConditionalPayoff

def cap403 : ℝ := 403145/1000
def mainA403 : ℝ := 37229551141281/212317000000
def mainB403 : ℝ := 32231698141281/212317000000
def mainQ403 : ℝ := 3712734513/339707200
def mix403 : ℝ := 129731/500000
def mixedA403 : ℝ := 2006906084110350816201/11571276500000000000
def mixedB403 : ℝ := 1742761533034350816201/11571276500000000000
def affineCredit403 : ℝ := 409906296873/18514042400000000
def rowCredit403 : ℝ := 386661609/1238000000
def targetCredit403 : ℝ := rowP*mix403
def extraCredit403 : ℝ := rowP*mix403+mainF*(1-mix403)

theorem main_branch_coupled {V J MF W r t q L e : ℝ}
    (hVariance : V ≤ mainJ*J+mainF*MF)
    (hJ : J ≤ (414149/171500:ℝ)*W-(250/343:ℝ)*q)
    (hMF : MF ≤ (1/3-847/72000:ℝ)*W+2*r+t-e+L/4-(21/1600:ℝ)*q)
    (hW : W ≤ 3*(r+t)) :
    V ≤ mainA403*r+mainB403*t-mainQ403*q-mainF*e+mainF*L/4 := by
  dsimp only [mainA403,mainB403,mainQ403,mainJ,mainF] at *
  linarith only [hVariance,hJ,hMF,hW]

theorem disk_certificate403 :
    0 ≤ cap403-mixedA403 ∧ mixedA403^2+mixedB403^2 ≤ (cap403-mixedA403)^2 := by
  norm_num [cap403,mixedA403,mixedB403]

theorem retained_joint_raw403145 {V N g r t q p L e : ℝ}
    (hg : 0 ≤ g) (hneff : 0 ≤ N-g/2)
    (hdisk : (r-(N-g/2))^2+t^2 ≤ (N-g/2)^2)
    (hq : 0 ≤ q) (hp : 0 ≤ p) (hL : 0 ≤ L) (he : 0 ≤ e)
    (hrow : V ≤ rowA*r+rowB*t+rowQ*q-rowP*p-18*L-rowP*e)
    (hmain : V ≤ mainA403*r+mainB403*t-mainQ403*q-mainF*e+mainF*L/4) :
    V ≤ cap403*N-(cap403/2)*g-affineCredit403*q-rowCredit403*L-
      targetCredit403*p-extraCredit403*e ∧ V ≤ cap403*N := by
  have hc := disk_certificate403
  have hsupport := disk_linear_support hneff hc.1 hc.2 hdisk
  have haverage : V ≤ mixedA403*r+mixedB403*t-affineCredit403*q-
      rowCredit403*L-targetCredit403*p-extraCredit403*e := by
    dsimp only [rowA,rowB,rowQ,rowP,mainA403,mainB403,mainQ403,mainF,mixedA403,mixedB403,
      affineCredit403,rowCredit403,targetCredit403,extraCredit403,mix403] at *
    linarith only [hrow,hmain]
  have hfirst : V ≤ cap403*N-(cap403/2)*g-affineCredit403*q-rowCredit403*L-
      targetCredit403*p-extraCredit403*e := by nlinarith only [hsupport,haverage]
  refine ⟨hfirst,?_⟩
  have ha : 0 ≤ affineCredit403*q := mul_nonneg (by norm_num [affineCredit403]) hq
  have hr : 0 ≤ rowCredit403*L := mul_nonneg (by norm_num [rowCredit403]) hL
  have ht : 0 ≤ targetCredit403*p := mul_nonneg (by norm_num [targetCredit403,rowP,mix403]) hp
  have hx : 0 ≤ extraCredit403*e := mul_nonneg (by norm_num [extraCredit403,rowP,mainF,mix403]) he
  have hg' : 0 ≤ (cap403/2)*g := mul_nonneg (by norm_num [cap403]) hg
  linarith only [hfirst,ha,hr,ht,hx,hg']

end KLSConstantImprovement.ProductionCoupled403145
#print axioms KLSConstantImprovement.ProductionCoupled403145.main_branch_coupled
#print axioms KLSConstantImprovement.ProductionCoupled403145.disk_certificate403
#print axioms KLSConstantImprovement.ProductionCoupled403145.retained_joint_raw403145
