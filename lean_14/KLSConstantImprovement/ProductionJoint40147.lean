import KLSConstantImprovement.ProductionYoung4047255

/-! Exact payoff from the coupled-center response estimate. This finite
module retains that estimate explicitly; original-law construction follows
only after its actual source binding is proved. -/
noncomputable section
namespace KLSConstantImprovement.ProductionJoint40147
open ProductionYoung4047255 SourceMatchedMeanResponseConditionalPayoff

def cap401 : ℝ := 40147/100
def mainA401 : ℝ := 240639642572139/1380060500000
def mainB401 : ℝ := 208153598072139/1380060500000
def mainQ401 : ℝ := 14571/1372
def mix401 : ℝ := 25399/100000
def mixedA401 : ℝ := 2598586564418515688751/15042659450000000000
def mixedB401 : ℝ := 2254972776992515688751/15042659450000000000
def affineCredit401 : ℝ := 473337/14954800000
def rowCredit401 : ℝ := 44971461/247600000
def targetCredit401 : ℝ := rowP*mix401
def extraCredit401 : ℝ := rowP*mix401+mainF*(1-mix401)

theorem main_branch_joint {V J MF W r t q L e : ℝ}
    (hVariance : V ≤ mainJ*J+mainF*MF)
    (hJ : J ≤ (414149/171500:ℝ)*W-(250/343:ℝ)*q)
    (hMF : MF ≤ (4/13:ℝ)*W+2*r+t-e+L/4)
    (hW : W ≤ 3*(r+t)) :
    V ≤ mainA401*r+mainB401*t-mainQ401*q-mainF*e+mainF*L/4 := by
  dsimp only [mainA401,mainB401,mainQ401,mainJ,mainF] at *
  linarith only [hVariance,hJ,hMF,hW]

theorem disk_certificate401 :
    0 ≤ cap401-mixedA401 ∧ mixedA401^2+mixedB401^2 ≤ (cap401-mixedA401)^2 := by
  norm_num [cap401,mixedA401,mixedB401]

theorem retained_joint_raw40147 {V N g r t q p L e : ℝ}
    (hg : 0 ≤ g) (hneff : 0 ≤ N-g/2)
    (hdisk : (r-(N-g/2))^2+t^2 ≤ (N-g/2)^2)
    (hq : 0 ≤ q) (hp : 0 ≤ p) (hL : 0 ≤ L) (he : 0 ≤ e)
    (hrow : V ≤ rowA*r+rowB*t+rowQ*q-rowP*p-18*L-rowP*e)
    (hmain : V ≤ mainA401*r+mainB401*t-mainQ401*q-mainF*e+mainF*L/4) :
    V ≤ cap401*N-(cap401/2)*g-affineCredit401*q-rowCredit401*L-
      targetCredit401*p-extraCredit401*e ∧ V ≤ cap401*N := by
  have hc := disk_certificate401
  have hsupport := disk_linear_support hneff hc.1 hc.2 hdisk
  have haverage : V ≤ mixedA401*r+mixedB401*t-affineCredit401*q-
      rowCredit401*L-targetCredit401*p-extraCredit401*e := by
    dsimp only [rowA,rowB,rowQ,rowP,mainA401,mainB401,mainQ401,mainF,mixedA401,mixedB401,
      affineCredit401,rowCredit401,targetCredit401,extraCredit401,mix401] at *
    linarith only [hrow,hmain]
  have hfirst : V ≤ cap401*N-(cap401/2)*g-affineCredit401*q-rowCredit401*L-
      targetCredit401*p-extraCredit401*e := by nlinarith only [hsupport,haverage]
  refine ⟨hfirst,?_⟩
  have ha : 0 ≤ affineCredit401*q := mul_nonneg (by norm_num [affineCredit401]) hq
  have hr : 0 ≤ rowCredit401*L := mul_nonneg (by norm_num [rowCredit401]) hL
  have ht : 0 ≤ targetCredit401*p := mul_nonneg (by norm_num [targetCredit401,rowP,mix401]) hp
  have hx : 0 ≤ extraCredit401*e := mul_nonneg (by norm_num [extraCredit401,rowP,mainF,mix401]) he
  have hg' : 0 ≤ (cap401/2)*g := mul_nonneg (by norm_num [cap401]) hg
  linarith only [hfirst,ha,hr,ht,hx,hg']

end KLSConstantImprovement.ProductionJoint40147
#print axioms KLSConstantImprovement.ProductionJoint40147.main_branch_joint
#print axioms KLSConstantImprovement.ProductionJoint40147.disk_certificate401
#print axioms KLSConstantImprovement.ProductionJoint40147.retained_joint_raw40147
