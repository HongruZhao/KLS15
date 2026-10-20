import KLSConstantImprovement.ActualCubicHilbertUpper405
import KLSConstantImprovement.SourceProductionJointRaw405Payoff

/-! Exact scalar reoptimization of established, same-field405 production inputs.
The three Young parameters are row763/1000, main619/1000, affine343/500.
The mixing weight25399/100000 is below the affine-cancellation value, retaining
all five original nonnegative loss quantities with strictly positive weights. -/
noncomputable section
namespace KLSConstantImprovement.ProductionYoung4047255
open SourceMatchedMeanResponseConditionalPayoff ActualCubicHilbertUpper405

def cap : ℝ := 4047255/10000
def rowA : ℝ := 9155259/54500
def rowB : ℝ := 56153313/381500
def rowQ : ℝ := 47601/1526
def rowP : ℝ := 15867/763
def mainJ : ℝ := 14571/1000
def mainF : ℝ := 14571/619
def mainA : ℝ := 18702966851703/106158500000
def mainB : ℝ := 16204040351703/106158500000
def mainQ : ℝ := 14571/1372
def mix : ℝ := 25399/100000
def mixedA : ℝ := 201454354441815706827/1157127650000000000
def mixedB : ℝ := 175022524639815706827/1157127650000000000
def affineCredit : ℝ := 473337/14954800000
def rowCredit : ℝ := 18*mix
def targetCredit : ℝ := rowP*mix
def extraCredit : ℝ := rowP*mix+mainF*(1-mix)

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem split_619_young (a f : E) :
    9*‖a+f‖^2 ≤ mainJ*‖a‖^2+mainF*‖f‖^2 := by
  have hc := real_inner_le_norm a f
  have hy := sq_nonneg (619*‖a‖-1000*‖f‖)
  rw [norm_add_sq_real]
  dsimp only [mainJ,mainF]
  nlinarith only [hc,hy]

theorem six_pairing_split_upper_619 (u a f w : E) {v : ℝ}
    (hw : ‖w‖^2 ≤ v) (hv : v=6*inner ℝ u w)
    (hf : a+f=(2:ℝ) • u) :
    v ≤ mainJ*‖a‖^2+mainF*‖f‖^2 := by
  have hwhole := six_pairing_upper u w hw hv
  have hy := split_619_young a f
  rw [hf,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hy
  nlinarith only [hwhole,hy]
end Hilbert

theorem row_ell_763 {ell W theta : ℝ} (hW : 0 ≤ W) (ht : 0 ≤ theta)
    (hCauchy : ell^2 ≤ W*theta) :
    0 ≤ (763/1000:ℝ)*W+(1000/763:ℝ)*theta-2*ell := by
  have hs := sq_nonneg ((763/1000:ℝ)*W-(1000/763:ℝ)*theta)
  have hsq : (2*ell)^2 ≤ ((763/1000:ℝ)*W+(1000/763:ℝ)*theta)^2 := by nlinarith only [hCauchy,hs]
  have hb : 0 ≤ (763/1000:ℝ)*W+(1000/763:ℝ)*theta := by positivity
  have h := le_of_sq_le_sq hsq hb
  linarith only [h]

theorem row_branch {V m W theta thetaF thetaZ ell r t q p e L : ℝ}
    (hVariance : V ≤ 36*m) (hRow : 2*m=W+theta+2*ell-L)
    (hEll : 0 ≤ (763/1000:ℝ)*W+(1000/763:ℝ)*theta-2*ell)
    (hSplit : 2*theta ≤ thetaF+thetaZ)
    (hAffine : thetaZ=(W+3*q-2*p)/2)
    (hTheta : thetaF ≤ 2*r+t-e) (hW : W ≤ 3*(r+t)) :
    V ≤ rowA*r+rowB*t+rowQ*q-rowP*p-18*L-rowP*e := by
  dsimp only [rowA,rowB,rowQ,rowP]
  linarith only [hVariance,hRow,hEll,hSplit,hAffine,hTheta,hW]

theorem main_branch {V J MF W r t q e : ℝ}
    (hVariance : V ≤ mainJ*J+mainF*MF)
    (hJ : J ≤ (414149/171500:ℝ)*W-(250/343:ℝ)*q)
    (hMF : MF ≤ W/3+2*r+t-e) (hW : W ≤ 3*(r+t)) :
    V ≤ mainA*r+mainB*t-mainQ*q-mainF*e := by
  dsimp only [mainA,mainB,mainQ,mainJ,mainF] at *
  linarith only [hVariance,hJ,hMF,hW]

theorem disk_certificate :
    0 ≤ cap-mixedA ∧ mixedA^2+mixedB^2 ≤ (cap-mixedA)^2 := by
  norm_num [cap,mixedA,mixedB]

theorem retained_joint_raw4047255 {V N g r t q p L e : ℝ}
    (hg : 0 ≤ g) (hneff : 0 ≤ N-g/2)
    (hdisk : (r-(N-g/2))^2+t^2 ≤ (N-g/2)^2)
    (hq : 0 ≤ q) (hp : 0 ≤ p) (hL : 0 ≤ L) (he : 0 ≤ e)
    (hrow : V ≤ rowA*r+rowB*t+rowQ*q-rowP*p-18*L-rowP*e)
    (hmain : V ≤ mainA*r+mainB*t-mainQ*q-mainF*e) :
    V ≤ cap*N-(cap/2)*g-affineCredit*q-rowCredit*L-targetCredit*p-extraCredit*e ∧
      V ≤ cap*N := by
  have hc := disk_certificate
  have hsupport := disk_linear_support hneff hc.1 hc.2 hdisk
  have haverage : V ≤ mixedA*r+mixedB*t-affineCredit*q-
      rowCredit*L-targetCredit*p-extraCredit*e := by
    dsimp only [rowA,rowB,rowQ,rowP,mainA,mainB,mainQ,mainF,mixedA,mixedB,
      affineCredit,rowCredit,targetCredit,extraCredit,mix] at *
    linarith only [hrow,hmain]
  have hfirst : V ≤ cap*N-(cap/2)*g-affineCredit*q-rowCredit*L-targetCredit*p-extraCredit*e := by
    nlinarith only [hsupport,haverage]
  refine ⟨hfirst,?_⟩
  have ha : 0 ≤ affineCredit*q := mul_nonneg (by norm_num [affineCredit]) hq
  have hr : 0 ≤ rowCredit*L := mul_nonneg (by norm_num [rowCredit,mix]) hL
  have ht : 0 ≤ targetCredit*p := mul_nonneg (by norm_num [targetCredit,rowP,mix]) hp
  have hx : 0 ≤ extraCredit*e := mul_nonneg (by norm_num [extraCredit,rowP,mainF,mix]) he
  have hg' : 0 ≤ (cap/2)*g := mul_nonneg (by norm_num [cap]) hg
  linarith only [hfirst,ha,hr,ht,hx,hg']

end KLSConstantImprovement.ProductionYoung4047255
#print axioms KLSConstantImprovement.ProductionYoung4047255.split_619_young
#print axioms KLSConstantImprovement.ProductionYoung4047255.six_pairing_split_upper_619
#print axioms KLSConstantImprovement.ProductionYoung4047255.row_ell_763
#print axioms KLSConstantImprovement.ProductionYoung4047255.row_branch
#print axioms KLSConstantImprovement.ProductionYoung4047255.main_branch
#print axioms KLSConstantImprovement.ProductionYoung4047255.disk_certificate
#print axioms KLSConstantImprovement.ProductionYoung4047255.retained_joint_raw4047255
