import KLSConstantImprovement.ActualCubicHilbertUpper405
import KLSConstantImprovement.SourceProductionJointRaw405Payoff

/-! Exact rational refinement of the accepted same-source joint-production family.
All orientation, affine, row, target and response-extra loss credits remain nonnegative;
the affine and row credits are strictly positive. -/
noncomputable section
namespace KLSConstantImprovement.ProductionParameter4013023465
open SourceMatchedMeanResponseConditionalPayoff ActualCubicHilbertUpper405

def cap : ℝ := 802604693/2000000
def rowA : ℝ := 6570642649071267/39108695000000
def rowB : ℝ := 5768664394071267/39108695000000
def rowQ : ℝ := 481186953/15643478
def rowP : ℝ := 160395651/7821739
def mainJ : ℝ := 72999783/5000000
def mainF : ℝ := 24333261/1037029
def mainA : ℝ := 120389129099454798259258348499309243815796153597682035416848403688547/690805625130481702847272538133320662998073031516164225000000000000
def mainB : ℝ := 104179791099680278616020670663365847353956461966161557391848403688547/690805625130481702847272538133320662998073031516164225000000000000
def mainQ : ℝ := 24333261/2238058
def mix : ℝ := 158607013739999952384207/607325476157930000000000
def mixedA : ℝ := 566521410621593082892695885674237374138484193321289546293470286878090720071588285960443482419418769/3281562534545098815909149901637897446141019714507657841459808694314253340750000000000000000000000
def mixedB : ℝ := 28944502158233175866337985335134052115551333887724853649844009249288888782966700644731969554083457/193033090267358753877008817743405732125942336147509284791753452606720784750000000000000000000000
def affineCredit : ℝ := 182197642847379/43763763857155000000000
def rowCredit : ℝ := 10918783461534182928377518790973/1259628262429163979940000000000000000000
def targetCredit : ℝ := 25439875221993237102633883883757/4750341362558051240270000000000
def extraCredit : ℝ := 4471430511809013724933278376827/197049670114888532785838313200

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem split_parameter_young (a f : E) :
    9*‖a+f‖^2 ≤ mainJ*‖a‖^2+mainF*‖f‖^2 := by
  have hc := real_inner_le_norm a f
  have hy := sq_nonneg (3111087*‖a‖-5000000*‖f‖)
  rw [norm_add_sq_real]
  dsimp only [mainJ,mainF]
  nlinarith only [hc,hy]

theorem six_pairing_split_upper_parameter (u a f w : E) {v : ℝ}
    (hw : ‖w‖^2 ≤ v) (hv : v=6*inner ℝ u w)
    (hf : a+f=(2:ℝ) • u) :
    v ≤ mainJ*‖a‖^2+mainF*‖f‖^2 := by
  have hwhole := six_pairing_upper u w hw hv
  have hy := split_parameter_young a f
  rw [hf,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hy
  nlinarith only [hwhole,hy]
end Hilbert

theorem row_ell_parameter {ell W theta : ℝ} (hW : 0 ≤ W) (ht : 0 ≤ theta)
    (hCauchy : ell^2 ≤ W*theta) :
    0 ≤ (7821739/10000000:ℝ)*W+(10000000/7821739:ℝ)*theta-2*ell := by
  have hs := sq_nonneg ((7821739/10000000:ℝ)*W-(10000000/7821739:ℝ)*theta)
  have hsq : (2*ell)^2 ≤ ((7821739/10000000:ℝ)*W+(10000000/7821739:ℝ)*theta)^2 := by nlinarith only [hCauchy,hs]
  have hb : 0 ≤ (7821739/10000000:ℝ)*W+(10000000/7821739:ℝ)*theta := by positivity
  have h := le_of_sq_le_sq hsq hb
  linarith only [h]

theorem row_branch {V m W theta thetaF thetaZ ell r t q p e L : ℝ}
    (hVariance : V ≤ 36*m) (hRow : 2*m=W+theta+2*ell-L)
    (hEll : 0 ≤ (7821739/10000000:ℝ)*W+(10000000/7821739:ℝ)*theta-2*ell)
    (hSplit : 2*theta ≤ thetaF+thetaZ)
    (hAffine : thetaZ=(W+3*q-2*p)/2)
    (hTheta : thetaF ≤ 2*r+t-e) (hW : W ≤ 3*(r+t)) :
    V ≤ rowA*r+rowB*t+rowQ*q-rowP*p-18*L-rowP*e := by
  dsimp only [rowA,rowB,rowQ,rowP]
  linarith only [hVariance,hRow,hEll,hSplit,hAffine,hTheta,hW]

theorem main_branch_parameter {V J MF W r t q L e : ℝ}
    (hVariance : V ≤ mainJ*J+mainF*MF)
    (hJ : J ≤ (40555468125569/16785435000000:ℝ)*W-(2500000/3357087:ℝ)*q)
    (hMF : MF ≤ (7279188974356121952251679193982000000000/23811327793650112297029478217856160403009:ℝ)*W+2*r+t-e+(1973760870581746440274440635910160403009/7279188974356121952251679193982000000000:ℝ)*L) (hW : W ≤ 3*(r+t)) :
    V ≤ mainA*r+mainB*t-mainQ*q-mainF*e+(1973760870581746440274440635910160403009/7279188974356121952251679193982000000000:ℝ)*mainF*L := by
  dsimp only [mainA,mainB,mainQ,mainJ,mainF] at *
  linarith only [hVariance,hJ,hMF,hW]

theorem disk_certificate :
    0 ≤ cap-mixedA ∧ mixedA^2+mixedB^2 ≤ (cap-mixedA)^2 := by
  norm_num [cap,mixedA,mixedB]

theorem retained_joint_raw4013023465 {V N g r t q p L e : ℝ}
    (hg : 0 ≤ g) (hneff : 0 ≤ N-g/2)
    (hdisk : (r-(N-g/2))^2+t^2 ≤ (N-g/2)^2)
    (hq : 0 ≤ q) (hp : 0 ≤ p) (hL : 0 ≤ L) (he : 0 ≤ e)
    (hrow : V ≤ rowA*r+rowB*t+rowQ*q-rowP*p-18*L-rowP*e)
    (hmain : V ≤ mainA*r+mainB*t-mainQ*q-mainF*e+(1973760870581746440274440635910160403009/7279188974356121952251679193982000000000:ℝ)*mainF*L) :
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

end KLSConstantImprovement.ProductionParameter4013023465
#print axioms KLSConstantImprovement.ProductionParameter4013023465.split_parameter_young
#print axioms KLSConstantImprovement.ProductionParameter4013023465.six_pairing_split_upper_parameter
#print axioms KLSConstantImprovement.ProductionParameter4013023465.row_ell_parameter
#print axioms KLSConstantImprovement.ProductionParameter4013023465.row_branch
#print axioms KLSConstantImprovement.ProductionParameter4013023465.main_branch_parameter
#print axioms KLSConstantImprovement.ProductionParameter4013023465.disk_certificate
#print axioms KLSConstantImprovement.ProductionParameter4013023465.retained_joint_raw4013023465
