import KLSConstantImprovement.ActualCubicHilbertUpper405
import KLSConstantImprovement.SourceProductionJointRaw405Payoff

/-! Exact reoptimization of the proved same-source joint-production family.
The Young parameters are row391/500, main311/500, affine671/1000;
production k=27/50. Mixing130613/500000 retains strictly positive
orientation, affine, row, affine-target and response-extra loss weights. -/
noncomputable section
namespace KLSConstantImprovement.ProductionParameter401317
open SourceMatchedMeanResponseConditionalPayoff ActualCubicHilbertUpper405

def cap : ℝ := 401317/1000
def rowA : ℝ := 8211456/48875
def rowB : ℝ := 7209081/48875
def rowQ : ℝ := 24057/782
def rowP : ℝ := 8019/391
def mainJ : ℝ := 7299/500
def mainF : ℝ := 7299/311
def mainA : ℝ := 1982148161286123/11373114500000
def mainB : ℝ := 1715227380786123/11373114500000
def mainQ : ℝ := 7299/671
def mix : ℝ := 130613/500000
def mixedA : ℝ := 383865693470108140238991/2223443884750000000000
def mixedB : ℝ := 333402203639618140238991/2223443884750000000000
def affineCredit : ℝ := 1292031/52472200000
def rowCredit : ℝ := 320953149/15550000000
def targetCredit : ℝ := 1047385647/195500000
def extraCredit : ℝ := 68996691/3040025

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem split_622_young (a f : E) :
    9*‖a+f‖^2 ≤ mainJ*‖a‖^2+mainF*‖f‖^2 := by
  have hc := real_inner_le_norm a f
  have hy := sq_nonneg (311*‖a‖-500*‖f‖)
  rw [norm_add_sq_real]
  dsimp only [mainJ,mainF]
  nlinarith only [hc,hy]

theorem six_pairing_split_upper_622 (u a f w : E) {v : ℝ}
    (hw : ‖w‖^2 ≤ v) (hv : v=6*inner ℝ u w)
    (hf : a+f=(2:ℝ) • u) :
    v ≤ mainJ*‖a‖^2+mainF*‖f‖^2 := by
  have hwhole := six_pairing_upper u w hw hv
  have hy := split_622_young a f
  rw [hf,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hy
  nlinarith only [hwhole,hy]
end Hilbert

theorem row_ell_782 {ell W theta : ℝ} (hW : 0 ≤ W) (ht : 0 ≤ theta)
    (hCauchy : ell^2 ≤ W*theta) :
    0 ≤ (391/500:ℝ)*W+(500/391:ℝ)*theta-2*ell := by
  have hs := sq_nonneg ((391/500:ℝ)*W-(500/391:ℝ)*theta)
  have hsq : (2*ell)^2 ≤ ((391/500:ℝ)*W+(500/391:ℝ)*theta)^2 := by nlinarith only [hCauchy,hs]
  have hb : 0 ≤ (391/500:ℝ)*W+(500/391:ℝ)*theta := by positivity
  have h := le_of_sq_le_sq hsq hb
  linarith only [h]

theorem row_branch {V m W theta thetaF thetaZ ell r t q p e L : ℝ}
    (hVariance : V ≤ 36*m) (hRow : 2*m=W+theta+2*ell-L)
    (hEll : 0 ≤ (391/500:ℝ)*W+(500/391:ℝ)*theta-2*ell)
    (hSplit : 2*theta ≤ thetaF+thetaZ)
    (hAffine : thetaZ=(W+3*q-2*p)/2)
    (hTheta : thetaF ≤ 2*r+t-e) (hW : W ≤ 3*(r+t)) :
    V ≤ rowA*r+rowB*t+rowQ*q-rowP*p-18*L-rowP*e := by
  dsimp only [rowA,rowB,rowQ,rowP]
  linarith only [hVariance,hRow,hEll,hSplit,hAffine,hTheta,hW]

theorem main_branch_parameter {V J MF W r t q L e : ℝ}
    (hVariance : V ≤ mainJ*J+mainF*MF)
    (hJ : J ≤ (1621241/671000:ℝ)*W-(500/671:ℝ)*q)
    (hMF : MF ≤ (100/327:ℝ)*W+2*r+t-e+(27/100:ℝ)*L) (hW : W ≤ 3*(r+t)) :
    V ≤ mainA*r+mainB*t-mainQ*q-mainF*e+(27/100:ℝ)*mainF*L := by
  dsimp only [mainA,mainB,mainQ,mainJ,mainF] at *
  linarith only [hVariance,hJ,hMF,hW]

theorem disk_certificate :
    0 ≤ cap-mixedA ∧ mixedA^2+mixedB^2 ≤ (cap-mixedA)^2 := by
  norm_num [cap,mixedA,mixedB]

theorem retained_joint_raw401317 {V N g r t q p L e : ℝ}
    (hg : 0 ≤ g) (hneff : 0 ≤ N-g/2)
    (hdisk : (r-(N-g/2))^2+t^2 ≤ (N-g/2)^2)
    (hq : 0 ≤ q) (hp : 0 ≤ p) (hL : 0 ≤ L) (he : 0 ≤ e)
    (hrow : V ≤ rowA*r+rowB*t+rowQ*q-rowP*p-18*L-rowP*e)
    (hmain : V ≤ mainA*r+mainB*t-mainQ*q-mainF*e+(27/100:ℝ)*mainF*L) :
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

end KLSConstantImprovement.ProductionParameter401317
#print axioms KLSConstantImprovement.ProductionParameter401317.split_622_young
#print axioms KLSConstantImprovement.ProductionParameter401317.six_pairing_split_upper_622
#print axioms KLSConstantImprovement.ProductionParameter401317.row_ell_782
#print axioms KLSConstantImprovement.ProductionParameter401317.row_branch
#print axioms KLSConstantImprovement.ProductionParameter401317.main_branch_parameter
#print axioms KLSConstantImprovement.ProductionParameter401317.disk_certificate
#print axioms KLSConstantImprovement.ProductionParameter401317.retained_joint_raw401317
