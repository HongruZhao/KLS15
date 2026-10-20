import Mathlib

/-! A lower witness for the accepted SCALAR production relaxation only.
This is not an admissible law and is not a lower bound for the universal cubic
constant. It proves that uniform scalar deductions using only the displayed
row/Cauchy, affine-square, parametric-production and Hilbert constraints cannot
improve below the exhibited value. All positive parameters are quantified. -/
noncomputable section
namespace KLSConstantImprovement.ProductionScalarFrontierLower
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

structure Point where
  V : ℝ
  r : ℝ
  t : ℝ
  W : ℝ
  q : ℝ
  L : ℝ
  theta : ℝ
  thetaZ : ℝ
  thetaU : ℝ
  ell : ℝ
  m : ℝ
  J : ℝ
  MF : ℝ
  deltaMF : ℝ
  cross : ℝ

structure Feasible (d : Point) : Prop where
  W_nonneg : 0 ≤ d.W
  q_nonneg : 0 ≤ d.q
  q_cap : d.q ≤ d.W
  L_nonneg : 0 ≤ d.L
  theta_nonneg : 0 ≤ d.theta
  thetaU_nonneg : 0 ≤ d.thetaU
  J_nonneg : 0 ≤ d.J
  MF_nonneg : 0 ≤ d.MF
  disk : (d.r-1)^2+d.t^2 ≤ 1
  W_payment : d.W ≤ 3*(d.r+d.t)
  theta_payment : d.theta ≤ 2*d.r+d.t
  affine_row : d.thetaZ=(d.W+3*d.q)/2
  split_row : 2*d.thetaU ≤ d.theta+d.thetaZ
  ell_Cauchy : d.ell^2 ≤ d.W*d.thetaU
  row_balance : 2*d.m=d.W+d.thetaU+2*d.ell-d.L
  row_variance : d.V ≤ 36*d.m
  affine_square : (d.J-d.W)^2 ≤ 2*d.W*(d.W-d.q)
  production_square : d.deltaMF^2 ≤ 4*d.W*d.L
  production_balance : d.MF=d.theta-3*d.L+d.deltaMF
  hilbert_square : d.cross^2 ≤ d.J*d.MF
  main_variance : d.V ≤ 9*(d.J+d.MF+2*d.cross)

theorem two_Cauchy_le_add {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : z^2 ≤ x*y) : 2*z ≤ x+y := by
  have hs := sq_nonneg (x-y)
  have hsq : (2*z)^2 ≤ (x+y)^2 := by nlinarith only [hz,hs]
  have hb : 0 ≤ x+y := add_nonneg hx hy
  have hh := le_of_sq_le_sq hsq hb
  linarith only [hh]

theorem weighted_Cauchy {x y z a : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : z^2 ≤ x*y) (ha : 0 < a) : 2*z ≤ a*x+y/a := by
  have he : (a*x)*(y/a)=x*y := by field_simp [ne_of_gt ha] <;> ring
  have hh : z^2 ≤ (a*x)*(y/a) := by rwa [he]
  exact two_Cauchy_le_add (mul_nonneg ha.le hx) (div_nonneg hy ha.le) hh

theorem row_all_parameters (d : Point) (h : Feasible d) {a : ℝ} (ha : 0<a) :
    0 ≤ a*d.W+d.thetaU/a-2*d.ell := by
  have hh := weighted_Cauchy h.W_nonneg h.thetaU_nonneg h.ell_Cauchy ha
  linarith only [hh]

theorem affine_all_parameters (d : Point) (h : Feasible d) {a : ℝ} (ha : 0<a) :
    d.J ≤ (1+a+1/(2*a))*d.W-d.q/(2*a) := by
  have hc : (d.J-d.W)^2 ≤ d.W*(2*(d.W-d.q)) := by
    nlinarith only [h.affine_square]
  have hh := weighted_Cauchy h.W_nonneg (by linarith only [h.q_cap] : 0≤2*(d.W-d.q))
    hc (by linarith only [ha] : 0<2*a)
  have he : (2*a)*d.W+(2*(d.W-d.q))/(2*a)=
      2*((1+a+1/(2*a))*d.W-d.q/(2*a)-d.W) := by
    field_simp [ne_of_gt ha] <;> ring
  rw [he] at hh
  linarith only [hh]

theorem production_all_parameters (d : Point) (h : Feasible d) {k : ℝ} (hk : 0≤k) :
    d.MF ≤ (2/(k+6))*d.W+d.theta+(k/2)*d.L := by
  have hu : 0<k+6 := by linarith only [hk]
  have hc : d.deltaMF^2 ≤ (2*d.W)*(2*d.L) := by
    nlinarith only [h.production_square]
  have hh := weighted_Cauchy (by linarith only [h.W_nonneg] : 0≤2*d.W)
    (by linarith only [h.L_nonneg] : 0≤2*d.L) hc
    (div_pos (by norm_num : (0:ℝ)<2) hu)
  have he : (2/(k+6))*(2*d.W)+(2*d.L)/(2/(k+6))=
      2*((2/(k+6))*d.W+(k/2)*d.L+3*d.L) := by
    field_simp [ne_of_gt hu] <;> ring
  rw [he] at hh
  linarith only [hh,h.production_balance]

theorem main_all_parameters (d : Point) (h : Feasible d) {a : ℝ} (ha : 0<a) :
    d.V ≤ 9*(1+a)*d.J+9*(1+1/a)*d.MF := by
  have hh := weighted_Cauchy h.J_nonneg h.MF_nonneg h.hilbert_square ha
  have he : 9*(1+a)*d.J+9*(1+1/a)*d.MF=
      9*(d.J+d.MF+a*d.J+d.MF/a) := by
    field_simp [ne_of_gt ha] <;> ring
  rw [he]
  linarith only [hh,h.main_variance]

def witness : Point where
  V := 2006511732043/5000000000
  r := 17549820379494961638012083309507962050503836198791593551/10000000000000000000000000000000000000000000000000000000
  t := 6557454707229212226469501064544529277078777353049827971/10000000000000000000000000000000000000000000000000000000
  W := 36160912630086260796722376561078736991373920327762132283/5000000000000000000000000000000000000000000000000000000
  q := 711627124169221934342262945161/1000000000000000000000000000000
  L := 675877726926177342369773985881/1000000000000000000000000000000
  theta := 41657095466219135502493667683560453378086449750633015073/10000000000000000000000000000000000000000000000000000000
  thetaZ := 46835319492624589811856320738493736991373920327762132283/10000000000000000000000000000000000000000000000000000000
  thetaU := 22123103739710931328587497105513547592365092519598786839/5000000000000000000000000000000000000000000000000000000
  ell := 5656824626724861109987700604277/1000000000000000000000000000000
  m := 55736437001207458256669004889978642291869506423680459561/5000000000000000000000000000000000000000000000000000000
  J := 84719046262451460033209241672563736991373920327762132283/5000000000000000000000000000000000000000000000000000000
  MF := 65598728724229232577646566288350453378086449750633015073/10000000000000000000000000000000000000000000000000000000
  deltaMF := 2210898253289770867312305909061/500000000000000000000000000000
  cross := 10542733738026375670464349478787/1000000000000000000000000000000

theorem witness_feasible : Feasible witness := by
  constructor <;> norm_num [witness]

theorem scalar_family_lower_bound {C : ℝ}
    (hC : ∀ d : Point, Feasible d → d.V ≤ C) :
    (2006511732043/5000000000 : ℝ) ≤ C := by
  have hh := hC witness witness_feasible
  simpa only [witness] using hh

theorem scalar_family_excludes_smaller {C : ℝ}
    (hC : C < (2006511732043/5000000000 : ℝ)) :
    ¬ (∀ d : Point, Feasible d → d.V ≤ C) := by
  intro hh
  exact (not_le_of_gt hC) (scalar_family_lower_bound hh)

end KLSConstantImprovement.ProductionScalarFrontierLower
#print axioms KLSConstantImprovement.ProductionScalarFrontierLower.row_all_parameters
#print axioms KLSConstantImprovement.ProductionScalarFrontierLower.affine_all_parameters
#print axioms KLSConstantImprovement.ProductionScalarFrontierLower.production_all_parameters
#print axioms KLSConstantImprovement.ProductionScalarFrontierLower.main_all_parameters
#print axioms KLSConstantImprovement.ProductionScalarFrontierLower.witness_feasible
#print axioms KLSConstantImprovement.ProductionScalarFrontierLower.scalar_family_lower_bound
#print axioms KLSConstantImprovement.ProductionScalarFrontierLower.scalar_family_excludes_smaller
