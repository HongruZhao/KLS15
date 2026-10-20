import Mathlib

/-! Exact scalar covariance normalization and the positive polynomial
certificate in the convex-tilt route audit. Actual laws are connected in
ConvexTiltCubicCounterexample. -/
noncomputable section
namespace KLSImprovement.ConvexTiltAlgebra
set_option maxHeartbeats 10000000

def variance (r : ℕ → ℝ) : ℝ := r 2-(r 1)^2
def centralThree (r : ℕ → ℝ) : ℝ := r 3-3*r 1*r 2+2*(r 1)^3
def centralFour (r : ℕ → ℝ) : ℝ :=
  r 4-4*r 1*r 3+6*(r 1)^2*r 2-3*(r 1)^4
def centralSix (r : ℕ → ℝ) : ℝ :=
  r 6-6*r 1*r 5+15*(r 1)^2*r 4-20*(r 1)^3*r 3+
    15*(r 1)^4*r 2-5*(r 1)^6
def cap (r : ℕ → ℝ) : ℝ :=
  (centralSix r-6*variance r*centralFour r+9*(variance r)^3-(centralThree r)^2)/
    (36*(variance r)^3)

def rawZero (k : ℕ) : ℝ := ((k.factorial:ℝ)+(-1:ℝ)^k/(k+1:ℕ))/2
def rawNine (w : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => -10*(w+8)/(9*(w-10))
  | 2 => (101*w-1460)/(81*(w-10))
  | 3 => -8*(43*w+1640)/(243*(w-10))
  | 4 => (3563*w-472400)/(2187*(w-10))
  | 5 => -2*(18749*w+10628800)/(19683*(w-10))
  | 6 => 5*(26809*w-76527520)/(59049*(w-10))
  | _ => 0

def denominator (w : ℝ) : ℝ := w^2-4070*w+8200
def numerator (w : ℝ) : ℝ :=
  w^6-289794165*w^5+5189637075*w^4+242103694750*w^3-
    1494007387500*w^2+1998534675000*w+443638000000
def bernstein (w : ℝ) : ℝ :=
  443638000000*(1-w)^6+6*776727112500*w*(1-w)^5+
  15*1010215732500*w^2*(1-w)^4+20*(2312418089475/2)*w^3*(1-w)^3+
  15*1227158209755*w^4*(1-w)^2+6*(2471624129745/2)*w^5*(1-w)+
  1195168825161*w^6

theorem cap_zero_exact : cap rawZero=24166423/5210695 := by
  norm_num [cap,variance,centralThree,centralFour,centralSix,rawZero]

theorem cap_zero_lt_five : cap rawZero<5 := by rw [cap_zero_exact]; norm_num

theorem denominator_positive {w : ℝ} (hw : w<1) : 0<denominator w := by
  unfold denominator
  nlinarith [sq_nonneg w]

theorem variance_nine {w : ℝ} (hw : w<1) :
    variance (rawNine w)=denominator w/(81*(w-10)^2) := by
  have hn : w-10≠0 := by linarith
  norm_num only [variance,rawNine,denominator]
  field_simp [hn]
  <;> ring

theorem variance_nine_positive {w : ℝ} (hw : w<1) : 0<variance (rawNine w) := by
  rw [variance_nine hw]
  have hd := denominator_positive hw
  have hn : w-10≠0 := by linarith
  exact div_pos hd (mul_pos (by norm_num) (sq_pos_of_ne_zero hn))

theorem numerator_eq_bernstein (w : ℝ) : numerator w=bernstein w := by
  unfold numerator bernstein
  ring

theorem numerator_positive {w : ℝ} (hw0 : 0≤w) (hw1 : w<1) : 0<numerator w := by
  rw [numerator_eq_bernstein]
  have hp : 0<1-w := by linarith
  unfold bernstein
  positivity

theorem cap_nine_minus_five {w : ℝ} (hw : w<1) :
    cap (rawNine w)-5=numerator w/(denominator w)^3 := by
  have hn : w-10≠0 := by linarith
  have hd : denominator w≠0 := (denominator_positive hw).ne'
  unfold cap
  rw [variance_nine hw]
  norm_num only [centralThree,centralFour,centralSix,rawNine,numerator]
  field_simp [hn,hd]
  unfold denominator
  ring

theorem cap_nine_gt_five {w : ℝ} (hw0 : 0≤w) (hw1 : w<1) : 5<cap (rawNine w) := by
  have h := div_pos (numerator_positive hw0 hw1) (pow_pos (denominator_positive hw1) 3)
  rw [←cap_nine_minus_five hw1] at h
  linarith

theorem strict_cap_increase {w : ℝ} (hw0 : 0≤w) (hw1 : w<1) :
    cap rawZero<cap (rawNine w) :=
  lt_trans cap_zero_lt_five (cap_nine_gt_five hw0 hw1)

end KLSImprovement.ConvexTiltAlgebra
#print axioms KLSImprovement.ConvexTiltAlgebra.cap_zero_exact
#print axioms KLSImprovement.ConvexTiltAlgebra.variance_nine_positive
#print axioms KLSImprovement.ConvexTiltAlgebra.numerator_eq_bernstein
#print axioms KLSImprovement.ConvexTiltAlgebra.cap_nine_minus_five
#print axioms KLSImprovement.ConvexTiltAlgebra.strict_cap_increase
