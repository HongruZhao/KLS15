import Mathlib

/-! Scalar moment-gap reductions with their analytic comparison inputs explicit.
No crossing/comparison theorem for a law is assumed proved by this algebra.
No rank-one sector is promoted to a bound for every tensor. -/
noncomputable section
namespace KLSConstantImprovement.ScalarCurvatureMomentGaps

def deficit (m4 : ℝ) : ℝ := 9-m4
def fourthGap (m3 m4 : ℝ) : ℝ := (4/3:ℝ)*(9-m4)-(4-m3^2)
def sixthGap (m4 m6 : ℝ) : ℝ := (265/9:ℝ)*m4-m6
def curvature (k m3 m4 m6 : ℝ) : ℝ :=
  27*m4+22*m3^2-m6-66+k*(9-m4)

theorem scalar_gap_identity (k m3 m4 m6 : ℝ) :
    curvature k m3 m4 m6=
      (k-(242/9:ℝ))*deficit m4+22*fourthGap m3 m4+sixthGap m4 m6 := by
  unfold curvature deficit fourthGap sixthGap
  ring

theorem curvature_at_242over9_nonnegative {m3 m4 m6 : ℝ}
    (hg4 : 0 ≤ fourthGap m3 m4) (hg6 : 0 ≤ sixthGap m4 m6) :
    0 ≤ curvature (242/9) m3 m4 m6 := by
  rw [scalar_gap_identity]
  nlinarith

theorem curvature_twenty_seven_pays_deficit {m3 m4 m6 : ℝ}
    (hg4 : 0 ≤ fourthGap m3 m4) (hg6 : 0 ≤ sixthGap m4 m6) :
    deficit m4/9 ≤ curvature 27 m3 m4 m6 := by
  rw [scalar_gap_identity]
  nlinarith

theorem curvature_above_242over9 {k m3 m4 m6 : ℝ}
    (hk : (242/9:ℝ) ≤ k) (hd : 0 ≤ deficit m4)
    (hg4 : 0 ≤ fourthGap m3 m4) (hg6 : 0 ≤ sixthGap m4 m6) :
    0 ≤ curvature k m3 m4 m6 := by
  rw [scalar_gap_identity]
  positivity

theorem canonical_cubic_variance_le_216 {m3 m4 m6 V : ℝ}
    (hV : V=m6-6*m4+9-m3^2)
    (h4 : m4 ≤ 6+(3/4:ℝ)*m3^2)
    (h3 : m3^2 ≤ 4) (h6 : m6 ≤ (265/9:ℝ)*m4) : V ≤ 216 := by
  have h : V ≤ (449/3:ℝ)+(199/12:ℝ)*m3^2 := by linarith
  linarith

theorem rank_one_cost_gives_336 {V M N : ℝ}
    (hV : V ≤ 216*M) (hcost : M ≤ (14/9:ℝ)*N) : V ≤ 336*N := by
  linarith

end KLSConstantImprovement.ScalarCurvatureMomentGaps
#print axioms KLSConstantImprovement.ScalarCurvatureMomentGaps.scalar_gap_identity
#print axioms KLSConstantImprovement.ScalarCurvatureMomentGaps.curvature_at_242over9_nonnegative
#print axioms KLSConstantImprovement.ScalarCurvatureMomentGaps.curvature_twenty_seven_pays_deficit
#print axioms KLSConstantImprovement.ScalarCurvatureMomentGaps.curvature_above_242over9
#print axioms KLSConstantImprovement.ScalarCurvatureMomentGaps.canonical_cubic_variance_le_216
#print axioms KLSConstantImprovement.ScalarCurvatureMomentGaps.rank_one_cost_gives_336
