import SingleSlotCounterexampleDensity

/-! Log-concavity of the actual two-cone probability measure. The proof uses
the convex maximum of two linear functions on the positive quadrant. -/
noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators ENNReal
namespace KLSImprovement.SingleSlotCounterexample
open KLS
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem potential_convex_combination (x y:Space 2) (t:ℝ) (ht0:0≤t) (ht1:t≤1):
    potential (t • x+(1-t) • y)≤t*potential x+(1-t)*potential y := by
  have hL:t*(x 0+x 1)+(1-t)*(y 0+y 1)≤
      t*max (x 0+x 1) (6*x 0-19*x 1)+(1-t)*max (y 0+y 1) (6*y 0-19*y 1) :=
    add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ht0)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr ht1))
  have hR:t*(6*x 0-19*x 1)+(1-t)*(6*y 0-19*y 1)≤
      t*max (x 0+x 1) (6*x 0-19*x 1)+(1-t)*max (y 0+y 1) (6*y 0-19*y 1) :=
    add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ht0)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (sub_nonneg.mpr ht1))
  calc
    potential (t • x+(1-t) • y)=
        max (t*(x 0+x 1)+(1-t)*(y 0+y 1))
          (t*(6*x 0-19*x 1)+(1-t)*(6*y 0-19*y 1))-Real.log (6/5:ℝ) := by
      unfold potential
      congr 1
      apply congrArg₂ max <;>
        simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] <;>ring
    _ ≤ t*max (x 0+x 1) (6*x 0-19*x 1)+
        (1-t)*max (y 0+y 1) (6*y 0-19*y 1)-Real.log (6/5:ℝ) :=
      sub_le_sub_right (max_le hL hR) _
    _ = t*potential x+(1-t)*potential y := by unfold potential;ring

theorem density_pointwise_logConcave (x y:Space 2) (t:ℝ) (ht0:0<t) (ht1:t<1):
    density x^t*density y^(1-t)≤density (t • x+(1-t) • y) := by
  unfold density
  by_cases hx:0≤x 0 ∧ 0≤x 1
  · by_cases hy:0≤y 0 ∧ 0≤y 1
    · have hz:0≤(t • x+(1-t) • y) 0 ∧ 0≤(t • x+(1-t) • y) 1 := by
        constructor
        · change 0≤t*x 0+(1-t)*y 0
          exact add_nonneg (mul_nonneg ht0.le hx.1) (mul_nonneg (sub_pos.mpr ht1).le hy.1)
        · change 0≤t*x 1+(1-t)*y 1
          exact add_nonneg (mul_nonneg ht0.le hx.2) (mul_nonneg (sub_pos.mpr ht1).le hy.2)
      rw [ite_eq_left hx,ite_eq_left hy,ite_eq_left hz,
        ←exp_neg_affine_eq_geometric (potential x) (potential y) t (1-t)
          ht0.le (sub_pos.mpr ht1).le]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg
        (potential_convex_combination x y t ht0.le ht1.le)))
    · simp only [hy,ite_false,ENNReal.zero_rpow_of_pos (sub_pos.mpr ht1),mul_zero]
      exact zero_le
  · simp only [hx,ite_false,ENNReal.zero_rpow_of_pos ht0,zero_mul]
    exact zero_le

theorem raw_logConcave :measureLogConcave rawMeasure := by
  rw [rawMeasure_eq_density]
  exact measureLogConcave_withDensity_of_pointwise density_measurable density_pointwise_logConcave

end KLSImprovement.SingleSlotCounterexample
#print axioms KLSImprovement.SingleSlotCounterexample.raw_logConcave
