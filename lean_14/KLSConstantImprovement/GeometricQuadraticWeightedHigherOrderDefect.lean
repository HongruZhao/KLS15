import KLSConstantImprovement.ResponseCurvatureProductionBudget

/-! Same geometric quadratic rows and FULL constant symmetric cubic tensor.
The cyclic source IBP, three-slot tensor contraction and source/domain
identifications are analytical inputs. This gives a quantitative source
contraction and an exact higher-order defect; its final payment is OPEN.
No generic matrix response lift or original CP improvement is asserted. -/
noncomputable section
namespace KLSConstantImprovement.GeometricQuadraticWeightedHigherOrderDefect

theorem weighted_geometric_row_defect
    {m W theta ell paired cross prod p loss d : ℝ}
    (hProduction : 2*m = theta+2*cross-prod)
    (hSourceIBP : paired = cross-ell)
    (hSquare : prod = p+loss+d-W+2*paired) :
    2*m = W+theta+2*ell-p-loss-d := by
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem opposite_three_slot_cauchy (a b : E) {ell W gamma : ℝ}
    (hPair : ell = inner ℝ a b)
    (hTop : ‖a‖^2 = W) (hBottom : ‖b‖^2 = gamma) :
    ell^2 ≤ W*gamma := by
  have hc := abs_real_inner_le_norm a b
  have hn := norm_nonneg a
  have hm := norm_nonneg b
  have hp := mul_nonneg (sub_nonneg.mpr hc)
    (add_nonneg (mul_nonneg hn hm) (abs_nonneg (inner ℝ a b)))
  have hid : (‖a‖*‖b‖)^2 = W*gamma := by rw [mul_pow, hTop, hBottom]
  rw [hPair]
  nlinarith [sq_abs (inner ℝ a b)]

theorem uniform_actual_row_contraction_eight
    {ell W gamma theta N : ℝ} (hN : 0 ≤ N)
    (hW : 0 ≤ W) (hTheta : 0 ≤ theta)
    (hCauchy : ell^2 ≤ W*gamma) (hRow : gamma ≤ theta)
    (hKernel : W ≤ 3*(1+Real.sqrt 2)*N)
    (hCharge : theta ≤ ((15+3*Real.sqrt 41)/4)*N) :
    |ell| ≤ 8*N := by
  have h2p := Real.sqrt_nonneg (2:ℝ)
  have h2s := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h2u : Real.sqrt (2:ℝ) ≤ 10/7 := by nlinarith
  have h41p := Real.sqrt_nonneg (41:ℝ)
  have h41s := Real.sq_sqrt (show (0:ℝ) ≤ 41 by norm_num)
  have h41u : Real.sqrt (41:ℝ) ≤ 13/2 := by nlinarith
  have hk : W ≤ (51/7:ℝ)*N := by
    have h := mul_le_mul_of_nonneg_right h2u hN
    nlinarith
  have ht : theta ≤ (69/8:ℝ)*N := by
    have h := mul_le_mul_of_nonneg_right h41u hN
    nlinarith
  have hrow := mul_le_mul_of_nonneg_left hRow hW
  have hwt := mul_le_mul_of_nonneg_right hk hTheta
  have hnt := mul_le_mul_of_nonneg_left ht (show (0:ℝ) ≤ (51/7:ℝ)*N by positivity)
  have hsquare : ell^2 ≤ (8*N)^2 := by
    nlinarith [sq_nonneg N]
  have habs : |ell|^2 ≤ (8*N)^2 := by simpa only [sq_abs] using hsquare
  exact le_of_sq_le_sq habs (by positivity)

theorem exact_compatible_cubic_higher_order_defect
    {V m W theta ell p loss d skew matching curv : ℝ}
    (hRow : 2*m = W+theta+2*ell-p-loss-d)
    (hVariance : V = 36*(m-skew)-matching-curv) :
    V-36*W = 18*(theta+2*ell-W-p-loss-d-2*skew)-matching-curv := by
  nlinarith

theorem paid_compatible_budget_gives_thirty_six_kernel
    {V m W theta ell p loss d skew matching curv : ℝ}
    (hRow : 2*m = W+theta+2*ell-p-loss-d)
    (hVariance : V = 36*(m-skew)-matching-curv)
    (hPaid : theta+2*ell ≤ W+p+loss+d+2*skew+(matching+curv)/18) :
    V ≤ 36*W := by
  have h := exact_compatible_cubic_higher_order_defect hRow hVariance
  linarith

end KLSConstantImprovement.GeometricQuadraticWeightedHigherOrderDefect
#print axioms KLSConstantImprovement.GeometricQuadraticWeightedHigherOrderDefect.weighted_geometric_row_defect
#print axioms KLSConstantImprovement.GeometricQuadraticWeightedHigherOrderDefect.opposite_three_slot_cauchy
#print axioms KLSConstantImprovement.GeometricQuadraticWeightedHigherOrderDefect.uniform_actual_row_contraction_eight
#print axioms KLSConstantImprovement.GeometricQuadraticWeightedHigherOrderDefect.exact_compatible_cubic_higher_order_defect
#print axioms KLSConstantImprovement.GeometricQuadraticWeightedHigherOrderDefect.paid_compatible_budget_gives_thirty_six_kernel
