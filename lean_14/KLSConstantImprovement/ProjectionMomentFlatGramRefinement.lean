import KLSConstantImprovement.HessianMomentScalar

/-! Formal consequences of the retained projection third-moment proof.
The projection/source two-moment and mean-power identities are explicit
inputs. The tensor consequence concerns flat nonzero slice Gram only;
neither it nor the residual corollary is a new all-tensor Poincare bound. -/
noncomputable section
namespace KLSConstantImprovement.ProjectionMomentFlatGramRefinement

theorem projection_third_moment_thirty_six_fifths {r m2 m3 s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hcircle : (m2-r)^2+s^2 ≤ r^2)
    (hthird : m3 ≤ 3*(m2+s)) (hmean : m3 ≤ 4*m2) :
    m3 ≤ (36/5)*r := by
  by_cases hlow : m2 ≤ (9/5)*r
  · linarith
  have hhigh : (9/5)*r < m2 := lt_of_not_ge hlow
  have hm2upper : m2 ≤ 2*r := by
    by_contra hh
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hh))
      (show 0 < m2 by linarith)
    nlinarith [sq_nonneg s]
  have hprod : 0 ≤ (m2-(9/5)*r)*(m2-(8/5)*r) :=
    mul_nonneg (by linarith) (by linarith)
  have hv : 0 ≤ (12/5)*r-m2 := by linarith
  have hsq : s^2 ≤ ((12/5)*r-m2)^2 := by nlinarith
  have hsb : s ≤ (12/5)*r-m2 := by
    by_contra hh
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hh))
      (show 0 < s+((12/5)*r-m2) by linarith)
    nlinarith
  linarith

/-- The actual flat-Gram interpolation/support binding is a paper input. -/
theorem flat_gram_tensor_third_transfer {N W lam r M : ℝ}
    (hlam : 0 ≤ lam) (hN : N = lam*r)
    (hpoint : W ≤ lam*M) (hprojection : M ≤ (36/5)*r) :
    W ≤ (36/5)*N := by
  have h := mul_le_mul_of_nonneg_left hprojection hlam
  rw [hN]
  nlinarith

theorem flat_gram_affine_trace {N W J : ℝ}
    (hW : W ≤ (36/5)*N)
    (hJ : J ≤ (1+Real.sqrt 2)*W) :
    J ≤ ((36/5)*(1+Real.sqrt 2))*N := by
  have h := mul_le_mul_of_nonneg_left hW
    (show 0 ≤ 1+Real.sqrt 2 by positivity)
  nlinarith

/-- Same-source residual90 remains an unproved universal premise. -/
theorem flat_gram_residual_ninety_gives_raw250 {N V J : ℝ}
    (hN : 0 ≤ N)
    (hJ : J ≤ ((36/5)*(1+Real.sqrt 2))*N)
    (hresidual : V-9*J ≤ 90*N) : V ≤ 250*N := by
  have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hpos := Real.sqrt_nonneg (2:ℝ)
  have hc : ((774/5)+(324/5)*Real.sqrt 2 : ℝ) < 250 := by
    nlinarith
  have h := mul_le_mul_of_nonneg_right hc.le hN
  nlinarith

theorem preserved_exponential_third : (6:ℝ) < 36/5 := by norm_num

end KLSConstantImprovement.ProjectionMomentFlatGramRefinement
#print axioms KLSConstantImprovement.ProjectionMomentFlatGramRefinement.projection_third_moment_thirty_six_fifths
#print axioms KLSConstantImprovement.ProjectionMomentFlatGramRefinement.flat_gram_tensor_third_transfer
#print axioms KLSConstantImprovement.ProjectionMomentFlatGramRefinement.flat_gram_affine_trace
#print axioms KLSConstantImprovement.ProjectionMomentFlatGramRefinement.flat_gram_residual_ninety_gives_raw250
#print axioms KLSConstantImprovement.ProjectionMomentFlatGramRefinement.preserved_exponential_third
