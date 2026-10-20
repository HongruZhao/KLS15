import KLSConstantImprovement.ActualCubicAffineQuadraticRegression

/-! Retain the coordinate covariance of the same unit test function when
applying the original-law affine mixed test. Optimizing the affine parameter
replaces C by C - ||Cov(f,X)||^2 in the squared covariance estimate.
This is a new original-law inequality, not a new universal CP endpoint.
The terminal still has to retain and use its own matching coordinate charge. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators ENNReal ContDiff
namespace KLSConstantImprovement.ActualSameTestAffineCovariance
open KLS KLS.DeterministicBridge KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
open ActualCubicQuadraticRegression ActualCubicAffineQuadraticRegression QuadraticCovarianceCharge
variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

theorem affine_covariance_scalar_saving {C r a E : ℝ}
    (hC : 0 < C) (hCr : 0 < C-r)
    (hbound : ∀ t : ℝ, (a+t*r)^2 ≤ C*(E+t^2*r)) :
    a^2 ≤ (C-r)*E := by
  have hb := hbound (a/(C-r))
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (C-r))
  have hid : (C-r)^2*((a+(a/(C-r))*r)^2-C*(E+(a/(C-r))^2*r)) =
      C*(C-r)*(a^2-(C-r)*E) := by
    field_simp [hCr.ne']
    <;> ring
  have hp : C*(C-r)*(a^2-(C-r)*E) ≤ 0 := by
    rw [←hid]
    nlinarith [hm]
  by_contra hh
  have hpos : 0 < a^2-(C-r)*E := by linarith
  have ht := mul_pos (mul_pos hC hCr) hpos
  linarith

theorem affine_mixed_same_test_covariance {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (B : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (u : Space n)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    covariance (affineQuadraticPerturbation μ T B s u) f μ =
      covariance (quadraticPerturbation μ T B s) f μ +
        inner ℝ (covarianceVector μ f) u := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hq := (quadraticPerturbation_original_test hμ T B s).2
  have hl := hμ.isotropic.memLp_inner u
  unfold affineQuadraticPerturbation
  rw [covariance_fun_add_left hq hl hf]
  congr 1
  rw [covariance_eq_sub hl hf, hμ.isotropic.integral_inner,
    zero_mul, sub_zero, covarianceVector_pairing hμ.isotropic hf u]
  rfl

theorem original_mixed_same_test_affine_saving {μ : Measure (Space n)}
    (hn : 1 ≤ n) (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c, T a b c = T b a c) (hT23 : ∀ a b c, T a b c = T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (s C : ℝ)
    (hC : LongPrefixCubicBellmanEndpoint.bound ≤ C)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (hunit : (∫ x, (f x)^2 ∂μ) = 1) :
    (covariance (quadraticPerturbation μ T B s) f μ)^2 ≤
      (C-‖covarianceVector μ f‖^2)*
        (9*(fourthContraction μ T+2*tensorSquare T)+4*s^2*matrixFrobeniusSq B-
          12*s*quadraticGradientPairing μ T B) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hC1 : 1 < C := lt_of_lt_of_le
    (by norm_num [LongPrefixCubicBellmanEndpoint.bound]) hC
  have hfvar : ProbabilityTheory.variance f μ ≤ 1 := by
    rw [ProbabilityTheory.variance_eq_sub hf]
    change (∫ x, (f x)^2 ∂μ)-(∫ x, f x ∂μ)^2 ≤ 1
    rw [hunit]
    nlinarith [sq_nonneg (∫ x, f x ∂μ)]
  have hr := (covarianceVector_norm_sq_le_variance hμ.isotropic hf).trans hfvar
  apply affine_covariance_scalar_saving (by linarith) (by linarith)
  intro t
  let u := t • covarianceVector μ f
  have hp := affineQuadraticPerturbation_poincare hn hμ T hT12 hT23 B hB s u C hC
  rw [←affineQuadraticPerturbation_variance hμ T B s u] at hp
  have htest := (affineQuadraticPerturbation_original_test hμ T B s u).2
  have hcs := covariance_sq_le_variance_mul_variance htest hf
  have hpaid := mul_le_mul_of_nonneg_left hfvar
    (ProbabilityTheory.variance_nonneg (affineQuadraticPerturbation μ T B s u) μ)
  have hb : (covariance (affineQuadraticPerturbation μ T B s u) f μ)^2 ≤
      ProbabilityTheory.variance (affineQuadraticPerturbation μ T B s u) μ :=
    hcs.trans (by simpa only [mul_one] using hpaid)
  rw [affine_mixed_same_test_covariance hμ T B s u hf] at hb
  dsimp only [u] at hb hp
  rw [inner_smul_right, real_inner_self_eq_norm_sq] at hb
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hp
  exact hb.trans hp

end KLSConstantImprovement.ActualSameTestAffineCovariance
#print axioms KLSConstantImprovement.ActualSameTestAffineCovariance.affine_covariance_scalar_saving
#print axioms KLSConstantImprovement.ActualSameTestAffineCovariance.affine_mixed_same_test_covariance
#print axioms KLSConstantImprovement.ActualSameTestAffineCovariance.original_mixed_same_test_affine_saving
