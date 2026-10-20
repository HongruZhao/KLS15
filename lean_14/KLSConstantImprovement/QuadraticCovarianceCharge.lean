import QuadraticAppellBridge

/-!
An actual covariance charge for the original quadratic test subclass.
The law is any admissible isotropic log-concave measure, not an exponential
product. The estimate does not extend the Schur condition to arbitrary tests.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Filter
open scoped BigOperators ENNReal ContDiff

namespace KLSConstantImprovement.QuadraticCovarianceCharge
open KLS KLS.DeterministicBridge
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- The actual coordinate covariance vector under an isotropic law. -/
def covarianceVector (μ : Measure (Space n)) (f : Space n → ℝ) : Space n :=
  WithLp.toLp 2 (fun i => ∫ x, x i * f x ∂μ)

theorem covarianceVector_pairing {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hiso : IsIsotropic μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (u : Space n) :
    inner ℝ (covarianceVector μ f) u = ∫ x, inner ℝ x u * f x ∂μ := by
  rw [inner_eq_coordinate_sum]
  change (∑ i, u i * ∫ x, x i * f x ∂μ) = _
  have he (x : Space n) : inner ℝ x u * f x =
      ∑ i, u i * (x i * f x) := by
    rw [inner_eq_coordinate_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  have hi (i : Fin n) : Integrable (fun x => u i * (x i * f x)) μ := by
    simpa only [Pi.mul_apply] using
      ((hiso.memLp_coordinate i).integrable_mul hf).const_mul (u i)
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp_rw [integral_const_mul]

/-- Isotropy makes coordinates an orthonormal system in centered L2. -/
theorem covarianceVector_norm_sq_le_variance {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hiso : IsIsotropic μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    ‖covarianceVector μ f‖ ^ 2 ≤ ProbabilityTheory.variance f μ := by
  let m := covarianceVector μ f
  have hpair := covarianceVector_pairing hiso hf m
  have hcs := hiso.integral_inner_mul_sq_le m hf
  rw [← hpair, real_inner_self_eq_norm_sq] at hcs
  by_cases hz : ‖m‖ ^ 2 = 0
  · change ‖m‖ ^ 2 ≤ _
    rw [hz]
    exact ProbabilityTheory.variance_nonneg f μ
  · have hp : 0 < ‖m‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    have hs : ‖m‖ ^ 2 * ‖m‖ ^ 2 ≤
        ‖m‖ ^ 2 * ProbabilityTheory.variance f μ := by nlinarith [hcs]
    exact (mul_le_mul_iff_of_pos_left hp).mp hs

theorem quadratic_original_test {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (A : Matrix (Fin n) (Fin n) ℝ) :
    LocallyLipschitzTests μ (quadraticAppellPrimitive μ A) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  refine ⟨?_, quadraticAppellPrimitive_memLp
    hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul A⟩
  have hd : ContDiff ℝ 1 (quadraticAppellPrimitive μ A) := by
    change ContDiff ℝ 1 (fun x => (1 / 2 : ℝ) *
      (matrixQuadratic A x - ∫ y, matrixQuadratic A y ∂μ))
    change ContDiff ℝ 1 ((1 / 2 : ℝ) •
      (fun x => matrixQuadratic A x - ∫ y, matrixQuadratic A y ∂μ))
    exact (((contDiff_matrixQuadratic A).sub contDiff_const).const_smul
      (1 / 2 : ℝ)).of_le (by simp)
  exact hd.locallyLipschitz

theorem quadratic_mean_gradient_zero {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (i : Fin n) :
    (∫ x, coordinateDerivative (quadraticAppellPrimitive μ A) i x ∂μ) = 0 := by
  have he : (fun x => coordinateDerivative (quadraticAppellPrimitive μ A) i x) =
      (fun x => ∑ j, A i j * x j) := by
    funext x
    rw [coordinateDerivative_eq_gradient, quadraticAppellPrimitive_gradient μ A hA,
      matrixAction_apply]
  rw [he, integral_finsetSum Finset.univ (fun j _ =>
    (hμ.isotropic.integrable_coordinate j).const_mul (A i j))]
  simp [integral_const_mul, hμ.isotropic.integral_coordinate]

theorem quadratic_gradient_energy {μ : Measure (Space n)}
    (hiso : IsIsotropic μ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    (∫ x, ‖gradient (quadraticAppellPrimitive μ A) x‖ ^ 2 ∂μ) =
      matrixFrobeniusSq A := by
  simp_rw [quadraticAppellPrimitive_gradient μ A hA]
  exact hiso.integral_matrixAction_norm_sq A

theorem quadratic_extended_energy {μ : Measure (Space n)}
    (hiso : IsIsotropic μ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    energy μ (quadraticAppellPrimitive μ A) = ENNReal.ofReal (matrixFrobeniusSq A) := by
  unfold energy
  simp_rw [quadraticAppellPrimitive_gradient μ A hA]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hiso.integrable_matrixAction_norm_sq A)
    (Eventually.of_forall fun _ => sq_nonneg _), hiso.integral_matrixAction_norm_sq A]

/-- A genuine reverse covariance observation bound, restricted to quadratics. -/
theorem quadratic_reverse_covariance_le_two {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    ‖covarianceVector μ (quadraticAppellPrimitive μ A)‖ ^ 2 ≤
      2 * (∫ x, ‖gradient (quadraticAppellPrimitive μ A) x‖ ^ 2 ∂μ) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hf := (quadratic_original_test hμ A).2
  have hb := covarianceVector_norm_sq_le_variance hμ.isotropic hf
  have hv := ProbabilityTheory.variance_eq_sub hf
  rw [quadraticAppellPrimitive_integral_eq_zero
    hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul A] at hv
  simp only [Pi.pow_apply, zero_pow (by norm_num : 2 ≠ 0), sub_zero] at hv
  have hq := quadraticAppellPrimitive_integral_sq_le_two hμ A hA
  rw [quadratic_gradient_energy hμ.isotropic A hA]
  simpa using hb.trans (by simpa [hv] using hq)

/-- Universal covariance charge one on the actual original quadratic tests.
This is stronger than charge one third required by the Schur target at four,
but proves that target only on this particular test subclass. -/
theorem quadratic_joint_charge_one {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    ProbabilityTheory.variance (quadraticAppellPrimitive μ A) μ +
      ‖covarianceVector μ (quadraticAppellPrimitive μ A)‖ ^ 2 ≤
        4 * (∫ x, ‖gradient (quadraticAppellPrimitive μ A) x‖ ^ 2 ∂μ) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hf := (quadratic_original_test hμ A).2
  have hm := covarianceVector_norm_sq_le_variance hμ.isotropic hf
  have hv := ProbabilityTheory.variance_eq_sub hf
  rw [quadraticAppellPrimitive_integral_eq_zero
    hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul A] at hv
  simp only [Pi.pow_apply, zero_pow (by norm_num : 2 ≠ 0), sub_zero] at hv
  have hq := quadraticAppellPrimitive_integral_sq_le_two hμ A hA
  rw [quadratic_gradient_energy hμ.isotropic A hA]
  nlinarith [hq]

theorem quadratic_joint_charge_one_original_energy {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    ENNReal.ofReal (ProbabilityTheory.variance (quadraticAppellPrimitive μ A) μ +
      ‖covarianceVector μ (quadraticAppellPrimitive μ A)‖ ^ 2) ≤
        (4 : ℝ≥0∞) * energy μ (quadraticAppellPrimitive μ A) := by
  have hb := quadratic_joint_charge_one hμ A hA
  rw [quadratic_gradient_energy hμ.isotropic A hA] at hb
  rw [quadratic_extended_energy hμ.isotropic A hA,
    show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  exact ENNReal.ofReal_le_ofReal hb

end KLSConstantImprovement.QuadraticCovarianceCharge

#print axioms KLSConstantImprovement.QuadraticCovarianceCharge.covarianceVector_norm_sq_le_variance
#print axioms KLSConstantImprovement.QuadraticCovarianceCharge.quadratic_original_test
#print axioms KLSConstantImprovement.QuadraticCovarianceCharge.quadratic_mean_gradient_zero
#print axioms KLSConstantImprovement.QuadraticCovarianceCharge.quadratic_extended_energy
#print axioms KLSConstantImprovement.QuadraticCovarianceCharge.quadratic_reverse_covariance_le_two
#print axioms KLSConstantImprovement.QuadraticCovarianceCharge.quadratic_joint_charge_one
#print axioms KLSConstantImprovement.QuadraticCovarianceCharge.quadratic_joint_charge_one_original_energy
