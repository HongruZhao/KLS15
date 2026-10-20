import KLSConstantImprovement.ActualCubicRowVariational405
import KLSConstantImprovement.ActualQuadraticHilbertMatrix405

/-! The genuine cubic inverse Hessian pairs with the actual quadratic
inverse matrix in the matrix-valued L2 Hilbert space. No scalar response
comparison or second Stein identity is assumed. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace Filter ProbabilityTheory
open scoped BigOperators
namespace KLSConstantImprovement.ActualCubicMatrixFactorization405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCubicRepresenter ActualCubicGradientEnergy ActualCubicSourceDatum405
open ActualNaturalGradientForm405 ActualSourceQuadraticEta405 ActualCubicRowVariational405
open ActualSourceNaturalTargetCurvatureDomain405 ActualSourceNaturalWhitenedHessian405
open ActualSourceNaturalGaffney405 ActualSourceNaturalHessian405 ActualCompactRawMetricGraph
open ActualSourceLocalizedGaffney405
open ActualQuadraticHilbertMatrix405 ActualWeakCanonicalMetricOrdinaryGraph
open ActualResponseWeightedEnergy405 ActualSourceMetricFaithfulness405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem natural_rawGradient_metric_derivative_white_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (Du : Fin n → Fin n → Space n → ℝ)
    (i r : Fin n) :
    rawCanonicalMetricDerivative d.potential (fun a x => naturalCanonicalHessian d g Du x i a) r
      =ᵐ[potentialMeasure d.potential] fun x =>
        (canonicalMetricUnroot d.potential x * naturalWhitenedHessian d g Du x) i r := by
  filter_upwards [d.hessian_ae_source, naturalCanonicalHessian_reconstruct_ae d g Du] with x hx hC
  let S := canonicalMetricUnroot d.potential x
  let R := canonicalMetricRoot d.potential x
  let C := naturalCanonicalHessian d g Du x
  let W := naturalWhitenedHessian d g Du x
  have hSR : S * R = 1 := canonicalMetricUnroot_mul_root_at hx.1
  have hCR : C * R = S * W := by
    change C = S * W * S at hC
    rw [hC, Matrix.mul_assoc, hSR, Matrix.mul_one]
  change _ = (S * W) i r
  rw [← hCR]
  simp only [Matrix.mul_apply, rawCanonicalMetricDerivative]
  apply Finset.sum_congr rfl
  intro a _
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm _
  change R r a * C i a = C i a * R a r
  rw [hR.apply r a]
  ring

def naturalWhiteLp (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hW : ∀ i j, MemLp (fun x => naturalWhitenedHessian d g Du x i j) 2 (potentialMeasure d.potential))
    (i j : Fin n) : Lp ℝ 2 (potentialMeasure d.potential) := (hW i j).toLp _

theorem naturalWhiteLp_coe (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hW : ∀ i j, MemLp (fun x => naturalWhitenedHessian d g Du x i j) 2 (potentialMeasure d.potential))
    (i j : Fin n) : (naturalWhiteLp d g Du hW i j : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] fun x => naturalWhitenedHessian d g Du x i j :=
  (hW i j).coeFn_toLp

theorem natural_gradient_white_Lp (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hW : ∀ i j, MemLp (fun x => naturalWhitenedHessian d g Du x i j) 2 (potentialMeasure d.potential))
    (U : Fin n → CanonicalMetricH1 d.potential)
    (hU : ∀ i r, (canonicalMetricGradient d.potential r (U i) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential
        (fun a x => naturalCanonicalHessian d g Du x i a) r) (i r : Fin n) :
    canonicalMetricGradient d.potential r (U i) =
      ∑ a, sourceUnrootMultiplier d i a (naturalWhiteLp d g Du hW a r) := by
  apply Lp.ext
  filter_upwards [hU i r, natural_rawGradient_metric_derivative_white_ae d g Du i r,
    Lp.coeFn_finsetSum Finset.univ (fun a => sourceUnrootMultiplier d i a (naturalWhiteLp d g Du hW a r)),
    ae_all_iff.mpr (fun a => sourceUnrootMultiplier_coe d i a (naturalWhiteLp d g Du hW a r)),
    ae_all_iff.mpr (fun a => naturalWhiteLp_coe d g Du hW a r)] with x hu hd hs hm hw
  rw [hu, hd, hs]
  simp only [Finset.sum_apply, hm, hw, Matrix.mul_apply]

abbrev MatrixL2 (φ : Space n → ℝ) :=
  PiLp 2 (fun _ : Fin n => PiLp 2 (fun _ : Fin n => Lp ℝ 2 (potentialMeasure φ)))

def actualQuadraticHilbert (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    MatrixL2 d.potential := WithLp.toLp 2 fun i => WithLp.toLp 2 (actualQuadraticWhiteLp d T i)

def naturalWhiteHilbert (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hW : ∀ i j, MemLp (fun x => naturalWhitenedHessian d g Du x i j) 2 (potentialMeasure d.potential)) :
    MatrixL2 d.potential := WithLp.toLp 2 fun i => WithLp.toLp 2 (naturalWhiteLp d g Du hW i)

theorem actualQuadraticHilbert_norm (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ‖actualQuadraticHilbert d T‖ ^ 2 = ∫ x, actualQuadraticMatrixCost d T x ∂potentialMeasure d.potential := by
  simp only [actualQuadraticHilbert, PiLp.norm_sq_eq_of_L2, PiLp.toLp_apply]
  exact actual_quadratic_Lp_norm_cost d T

theorem naturalWhiteHilbert_norm (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hW : ∀ i j, MemLp (fun x => naturalWhitenedHessian d g Du x i j) 2 (potentialMeasure d.potential)) :
    ‖naturalWhiteHilbert d g Du hW‖ ^ 2 =
      ∫ x, matrixFrobeniusSq (naturalWhitenedHessian d g Du x) ∂potentialMeasure d.potential := by
  simp only [naturalWhiteHilbert, PiLp.norm_sq_eq_of_L2, PiLp.toLp_apply]
  simp_rw [L2.norm_sq_eq_integral_sq]
  have hi (i j : Fin n) : Integrable (fun x => naturalWhiteLp d g Du hW i j x ^ 2)
      (potentialMeasure d.potential) := (Lp.memLp _).integrable_sq
  have hrow (i : Fin n) : (∑ j, ∫ x, naturalWhiteLp d g Du hW i j x ^ 2 ∂potentialMeasure d.potential) =
      ∫ x, ∑ j, naturalWhiteLp d g Du hW i j x ^ 2 ∂potentialMeasure d.potential :=
    (integral_finsetSum Finset.univ fun j _ => hi i j).symm
  simp_rw [hrow]
  rw [← integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun j _ => hi i j)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => naturalWhiteLp_coe d g Du hW i j] with x hw
  simp only [hw, matrixFrobeniusSq]

theorem actual_row_energy_white_pairing (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (Du : Fin n → Fin n → Space n → ℝ)
    (hW : ∀ i j, MemLp (fun x => naturalWhitenedHessian d g Du x i j) 2 (potentialMeasure d.potential))
    (U : Fin n → CanonicalMetricH1 d.potential)
    (hU : ∀ i r, (canonicalMetricGradient d.potential r (U i) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential
        (fun a x => naturalCanonicalHessian d g Du x i a) r) :
    (∑ i, canonicalMetricEnergy d.potential (quadraticSourceEta d (T i)) (U i)) =
      inner ℝ (actualQuadraticHilbert d T) (naturalWhiteHilbert d g Du hW) := by
  simp only [canonicalMetricEnergy_apply, natural_gradient_white_Lp d g Du hW U hU,
    inner_sum, sourceUnrootMultiplier_inner]
  simp only [actualQuadraticHilbert, naturalWhiteHilbert, PiLp.inner_apply, PiLp.toLp_apply,
    actualQuadraticWhiteLp, sum_inner]
  calc
    _ = ∑ i, ∑ a, ∑ r, inner ℝ
        (sourceUnrootMultiplier d i a (canonicalMetricGradient d.potential r (quadraticSourceEta d (T i))))
        (naturalWhiteLp d g Du hW a r) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ r, inner ℝ
        (sourceUnrootMultiplier d i a (canonicalMetricGradient d.potential r (quadraticSourceEta d (T i))))
        (naturalWhiteLp d g Du hW a r) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm

theorem exists_actual_cubic_matrix_pairing_of_mass_bound (d : SourceData μ)
    (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (actualCubicDatum d T)) x ≤ C) :
    ∃ W : MatrixL2 d.potential,
      ‖W‖ ^ 2 ≤ variance (tensorPolynomial μ T) μ ∧
      variance (tensorPolynomial μ T) μ = 6 * inner ℝ (actualQuadraticHilbert d T) W := by
  obtain ⟨Du, hW, hb, U, hU, hv⟩ := exists_actual_cubic_row_variational_of_mass_bound d hn hμ T hT12 hT23 hC hM
  refine ⟨naturalWhiteHilbert d (actualCubicDatum d T) Du hW, ?_, ?_⟩
  · rwa [naturalWhiteHilbert_norm]
  · rwa [actual_row_energy_white_pairing d T (actualCubicDatum d T) Du hW U hU] at hv

end KLSConstantImprovement.ActualCubicMatrixFactorization405
#print axioms KLSConstantImprovement.ActualCubicMatrixFactorization405.actual_row_energy_white_pairing
#print axioms KLSConstantImprovement.ActualCubicMatrixFactorization405.exists_actual_cubic_matrix_pairing_of_mass_bound
#print axioms KLSConstantImprovement.ActualCubicMatrixFactorization405.actualQuadraticHilbert_norm
#print axioms KLSConstantImprovement.ActualCubicMatrixFactorization405.naturalWhiteHilbert_norm
