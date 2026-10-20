import KLSConstantImprovement.ActualResponseCompletionWhitening405
import KLSConstantImprovement.ActualBoundedConnectionMatrixDomain405
import KLSConstantImprovement.ActualQuadraticJacobianEnergy405
import KLSConstantImprovement.ActualSourceResponseProduction405

/-! Global L2 domains for the two actual whitened production factors.
The same chosen natural Jacobian is used throughout. The only mass
hypothesis is the explicitly displayed quadratic natural mass bound. -/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualResponseSquareDomains405
open KLS ActualBoundedCanonicalSource ActualResponseProductionAlgebra405
open ActualResponseCompletionWhitening405 ActualBoundedConnectionMatrixDomain405
open ActualQuadraticJacobianEnergy405 ActualQuadraticResponseField405 ActualQuadraticResponseMetricFlux405
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualSourceConnectionFields405 ActualSourceNaturalHessian405 ActualSourceNaturalWhitenedHessian405
open ActualWhitenedWeakMatrixDomain405 ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricCore
open ActualWeakCanonicalMetricOrdinaryGraph ActualSourceLimitFluxDomains405 ActualSourceMetricFaithfulness405
open ActualSourceGradientCoefficientPassage405 ActualBoundedRawSourceCalculus405 ActualAffineMatrixTests405
open ActualQuarticThirdWhitening405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def actualResponseLeftFactor (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  completionLeft (coordinateHessian d.potential x) (coordinateHessian d.potential x)⁻¹
    (sourceThirdAlong d (fun a y => quadraticResponseMatrix d T y i a) x)
    (responseRowJacobian d hn hμ T i x) (T i)

def actualResponseRightFactor (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  completionRight (coordinateHessian d.potential x) (responseRowJacobian d hn hμ T i x) (T i)

theorem sourceThirdAlong_response (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Space n) :
    sourceThirdAlong d (fun a y => quadraticResponseMatrix d T y i a) x =
      (2 : ℝ) • sourceThirdAlong d (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x -
        sourceThirdAlong d (fun a y => actualAffineMatrix d T y i a) x := by
  ext a b
  simp only [sourceThirdAlong, quadraticResponseMatrix, Matrix.of_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
    quadraticRowFlux, mul_assoc, Finset.mul_sum]

theorem responseRowJacobian_eq (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {x : Space n} (hH : (coordinateHessian d.potential x).IsSymm) (i : Fin n) :
    responseRowJacobian d hn hμ T i x = (2 : ℝ) • quadraticJacobianMatrix d hn hμ (T i) x -
      T i * coordinateHessian d.potential x := by
  ext a b
  change 2 * quadraticFluxJacobian d hn hμ (T i) a b x -
    mixFamily (coordinateHessian d.potential x) T b i a = _
  rw [full_tensor_affine_derivative _ hH T h12 h23]
  rfl

theorem actualResponseLeftFactor_white_ae (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j) (i : Fin n) :
    sourceWhitenedJacobian d (actualResponseLeftFactor d hn hμ T i) =ᵐ[potentialMeasure d.potential]
      fun x => (2 : ℝ) • naturalWhitenedHessian d (quadraticSourceDatum d (T i))
        (quadraticFluxJacobian d hn hμ (T i)) x -
        (2 : ℝ) • (canonicalMetricUnroot d.potential x * T i * canonicalMetricUnroot d.potential x) -
          sourceWhitenedMatrix d (sourceThirdAlong d (fun a y => actualAffineMatrix d T y i a)) x := by
  filter_upwards [d.hessian_ae_source] with x hx
  let H := coordinateHessian d.potential x
  let J := H⁻¹
  let S := canonicalMetricUnroot d.potential x
  let R := canonicalMetricRoot d.potential x
  have hSJ : S * J = R := by
    have hRR : R * R = J := by
      have hgram := canonicalMetricRoot_gram_at hx.1
      have hR : (canonicalMetricRoot d.potential x).IsSymm := inverseSqrtMatrix_isSymm _
      rwa [hR.eq] at hgram
    rw [← hRR, ← Matrix.mul_assoc, canonicalMetricUnroot_mul_root_at hx.1, Matrix.one_mul]
  change S * completionLeft H J _ (responseRowJacobian d hn hμ T i x) (T i) * R = _
  rw [sourceThirdAlong_response, responseRowJacobian_eq d hn hμ T h12 h23 hx.1.isHermitian.isSymm]
  exact completionLeft_whitening H J S R (quadraticJacobianMatrix d hn hμ (T i) x)
    (sourceThirdAlong d (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x)
    (sourceThirdAlong d (fun a y => actualAffineMatrix d T y i a) x) (T i) hSJ
    (hessian_mul_canonicalMetricRoot_at hx.1) (canonicalMetricRoot_mul_hessian_at hx.1)

theorem actualResponseRightFactor_white_ae (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j) (i : Fin n) :
    sourceWhitenedJacobian d (actualResponseRightFactor d hn hμ T i) =ᵐ[potentialMeasure d.potential]
      fun x => (2 : ℝ) • sourceWhitenedJacobian d (quadraticJacobianMatrix d hn hμ (T i)) x := by
  filter_upwards [d.hessian_ae_source] with x hx
  change canonicalMetricUnroot d.potential x * completionRight (coordinateHessian d.potential x)
    (responseRowJacobian d hn hμ T i x) (T i) * canonicalMetricRoot d.potential x = _
  rw [responseRowJacobian_eq d hn hμ T h12 h23 hx.1.isHermitian.isSymm]
  exact completionRight_whitening _ _ _ _ _ (hessian_mul_canonicalMetricRoot_at hx.1)

theorem actual_constant_hessian_congruence_memLp_top (d : SourceData μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    MemLp (fun x => (canonicalMetricUnroot d.potential x * B * canonicalMetricUnroot d.potential x) a b)
      ∞ (potentialMeasure d.potential) := by
  have hm (i j : Fin n) : MemLp (fun x => (canonicalMetricUnroot d.potential x * B) i j)
      ∞ (potentialMeasure d.potential) :=
    memLp_matrix_mul_entries (p := ∞) (q := ∞) (r := ∞)
      (actualUnroot_entry_memLp_top d) (memLp_constant_matrix_entries B) i j
  exact memLp_matrix_mul_entries (p := ∞) (q := ∞) (r := ∞) hm (actualUnroot_entry_memLp_top d) a b

section Fixed
variable (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)

include h12 h23 hC hM in
theorem actualResponseLeftFactor_white_memLp (i a b : Fin n) :
    MemLp (fun x => sourceWhitenedJacobian d (actualResponseLeftFactor d hn hμ T i) x a b)
      2 (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hm : MemLp (fun x => 2 * naturalWhitenedHessian d (quadraticSourceDatum d (T i))
      (quadraticFluxJacobian d hn hμ (T i)) x a b -
      2 * (canonicalMetricUnroot d.potential x * T i * canonicalMetricUnroot d.potential x) a b -
      sourceWhitenedMatrix d (sourceThirdAlong d (fun r y => actualAffineMatrix d T y i r)) x a b)
      2 (potentialMeasure d.potential) :=
    (((quadraticCanonicalHessian_white_memLp_of_mass_bound d hn hμ (T i) hC (hM i) a b).const_mul 2).sub
      (((actual_constant_hessian_congruence_memLp_top d (T i) a b).mono_exponent (by simp)).const_mul 2)).sub
      (actual_affine_third_white_memLp d T i a b)
  apply (memLp_congr_ae ?_).mp hm
  filter_upwards [actualResponseLeftFactor_white_ae d hn hμ T h12 h23 i] with x hx
  exact (congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A a b) hx).symm

include h12 h23 in
theorem actualResponseRightFactor_white_memLp (i a b : Fin n) :
    MemLp (fun x => sourceWhitenedJacobian d (actualResponseRightFactor d hn hμ T i) x a b)
      2 (potentialMeasure d.potential) := by
  have hm := (quadraticFluxJacobian_white_memLp d hn hμ (T i) a b).const_mul 2
  apply (memLp_congr_ae ?_).mp hm
  filter_upwards [actualResponseRightFactor_white_ae d hn hμ T h12 h23 i] with x hx
  exact (congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A a b) hx).symm

end Fixed
end KLSConstantImprovement.ActualResponseSquareDomains405

#print axioms KLSConstantImprovement.ActualResponseSquareDomains405.actualResponseLeftFactor_white_ae
#print axioms KLSConstantImprovement.ActualResponseSquareDomains405.actualResponseLeftFactor_white_memLp
#print axioms KLSConstantImprovement.ActualResponseSquareDomains405.actualResponseRightFactor_white_memLp
