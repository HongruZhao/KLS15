import ActualDampedLaplaceJets
import AdmissibleLawCompactness
import KLS.AffineWhitening
import KLS.TiltCovariancePositive
import KLS.AdaptiveExponentConcavity

/-! Actual noncompact tilt laws have full support dimension and strictly
positive covariance. Their centered inverse-square-root pushforward belongs
to the original admissible class throughout a genuine local tilt domain. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem covarianceMatrix_posDef_of_memLp_full_support {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hid : MemLp (fun x : Space n => x) 2 μ)
    (hfull : affineSpan ℝ μ.support = ⊤) : (covarianceMatrix μ).PosDef := by
  have hs : (covarianceBilin μ).toBilinForm.IsSymm := ⟨covarianceBilin_comm⟩
  change ((covarianceBilin μ).toBilinForm.toMatrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).PosDef
  apply (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis _ hs).mp
  intro u hu
  change 0 < covarianceBilin μ u u
  rw [covarianceBilin_self hid]
  apply lt_of_le_of_ne' (variance_nonneg _ _)
  intro hz
  have hae := ae_eq_integral_of_variance_eq_zero (hid.const_inner u) hz
  exact hu (eq_zero_of_affineSpan_support_eq_top_ae_inner_eq_const hfull hae)

 theorem logConcave_memLp_id {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) : MemLp (fun x : Space n => x) 2 μ := by
  apply MemLp.of_eval_piLp
  intro i
  exact memLp_two_of_norm_pow_bound hLC (by fun_prop) 1
    (fun x => by simpa only [pow_one] using PiLp.norm_apply_le x i)

 theorem actualDampedTiltLaw_eq_adaptiveLaw {n : ℕ} (μ : Measure (Space n))
    (z : Space n) (s : ℝ) :
    actualDampedTiltLaw μ z s = KLS.AdaptiveLocalization.law μ (fun i => z i)
      (s • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  unfold actualDampedTiltLaw KLS.AdaptiveLocalization.law
  congr 1
  funext x
  rw [KLS.AdaptiveLocalization.exponent_eq_dotProduct]
  simp only [Matrix.smul_mulVec,Matrix.one_mulVec,smul_eq_mul,dotProduct_smul,
    EuclideanSpace.inner_eq_star_dotProduct,Pi.star_apply,star_trivial]
  rw [dotProduct_comm]
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct,pow_two]
  ring

 theorem actualDampedTiltLaw_logConcave {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (z : Space n) {s : ℝ} (hs : 0 ≤ s) :
    measureLogConcave (actualDampedTiltLaw μ z s) := by
  rw [actualDampedTiltLaw_eq_adaptiveLaw]
  exact KLS.AdaptiveLocalization.law_measureLogConcave_of_admissible hμ _
    (Matrix.PosSemidef.one.smul hs)

 theorem integrable_exp_actualDampedExponent {n : ℕ} {μ : Measure (Space n)}
    {r : ℝ} (hD : LocalNormExponentialDomain μ (fun _ => 1) r)
    {z : Space n} (hz : ‖z‖ ≤ r) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun x => Real.exp (inner ℝ z x-s*(‖x‖^2/2))) μ := by
  have hi := (LocalNormExponentialDomain.mul_nonneg_damping hD hs).integrable_tilt hz
  convert hi using 1
  funext x
  simp only [one_mul,← Real.exp_add]
  congr 1
  ring

 theorem actualDampedTiltLaw_support_eq {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] {z : Space n} {s : ℝ}
    (hi : Integrable (fun x => Real.exp (inner ℝ z x-s*(‖x‖^2/2))) μ) :
    (actualDampedTiltLaw μ z s).support = μ.support :=
  Set.Subset.antisymm (tilted_absolutelyContinuous μ _).support_mono
    (absolutelyContinuous_tilted hi).support_mono

 theorem actualDampedTiltLaw_whitening_admissible {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {z : Space n} {s : ℝ} (hs : 0 ≤ s)
    (hi : Integrable (fun x => Real.exp (inner ℝ z x-s*(‖x‖^2/2))) μ) :
    admissibleMeasure (whitenedMeasure (actualDampedTiltLaw μ z s)) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  letI : IsProbabilityMeasure (actualDampedTiltLaw μ z s) := isProbabilityMeasure_tilted hi
  have hLC := actualDampedTiltLaw_logConcave hμ z hs
  have hid := logConcave_memLp_id hLC
  have hfull : affineSpan ℝ (actualDampedTiltLaw μ z s).support = ⊤ := by
    rw [actualDampedTiltLaw_support_eq hi]
    exact hμ.isotropic.affineSpan_support_eq_top
  exact ⟨inferInstance,hLC.whitenedMeasure,
    whitenedMeasure_isIsotropic hid (covarianceMatrix_posDef_of_memLp_full_support hid hfull)⟩

/-- A genuine positive-radius domain is constructed uniformly in all
nonnegative damping parameters. No covariance or whitening premise remains. -/
 theorem exists_local_actual_damped_whitening {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) :
    ∃ r : ℝ, 0 < r ∧ ∀ (z : Space n), ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      IsProbabilityMeasure (actualDampedTiltLaw μ z s) ∧
      (actualDampedTiltLaw μ z s).support = μ.support ∧
      (covarianceMatrix (actualDampedTiltLaw μ z s)).PosDef ∧
      admissibleMeasure (whitenedMeasure (actualDampedTiltLaw μ z s)) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨r,hr,h1D,h1D'⟩ := exists_common_local_exponential_domains hμ.logConcave
    (memLp_const (1 : ℝ))
  refine ⟨r,hr,?_⟩
  intro z hz s hs
  have hi := integrable_exp_actualDampedExponent h1D hz hs
  letI : IsProbabilityMeasure (actualDampedTiltLaw μ z s) := isProbabilityMeasure_tilted hi
  have hsupport := actualDampedTiltLaw_support_eq hi
  have hLC := actualDampedTiltLaw_logConcave hμ z hs
  have hid := logConcave_memLp_id hLC
  have hfull : affineSpan ℝ (actualDampedTiltLaw μ z s).support = ⊤ := by
    rw [hsupport]
    exact hμ.isotropic.affineSpan_support_eq_top
  exact ⟨inferInstance,hsupport,covarianceMatrix_posDef_of_memLp_full_support hid hfull,
    actualDampedTiltLaw_whitening_admissible hμ hs hi⟩

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.covarianceMatrix_posDef_of_memLp_full_support
#print axioms KLS.DeterministicBridgeNext.exists_local_actual_damped_whitening
