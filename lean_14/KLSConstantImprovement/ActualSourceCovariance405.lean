import KLSConstantImprovement.ActualBoundedCanonicalSource
import KLS.QuadraticDamping
import KLS.LogConcavityMoments
import KLS.AffineWhitening
import KLS.WeightedClassicalLiouville

/-!
The actual canonical source is a full-dimensional log-concave probability
law, with finite covariance. Strict covariance positivity is derived from
its positive density on all of Euclidean space. Only the covariance-whitened
source is claimed to be isotropic.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix
open scoped ContDiff RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceCovariance405
open KLS ActualBoundedCanonicalSource
variable {n : ℕ} {μ : Measure (Space n)}

theorem memLp_id_of_logConcave [IsProbabilityMeasure μ]
    (hlc : measureLogConcave μ) : MemLp (fun x : Space n => x) 2 μ := by
  apply (hlc.memLp_two_norm_pow 1).mono' aestronglyMeasurable_id
  exact Filter.Eventually.of_forall fun x => by simp

/-- Positive full-space density rules out a constant nonzero linear
functional. No compact-support assertion is used. -/
theorem eq_zero_of_potential_ae_inner_eq_const {φ : Space n → ℝ}
    (hφ : Continuous φ) {u : Space n} {c : ℝ}
    (heq : (fun x : Space n => inner ℝ u x) =ᵐ[potentialMeasure φ] fun _ => c) :
    u = 0 := by
  have hfull : (fun x : Space n => inner ℝ u x) = fun _ => c :=
    MeasureTheory.Measure.eq_of_ae_eq
      ((volume_absolutelyContinuous_potentialMeasure hφ).ae_eq heq)
      (by fun_prop) continuous_const
  have hc : (0 : ℝ) = c := by
    simpa only [inner_zero_right] using congrFun hfull 0
  have hu : inner ℝ u u = 0 := by
    simpa only [← hc] using congrFun hfull u
  exact inner_self_eq_zero.mp hu

theorem covarianceMatrix_posDef_of_positive_density {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : Continuous φ)
    (hid : MemLp (fun x : Space n => x) 2 (potentialMeasure φ)) :
    (covarianceMatrix (potentialMeasure φ)).PosDef := by
  have hs : (covarianceBilin (potentialMeasure φ)).toBilinForm.IsSymm :=
    ⟨covarianceBilin_comm⟩
  change ((covarianceBilin (potentialMeasure φ)).toBilinForm.toMatrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).PosDef
  apply (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis _ hs).mp
  intro u hu
  change 0 < covarianceBilin (potentialMeasure φ) u u
  rw [covarianceBilin_self hid]
  apply lt_of_le_of_ne' (variance_nonneg _ _)
  intro hz
  have hinner : MemLp (fun x : Space n => inner ℝ u x) 2
      (potentialMeasure φ) := (innerSL ℝ u).comp_memLp' hid
  have hae := ae_eq_integral_of_variance_eq_zero hinner hz
  exact hu (eq_zero_of_potential_ae_inner_eq_const hφ hae)

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.source_logConcave
    (d : SourceData μ) : measureLogConcave (potentialMeasure d.potential) :=
  measureLogConcave_potentialMeasure d.source_C1.continuous.measurable d.source_convex

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.source_id_memLp
    (d : SourceData μ) :
    MemLp (fun x : Space n => x) 2 (potentialMeasure d.potential) := by
  letI := d.source_probability
  exact memLp_id_of_logConcave d.source_logConcave

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.source_covariance_posDef
    (d : SourceData μ) : (covarianceMatrix (potentialMeasure d.potential)).PosDef := by
  letI := d.source_probability
  exact covarianceMatrix_posDef_of_positive_density d.source_C1.continuous d.source_id_memLp

/-- This is the admissible law to which the retained universal Poincare
theorem applies; the original canonical source has not been called isotropic. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.whitened_source_admissible
    (d : SourceData μ) : admissibleMeasure (whitenedMeasure (potentialMeasure d.potential)) := by
  letI := d.source_probability
  exact ⟨inferInstance, d.source_logConcave.whitenedMeasure,
    whitenedMeasure_isIsotropic d.source_id_memLp d.source_covariance_posDef⟩

end KLSConstantImprovement.ActualSourceCovariance405

#print axioms KLSConstantImprovement.ActualSourceCovariance405.eq_zero_of_potential_ae_inner_eq_const
#print axioms KLSConstantImprovement.ActualSourceCovariance405.covarianceMatrix_posDef_of_positive_density
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.source_id_memLp
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.whitened_source_admissible
