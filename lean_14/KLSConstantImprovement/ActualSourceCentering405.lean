import KLSConstantImprovement.ActualSourceDualEnergyBound405

/-! Actual centering at source minima for increasing-target exhaustion.
The potential value, gradient normalization, uniform C1,1 bound, partition
and transport normalization are consequences of the constructed source. -/
noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped Topology NNReal BigOperators
namespace KLSConstantImprovement.ActualSourceCentering405
open KLS ActualBoundedCanonicalSource ActualSourceDualEnergyBound405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

def actualSourceMinimum (d : SourceData μ) : Space n :=
  Classical.choose (exists_actual_source_normalization_dualEnergy_bound d)

theorem actualSourceMinimum_spec (d : SourceData μ) :
    ∀ x, d.potential (actualSourceMinimum d) ≤ d.potential x :=
  (Classical.choose_spec (exists_actual_source_normalization_dualEnergy_bound d)).1

def centeredSourcePotential (d : SourceData μ) : Space n → ℝ :=
  normalizeMomentPotentialAt d.potential (actualSourceMinimum d)

theorem gradient_normalizeAt (d : SourceData μ) (a : Space n) (x : Space n) :
    gradient (normalizeMomentPotentialAt d.potential a) x = gradient d.potential (x + a) := by
  have hd : HasFDerivAt (normalizeMomentPotentialAt d.potential a)
      (fderiv ℝ d.potential (x + a)) x := by
    have ht : HasFDerivAt (fun z : Space n => z + a) (ContinuousLinearMap.id ℝ (Space n)) x :=
      (hasFDerivAt_id x).add_const a
    have hf : HasFDerivAt d.potential (fderiv ℝ d.potential (x + a)) (x + a) :=
      (d.source_C1.differentiable (by norm_num) (x + a)).hasFDerivAt
    have h : HasFDerivAt (fun z : Space n => d.potential (z + a))
        ((fderiv ℝ d.potential (x + a)).comp (ContinuousLinearMap.id ℝ (Space n))) x :=
      hf.comp x ht
    change HasFDerivAt (fun z : Space n => d.potential (z + a) - d.potential a)
      (fderiv ℝ d.potential (x + a)) x
    simpa only [ContinuousLinearMap.comp_id] using h.sub_const (d.potential a)
  simp only [gradient, hd.fderiv]

theorem centeredSourcePotential_C1 (d : SourceData μ) : ContDiff ℝ 1 (centeredSourcePotential d) :=
  (d.source_C1.comp (contDiff_id.add contDiff_const)).sub contDiff_const

theorem centeredSourcePotential_convex (d : SourceData μ) :
    ConvexOn ℝ univ (centeredSourcePotential d) :=
  convexOn_normalizeMomentPotentialAt d.source_convex _

theorem centeredSourcePotential_nonnegative (d : SourceData μ) :
    ∀ x, 0 ≤ centeredSourcePotential d x :=
  normalizeMomentPotentialAt_nonneg (actualSourceMinimum_spec d)

theorem centeredSourcePotential_zero (d : SourceData μ) : centeredSourcePotential d 0 = 0 :=
  normalizeMomentPotentialAt_zero _ _

theorem centeredSourcePotential_gradient_zero (d : SourceData μ) :
    gradient (centeredSourcePotential d) 0 = 0 := by
  rw [centeredSourcePotential, gradient_normalizeAt, zero_add]
  have hmin : IsLocalMin d.potential (actualSourceMinimum d) :=
    Eventually.of_forall (actualSourceMinimum_spec d)
  simp only [gradient, hmin.fderiv_eq_zero, map_zero]

theorem centeredSourcePotential_gradient_lipschitz (d : SourceData μ) :
    LipschitzWith (⟨16 / d.targetConvexityConstant, div_nonneg (by norm_num) d.target_convexity_pos.le⟩ : ℝ≥0)
      (gradient (centeredSourcePotential d)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [centeredSourcePotential, gradient_normalizeAt, gradient_normalizeAt]
  simpa only [dist_add_right] using d.gradient_lipschitz.dist_le_mul
    (x + actualSourceMinimum d) (y + actualSourceMinimum d)

theorem centeredSourcePotential_dualEnergy (d : SourceData μ) :
    momentDualEnergy μ (centeredSourcePotential d) ≤ ENNReal.ofReal n :=
  actual_source_normalized_dualEnergy_le_dim d _ (actualSourceMinimum_spec d)

theorem actual_source_partition_eq_one (d : SourceData μ) : momentPartitionFunction d.potential = 1 := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have h : (∫ _ : Space n, (1 : ℝ) ∂potentialMeasure d.potential) = 1 := by simp
  rw [integral_potentialMeasure d.source_C1.continuous.measurable] at h
  simpa only [one_mul, momentPartitionFunction] using h

theorem centeredSourcePotential_normalized (d : SourceData μ) (x : Space n) :
    normalizedMomentPotential (centeredSourcePotential d) x =
      d.potential (x + actualSourceMinimum d) := by
  have hZ : momentPartitionFunction (centeredSourcePotential d) =
      Real.exp (d.potential (actualSourceMinimum d)) := by
    rw [centeredSourcePotential, momentPartitionFunction_normalizeAt, actual_source_partition_eq_one, mul_one]
  change centeredSourcePotential d x + Real.log (momentPartitionFunction (centeredSourcePotential d)) = _
  rw [hZ, Real.log_exp]
  change d.potential (x + actualSourceMinimum d) - d.potential (actualSourceMinimum d) +
    d.potential (actualSourceMinimum d) = _
  ring

end KLSConstantImprovement.ActualSourceCentering405
#print axioms KLSConstantImprovement.ActualSourceCentering405.gradient_normalizeAt
#print axioms KLSConstantImprovement.ActualSourceCentering405.centeredSourcePotential_gradient_zero
#print axioms KLSConstantImprovement.ActualSourceCentering405.centeredSourcePotential_gradient_lipschitz
#print axioms KLSConstantImprovement.ActualSourceCentering405.centeredSourcePotential_dualEnergy
#print axioms KLSConstantImprovement.ActualSourceCentering405.centeredSourcePotential_normalized
