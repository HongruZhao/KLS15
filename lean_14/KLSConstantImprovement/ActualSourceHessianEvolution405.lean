import KLSConstantImprovement.ActualBoundedSourceCalculus
import KLS.WeakMomentHessianEvolution

/-! The actual weak matrix evolution and positive curvature field on the
constructed C1,1 source. No classical Hessian derivative or matrix PDE
realization is supplied. Compact test domains are discharged explicitly.
-/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceHessianEvolution405
open KLS ActualBoundedCanonicalSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def sourceThirdMatrix (d : SourceData μ) (x : Space n) (k : Fin n) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.of (d.third x k)

def sourceConnectionCurvature (d : SourceData μ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  coordinateHessian d.potential x *
      coordinateHessian d.targetPotential (gradient d.potential x) *
        coordinateHessian d.potential x +
    matrixTraceGram (coordinateHessian d.potential x)⁻¹ (sourceThirdMatrix d x)

theorem actual_source_connection_curvature_positive (d : SourceData μ) :
    ∀ᵐ x ∂potentialMeasure d.potential, (sourceConnectionCurvature d x).PosSemidef := by
  have hac : potentialMeasure d.potential ≪ volume := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le] with x hx hN
  have hV := coordinateHessian_posSemidef_of_convex
    (d.target_smooth.of_le (by simp)) d.target_convex_potential (gradient d.potential x)
  have hP : (coordinateHessian d.potential x *
      coordinateHessian d.targetPotential (gradient d.potential x) *
        coordinateHessian d.potential x).PosSemidef := by
    simpa only [hx.1.isHermitian.eq] using
      hV.conjTranspose_mul_mul_same (coordinateHessian d.potential x)
  have hG := matrixTraceGram_posSemidef hx.1.posSemidef.inv
    (sourceThirdMatrix d x) (fun k => Matrix.IsSymm.ext (fun i j => (hN k j i).2))
  exact hP.add hG

theorem actual_compact_hessian_evolution (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (k l : Fin n) :
    (∀ a, Integrable (fun x => ((coordinateHessian d.potential x)⁻¹ *
      sourceThirdMatrix d x k) a l * coordinateDerivative ψ a x)
        (potentialMeasure d.potential)) ∧
    Integrable (fun x => (-coordinateHessian d.potential x k l +
      sourceConnectionCurvature d x k l) * ψ x) (potentialMeasure d.potential) ∧
    -(∑ a, ∫ x, ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x k) a l *
      coordinateDerivative ψ a x ∂potentialMeasure d.potential) =
      ∫ x, (-coordinateHessian d.potential x k l + sourceConnectionCurvature d x k l) *
        ψ x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hψl (E : Set (Space n)) (hE : IsCompact E) :
      MemLp ψ 2 (volume.restrict E) := by
    letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
    exact (memLp_top_restrict_compact_of_continuous hψ.continuous hE).mono_exponent
      (by simp)
  have hDl (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (coordinateDerivative ψ a) 2 (volume.restrict E) := by
    letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
    exact (memLp_top_restrict_compact_of_continuous
      (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) a).continuous hE).mono_exponent
        (by simp)
  obtain ⟨C, hb⟩ := hψ.continuous.bounded_above_of_compact_support hc
  have he := weak_moment_hessian_evolution_bounded_H1
    d.source_lipschitz d.source_convex (d.target_smooth.of_le (by simp))
    d.target_convex_potential d.target_convexity_pos d.target_strong
    d.target_closed d.target_convex (d.pushforward.trans d.target_representation)
    (T := sourceThirdMatrix d) d.third_local_L2 d.third_weak_derivative
    hψl hc (Eventually.of_forall hb) hDl
    (fun a => hasLocalWeakCoordinateDerivative_of_contDiff hψ a) k l
  simpa only [sourceConnectionCurvature, matrixTraceGram, Matrix.add_apply,
    add_assoc] using he

end KLSConstantImprovement.ActualSourceHessianEvolution405
#print axioms KLSConstantImprovement.ActualSourceHessianEvolution405.actual_source_connection_curvature_positive
#print axioms KLSConstantImprovement.ActualSourceHessianEvolution405.actual_compact_hessian_evolution
