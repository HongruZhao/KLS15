import KLSConstantImprovement.ActualBoundedCanonicalSource
import KLS.RawMomentMapStein
import KLS.WeakMomentTraceSquareBound
import KLSConstantImprovement.ActualCubicGradientEnergy

/-!
Actual global calculus on the constructed bounded-target source.

Every source used below comes from `exists_sourceData`, rather than a supplied
analytic realization. Boundedness of the actual gradient range discharges all
Lp domains of continuous target observables and all first-order chain-rule
terms. The global Stein identity applies to arbitrary C1 target functions,
including every literal polynomial; it has no compact-support premise.
The source remains C1,1 and its third tensor remains a weak derivative.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators ContDiff Topology NNReal ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualBoundedCanonicalSource
open KLS ActualBoundedCanonicalSource
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem SourceData.gradient_measurePreserving {μ : Measure (Space n)}
    (d : SourceData μ) :
    MeasurePreserving (gradient d.potential) (potentialMeasure d.potential) μ :=
  ⟨d.gradient_lipschitz.continuous.measurable, d.pushforward⟩

theorem SourceData.integral_comp_gradient {μ : Measure (Space n)}
    (d : SourceData μ) {f : Space n → ℝ} (hf : Continuous f) :
    (∫ x, f (gradient d.potential x) ∂potentialMeasure d.potential) =
      ∫ y, f y ∂μ := by
  calc
    (∫ x, f (gradient d.potential x) ∂potentialMeasure d.potential) =
        ∫ y, f y ∂MomentMap.gradientPushforward d.potential :=
      (integral_map (measurable_gradient _).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂μ :=
      congrArg (fun ρ : Measure (Space n) => ∫ y, f y ∂ρ) d.pushforward

theorem SourceData.variance_comp_gradient {μ : Measure (Space n)}
    (d : SourceData μ) {f : Space n → ℝ} (hf : Continuous f) :
    variance (fun x => f (gradient d.potential x)) (potentialMeasure d.potential) =
      variance f μ := by
  exact d.gradient_measurePreserving.variance_fun_comp hf.measurable.aemeasurable

/-- A target observable is bounded on the actual source gradient range.
There is no polynomial-growth premise, and the bound may depend on f. -/
theorem SourceData.exists_bound_continuous_comp_gradient
    {μ : Measure (Space n)} (d : SourceData μ)
    {f : Space n → ℝ} (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f (gradient d.potential x)‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    d.gradient_range_bounded.isCompact_closure.bddAbove_image hf.norm.continuousOn
  have hb (x : Space n) : ‖f (gradient d.potential x)‖ ≤ C :=
    hC ⟨gradient d.potential x, subset_closure ⟨x, rfl⟩, rfl⟩
  exact ⟨C, (norm_nonneg _).trans (hb 0), hb⟩

/-- In particular every literal polynomial of the actual target variable
belongs to every source Lp space, including L-infinity. -/
theorem SourceData.continuous_comp_gradient_memLp
    {μ : Measure (Space n)} (d : SourceData μ)
    {f : Space n → ℝ} (hf : Continuous f) (p : ℝ≥0∞) :
    MemLp (fun x => f (gradient d.potential x)) p (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨C, _, hb⟩ := d.exists_bound_continuous_comp_gradient hf
  exact MemLp.of_bound (hf.comp d.gradient_lipschitz.continuous).aestronglyMeasurable
    C (Eventually.of_forall hb)

theorem SourceData.hessian_entry_memLp {μ : Measure (Space n)}
    (d : SourceData μ) (i j : Fin n) (p : ℝ≥0∞) :
    MemLp (fun x => coordinateHessian d.potential x i j) p
      (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  exact memLp_actual_hessian_entry_of_global_gradient_lipschitz
    d.gradient_lipschitz i j p

/-- The literal first-order source derivative of a C1 target pullback.
This is a weak chain rule on the actual C1,1 source. -/
theorem SourceData.pullback_hasLocalWeakCoordinateDerivative
    {μ : Measure (Space n)} (d : SourceData μ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin n) :
    HasLocalWeakCoordinateDerivative
      (fun x => f (gradient d.potential x))
      (fun x => inner ℝ (gradient f (gradient d.potential x))
        (matrixAction (coordinateHessian d.potential x) (EuclideanSpace.single i 1))) i := by
  simpa only [matrixAction_one_apply] using
    MomentMap.raw_linear_gradient_test_weak_derivative
      d.source_C1 d.gradient_lipschitz hf (1 : Matrix (Fin n) (Fin n) ℝ) i

/-- All chain-rule terms are globally Lp, without a source C2 assumption.
The actual bounded Hessian and bounded target gradient pay the domain. -/
theorem SourceData.pullback_weak_derivative_memLp
    {μ : Measure (Space n)} (d : SourceData μ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin n) (p : ℝ≥0∞) :
    MemLp
      (fun x => inner ℝ (gradient f (gradient d.potential x))
        (matrixAction (coordinateHessian d.potential x) (EuclideanSpace.single i 1)))
      p (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hgc : Continuous (gradient f) := continuous_gradient_of_contDiff hf
  obtain ⟨C, _, hb⟩ := d.exists_bound_continuous_comp_gradient hgc.norm
  have hh := MomentMap.memLp_matrixAction_actualHessian
    (μ := potentialMeasure d.potential) d.gradient_lipschitz (EuclideanSpace.single i 1) p
  apply (hh.norm.const_mul C).mono'
    ((hgc.comp d.gradient_lipschitz.continuous).aestronglyMeasurable.inner
      hh.aestronglyMeasurable)
  exact Eventually.of_forall fun x =>
    (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (by simpa using hb x) (norm_nonneg _))

/-- Actual global target Stein identity. The same source transports the law,
and the actual weak derivative domains are discharged before IBP. -/
theorem SourceData.integral_target_coordinate_mul_eq_hessian_pair
    {μ : Measure (Space n)} (d : SourceData μ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin n) :
    (∫ y, f y * y i ∂μ) =
      ∫ x, inner ℝ (gradient f (gradient d.potential x))
        (matrixAction (coordinateHessian d.potential x) (EuclideanSpace.single i 1))
          ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hF2 := d.continuous_comp_gradient_memLp hf.continuous 2
  have hX2 := d.continuous_comp_gradient_memLp (EuclideanSpace.proj i).continuous 2
  have hRi := (d.pullback_weak_derivative_memLp hf i 2).integrable (by norm_num)
  have hfd : Integrable
      (fun x => f (gradient d.potential x) * coordinateDerivative d.potential i x)
      (potentialMeasure d.potential) := by
    have hm := hF2.integrable_mul hX2
    change Integrable (fun x => f (gradient d.potential x) * gradient d.potential x i)
      (potentialMeasure d.potential) at hm
    simpa only [coordinateDerivative_eq_gradient] using hm
  have hmean := integral_raw_derivative_potential d.source_C1
    (d.pullback_hasLocalWeakCoordinateDerivative hf i)
    (hF2.integrable (by norm_num)) hRi hfd
  calc
    (∫ y, f y * y i ∂μ) =
        ∫ x, f (gradient d.potential x) * gradient d.potential x i
          ∂potentialMeasure d.potential :=
      (d.integral_comp_gradient (hf.continuous.mul (EuclideanSpace.proj i).continuous)).symm
    _ = ∫ x, inner ℝ (gradient f (gradient d.potential x))
        (matrixAction (coordinateHessian d.potential x) (EuclideanSpace.single i 1))
          ∂potentialMeasure d.potential := by
      simpa only [coordinateDerivative_eq_gradient] using hmean.symm

/-- The stored actual weak third tensor has the full global energy identity;
no energy/production premise is added to SourceData. -/
theorem SourceData.global_trace_energy {μ : Measure (Space n)}
    (d : SourceData μ) {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
    Integrable (fun x => rawHessianTraceSquare (coordinateHessian d.potential x) B)
      (potentialMeasure d.potential) ∧
    Integrable (fun x => rawHessianTraceGradientTerm
      (coordinateHessian d.potential x) B (d.third x)) (potentialMeasure d.potential) ∧
    Integrable (fun x => rawHessianTraceTargetTerm
      (coordinateHessian d.potential x)
      (coordinateHessian d.targetPotential (gradient d.potential x)) B)
        (potentialMeasure d.potential) ∧
    Integrable (fun x => rawHessianTraceThirdTerm
      (coordinateHessian d.potential x) B (d.third x)) (potentialMeasure d.potential) ∧
    (∫ x, rawHessianTraceSquare (coordinateHessian d.potential x) B
        ∂potentialMeasure d.potential) =
      (∫ x, rawHessianTraceGradientTerm (coordinateHessian d.potential x) B (d.third x)
        ∂potentialMeasure d.potential) +
      (∫ x, rawHessianTraceTargetTerm (coordinateHessian d.potential x)
        (coordinateHessian d.targetPotential (gradient d.potential x)) B
        ∂potentialMeasure d.potential) +
      (∫ x, rawHessianTraceThirdTerm (coordinateHessian d.potential x) B (d.third x)
        ∂potentialMeasure d.potential) ∧
    (∫ x, rawHessianTraceGradientTerm (coordinateHessian d.potential x) B (d.third x)
        ∂potentialMeasure d.potential) ≤
      (1 / 2 : ℝ) * ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x) B
        ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  exact weak_moment_global_trace_energy d.source_lipschitz d.source_convex
    (d.target_smooth.of_le (by simp)) d.target_convex_potential
    d.target_convexity_pos d.target_strong d.target_closed d.target_convex
    (d.pushforward.trans d.target_representation)
    d.third_local_L2 d.third_weak_derivative hB

/-- Isotropy is used on the same actual pushforward to close the raw trace
square estimate, without supplying a Hessian mean or variance certificate. -/
theorem SourceData.integral_trace_square_le {μ : Measure (Space n)}
    (d : SourceData μ) (hiso : IsIsotropic μ)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
    (∫ x, rawHessianTraceSquare (coordinateHessian d.potential x) B
      ∂potentialMeasure d.potential) ≤ 2 * (B * B).trace := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  exact (weak_moment_trace_square_le_twice_trace
    d.source_lipschitz d.source_convex (d.target_smooth.of_le (by simp))
    d.target_convex_potential d.target_convexity_pos d.target_strong
    d.target_closed d.target_convex (d.pushforward.trans d.target_representation)
    (d.pushforward.symm ▸ hiso) hB).2

end KLSConstantImprovement.ActualBoundedCanonicalSource

#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.gradient_measurePreserving
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.integral_comp_gradient
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.variance_comp_gradient
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.exists_bound_continuous_comp_gradient
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.continuous_comp_gradient_memLp
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.hessian_entry_memLp
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.pullback_hasLocalWeakCoordinateDerivative
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.pullback_weak_derivative_memLp
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.integral_target_coordinate_mul_eq_hessian_pair
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.global_trace_energy
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.integral_trace_square_le
