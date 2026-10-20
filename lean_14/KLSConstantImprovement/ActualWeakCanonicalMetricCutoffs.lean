import KLSConstantImprovement.ActualBoundedCanonicalSource
import KLS.LocalC11FirstFactor
import KLS.WeakMomentSublevelSequence

/-!
Conservative metric-energy cutoffs for the actual constructed C1,1 source.
The first-factor IBP uses genuine weak inverse-Hessian divergence, then the
accepted potential-sublevel cutoffs give vanishing metric energy. No C4
source, compact strong-operator core, or source boundary assertion is used.
-/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators ContDiff Topology NNReal ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualWeakCanonicalMetricCutoffs
open KLS ActualBoundedCanonicalSource
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

/-- Actual compact first-factor IBP at local C1,1 regularity of the second
factor. The density-weighted coefficients, their local integrability, and
their divergence all come from the constructed canonical source. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.compact_metric_first_factor {μ : Measure (Space n)} (d : SourceData μ)
    {f η : Space n → ℝ} (hDf : ∀ j, LocallyLipschitz (coordinateDerivative f j))
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    Integrable (fun x => η x * hessianMetricDiffusion d.potential d.targetPotential f x)
      (potentialMeasure d.potential) ∧
    Integrable (fun x => ∑ i, ∑ j, (coordinateHessian d.potential x)⁻¹ i j *
      coordinateDerivative η i x * coordinateDerivative f j x) (potentialMeasure d.potential) ∧
    (∫ x, η x * hessianMetricDiffusion d.potential d.targetPotential f x
      ∂potentialMeasure d.potential) =
      -(∫ x, ∑ i, ∑ j, (coordinateHessian d.potential x)⁻¹ i j *
        coordinateDerivative η i x * coordinateDerivative f j x ∂potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hV1 : ContDiff ℝ 1 d.targetPotential := d.target_smooth.of_le (by simp)
  let A : Space n → Matrix (Fin n) (Fin n) ℝ := fun x =>
    Real.exp (-d.potential x) • (coordinateHessian d.potential x)⁻¹
  let b : Fin n → Space n → ℝ := fun j x =>
    Real.exp (-d.potential x) * coordinateDerivative d.targetPotential j (gradient d.potential x)
  have hAe : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x).PosDef ∧
        (coordinateHessian d.potential x).det =
          Real.exp (-d.potential x + d.targetPotential (gradient d.potential x)) :=
    d.hessian_ae.mono fun _ hx => ⟨hx.1, hx.2.1⟩
  have hA (i j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => A x i j) 2 (volume.restrict E) :=
    memLp_weighted_inverseHessian_on_compact_of_ae_equation d.source_lipschitz
      d.gradient_lipschitz d.target_smooth.continuous hAe hE i j
  have hb (j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (b j) 2 (volume.restrict E) :=
    memLp_continuous_on_compact
      ((Real.continuous_exp.comp d.source_C1.continuous.neg).mul
        (((contDiff_coordinateDerivative hV1
          (m := 0) (by norm_num) j).continuous).comp d.gradient_lipschitz.continuous)) hE
  have hdiv (j : Fin n) (ψ : Space n → ℝ) (hψ : LocallyLipschitz ψ)
      (hψc : HasCompactSupport ψ) :
      (∑ i, ∫ x, A x i j * coordinateDerivative ψ i x) = ∫ x, b j x * ψ x :=
    weak_moment_inverseHessian_integral_column_locallyLipschitz_volume
      d.source_lipschitz d.source_convex hV1
      d.target_convex_potential d.target_convexity_pos d.target_strong
      d.target_closed d.target_convex (d.pushforward.trans d.target_representation) hψ hψc j
  obtain ⟨hleft, hright, heq⟩ :=
    integral_weakEllipticExpression_localC11_compact_first_factor hA hb hdiv hDf hη hc
  have hop (g : Space n → ℝ) (x : Space n) : weakEllipticExpression A b g x =
      Real.exp (-d.potential x) * hessianMetricDiffusion d.potential d.targetPotential g x :=
    weakEllipticExpression_weighted_inverseHessian d.potential d.targetPotential g x
  refine ⟨(integrable_potentialMeasure_iff d.source_C1.continuous.measurable).mpr ?_,
    (integrable_potentialMeasure_iff d.source_C1.continuous.measurable).mpr ?_, ?_⟩
  · simpa only [hop, mul_comm, mul_left_comm, mul_assoc] using hleft
  · simpa only [A, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_comm, mul_left_comm, mul_assoc] using hright
  · simpa only [integral_potentialMeasure d.source_C1.continuous.measurable, hop, A,
      Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using heq

/-- The actual weak source has compact C1 conservative cutoffs tending to
one whose inverse-Hessian gradient energy tends to zero. Their integrable
diffusion error is also retained. This is a form-domain cutoff statement;
no compact strong-operator graph core is claimed. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.exists_metric_energy_cutoffs {μ : Measure (Space n)} (d : SourceData μ) :
    ∃ x₀ : Space n, (∀ x, d.potential x₀ ≤ d.potential x) ∧
      (∀ k, ContDiff ℝ 1 (hessianMetricCutoffSequence d.potential x₀ k) ∧
        HasCompactSupport (hessianMetricCutoffSequence d.potential x₀ k) ∧
        ∀ x, hessianMetricCutoffSequence d.potential x₀ k x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, Monotone (fun k => hessianMetricCutoffSequence d.potential x₀ k x)) ∧
      (∀ x, Tendsto (fun k => hessianMetricCutoffSequence d.potential x₀ k x) atTop (𝓝 1)) ∧
      (∀ k, Integrable (hessianMetricDiffusion d.potential d.targetPotential
        (hessianMetricCutoffSequence d.potential x₀ k)) (potentialMeasure d.potential)) ∧
      Tendsto (fun k => ∫ x, ‖hessianMetricDiffusion d.potential d.targetPotential
        (hessianMetricCutoffSequence d.potential x₀ k) x‖ ∂potentialMeasure d.potential)
        atTop (𝓝 0) ∧
      (∀ k, Integrable (inverseHessianGradientForm d.potential
        (hessianMetricCutoffSequence d.potential x₀ k)) (potentialMeasure d.potential)) ∧
      Tendsto (fun k => ∫ x, inverseHessianGradientForm d.potential
        (hessianMetricCutoffSequence d.potential x₀ k) x ∂potentialMeasure d.potential)
        atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨x₀, hmin, hc, hmono, hlim, hLi, hLlim⟩ :=
    weak_moment_exists_hessianMetricCutoffSequence d.source_lipschitz d.source_convex
      (d.target_smooth.of_le (by simp)) d.target_convex_potential d.target_convexity_pos
      d.target_strong d.target_closed d.target_convex
      (d.pushforward.trans d.target_representation)
  let χ : ℕ → Space n → ℝ := hessianMetricCutoffSequence d.potential x₀
  have hD (k : ℕ) (i : Fin n) : LocallyLipschitz (coordinateDerivative (χ k) i) :=
    coordinateDerivative_potentialSublevelCutoff_locallyLipschitz
      d.source_C1 d.gradient_lipschitz x₀ (cutoffScale k) i
  have hIBP (k : ℕ) := d.compact_metric_first_factor (hD k) (hc k).1 (hc k).2.1
  have hE (k : ℕ) : Integrable (inverseHessianGradientForm d.potential (χ k))
      (potentialMeasure d.potential) := (hIBP k).2.1
  have hzero (k : ℕ) : 0 ≤ ∫ x, inverseHessianGradientForm d.potential (χ k) x
      ∂potentialMeasure d.potential :=
    integral_nonneg_of_ae (d.hessian_ae_source.mono fun x hx =>
      inverseHessianGradientForm_nonneg_at (χ k) hx.1)
  have hbound (k : ℕ) : (∫ x, inverseHessianGradientForm d.potential (χ k) x
      ∂potentialMeasure d.potential) ≤
      ∫ x, ‖hessianMetricDiffusion d.potential d.targetPotential (χ k) x‖
        ∂potentialMeasure d.potential := by
    have hi := integral_mono_ae (hIBP k).1.neg (hLi k).norm
      (Eventually.of_forall fun x => show -(χ k x *
        hessianMetricDiffusion d.potential d.targetPotential (χ k) x) ≤
        ‖hessianMetricDiffusion d.potential d.targetPotential (χ k) x‖ from by
        have hχ : |χ k x| ≤ 1 := by
          rw [abs_of_nonneg ((hc k).2.2 x).1]
          exact ((hc k).2.2 x).2
        calc
          _ ≤ |χ k x * hessianMetricDiffusion d.potential d.targetPotential (χ k) x| := neg_le_abs _
          _ = |χ k x| * ‖hessianMetricDiffusion d.potential d.targetPotential (χ k) x‖ := by
            rw [abs_mul, Real.norm_eq_abs]
          _ ≤ 1 * ‖hessianMetricDiffusion d.potential d.targetPotential (χ k) x‖ :=
            mul_le_mul_of_nonneg_right hχ (norm_nonneg _)
          _ = _ := one_mul _)
    change (∫ x, -(χ k x * hessianMetricDiffusion d.potential d.targetPotential (χ k) x)
        ∂potentialMeasure d.potential) ≤
      ∫ x, ‖hessianMetricDiffusion d.potential d.targetPotential (χ k) x‖
        ∂potentialMeasure d.potential at hi
    have hIBPk : (∫ x, χ k x * hessianMetricDiffusion d.potential d.targetPotential (χ k) x
        ∂potentialMeasure d.potential) =
      -(∫ x, inverseHessianGradientForm d.potential (χ k) x ∂potentialMeasure d.potential) :=
      (hIBP k).2.2
    rw [integral_neg, hIBPk, neg_neg] at hi
    exact hi
  exact ⟨x₀, hmin, hc, hmono, hlim, hLi, hLlim, hE,
    squeeze_zero hzero hbound hLlim⟩

end KLSConstantImprovement.ActualWeakCanonicalMetricCutoffs
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.compact_metric_first_factor
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.exists_metric_energy_cutoffs
