import KLSConstantImprovement.ActualSourceCurvatureDomains405

/-! Every actual curvature entry has the actual Hessian mean. The full
matrix mean identity is obtained by conservative weak cutoff passage;
it is not inferred from the diagonal trace identity. -/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceCurvatureMean405
open KLS ActualBoundedCanonicalSource ActualSourceHessianEvolution405
open ActualSourceGlobalCurvature405 ActualSourceCurvatureDomains405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_connection_curvature_entry_mean (d : SourceData μ) (i j : Fin n) :
    Integrable (fun x => sourceConnectionCurvature d x i j) (potentialMeasure d.potential) ∧
      (∫ x, sourceConnectionCurvature d x i j ∂potentialMeasure d.potential) =
        ∫ x, coordinateHessian d.potential x i j ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let S : Space n → ℝ := fun x => coordinateHessian d.potential x i j
  let G : Space n → ℝ := fun x => sourceConnectionCurvature d x i j
  let F : Fin n → Space n → ℝ := fun a x => d.third x a i j
  have hStop : MemLp S ∞ (volume : Measure (Space n)) :=
    memLp_coordinateHessian_top_of_gradient_lipschitz d.gradient_lipschitz volume i j
  have hSi : Integrable S (potentialMeasure d.potential) :=
    (d.hessian_entry_memLp i j 1).integrable le_rfl
  have hSloc (E : Set (Space n)) (hE : IsCompact E) :
      MemLp S 2 (volume.restrict E) := by
    letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
    exact (hStop.restrict E).mono_exponent (by simp)
  obtain ⟨x₀, _, hc, _, _, hpoint, htransfer⟩ :=
    weak_moment_exists_cutoffs_with_H1_flux_errors
      d.source_lipschitz d.source_convex (d.target_smooth.of_le (by simp))
      d.target_convex_potential d.target_convexity_pos d.target_strong
      d.target_closed d.target_convex (d.pushforward.trans d.target_representation)
  let χ : ℕ → Space n → ℝ := hessianMetricCutoffSequence d.potential x₀
  have hf := htransfer S F hSloc (lpNorm S ∞ volume) (ae_le_lpNorm_exponent_top hStop)
    (fun a E hE => d.third_local_L2 a i j E hE)
    (fun a => d.third_weak_derivative a i j)
  let error : ℕ → ℝ := fun k => -(∫ x, ∑ a, ∑ b,
    (coordinateHessian d.potential x)⁻¹ a b * F a x * coordinateDerivative (χ k) b x
      ∂potentialMeasure d.potential)
  have herror : Tendsto error atTop (𝓝 0) := by
    simpa only [error, neg_zero] using hf.2.neg
  have hχm (k : ℕ) : AEStronglyMeasurable (χ k) (potentialMeasure d.potential) :=
    (hc k).1.continuous.aestronglyMeasurable
  have hχnorm (k : ℕ) : ∀ᵐ x ∂potentialMeasure d.potential, ‖χ k x‖ ≤ 1 :=
    Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((hc k).2.2 x).1]
      exact ((hc k).2.2 x).2
  have hχSi (k : ℕ) : Integrable (fun x => χ k x * S x) (potentialMeasure d.potential) :=
    hSi.bdd_mul (hχm k) (hχnorm k)
  have he (k : ℕ) := actual_compact_hessian_evolution d (hc k).1 (hc k).2.1 i j
  have hχGi (k : ℕ) : Integrable (fun x => χ k x * G x) (potentialMeasure d.potential) := by
    apply ((he k).2.1.add (hχSi k)).congr
    exact Eventually.of_forall fun x => by
      change (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) * χ k x +
        χ k x * coordinateHessian d.potential x i j = χ k x * sourceConnectionCurvature d x i j
      ring
  have hbalance (k : ℕ) : (∫ x, χ k x * G x ∂potentialMeasure d.potential) =
      (∫ x, χ k x * S x ∂potentialMeasure d.potential) + error k := by
    have hac : potentialMeasure d.potential ≪ volume := withDensity_absolutelyContinuous _ _
    have hl : (∑ a, ∫ x, ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
        coordinateDerivative (χ k) a x ∂potentialMeasure d.potential) =
        ∫ x, ∑ a, ∑ b, (coordinateHessian d.potential x)⁻¹ a b * F a x *
          coordinateDerivative (χ k) b x ∂potentialMeasure d.potential := by
      rw [← integral_finsetSum _ (fun a _ => (he k).1 a)]
      apply integral_congr_ae
      filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le] with x hx hN
      exact actual_hessian_flux_contraction _ hx.1.posSemidef.inv.isHermitian.isSymm
        (sourceThirdMatrix d x) (fun k a b => (hN k a b).1)
        (fun a => coordinateDerivative (χ k) a x) i j
    have hr : (∫ x, (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
        χ k x ∂potentialMeasure d.potential) =
        (∫ x, χ k x * G x ∂potentialMeasure d.potential) -
          ∫ x, χ k x * S x ∂potentialMeasure d.potential := by
      rw [← integral_sub (hχGi k) (hχSi k)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [S, G]; ring
    have h := (he k).2.2
    rw [hl, hr] at h
    dsimp only [error]
    linarith
  have hGi : Integrable G (potentialMeasure d.potential) :=
    actual_connection_curvature_entry_integrable d i j
  have hSlim := (integral_mul_tendsto_of_ae_bounded_cutoffs hSi hχm hχnorm
    (Eventually.of_forall hpoint)).2
  have hGlim := (integral_mul_tendsto_of_ae_bounded_cutoffs hGi hχm hχnorm
    (Eventually.of_forall hpoint)).2
  have hlim : Tendsto (fun k => ∫ x, χ k x * G x ∂potentialMeasure d.potential)
      atTop (𝓝 (∫ x, S x ∂potentialMeasure d.potential)) := by
    simp_rw [hbalance]
    simpa only [add_zero] using hSlim.add herror
  exact ⟨hGi, tendsto_nhds_unique hGlim hlim⟩

theorem actual_connection_curvature_mean_eq_one (d : SourceData μ) (hiso : IsIsotropic μ)
    (i j : Fin n) :
    (∫ x, sourceConnectionCurvature d x i j ∂potentialMeasure d.potential) =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  rw [(actual_connection_curvature_entry_mean d i j).2]
  exact integral_actual_hessian_entry_eq_one_C11
    d.source_C1 d.gradient_lipschitz (d.pushforward.symm ▸ hiso) i j

end KLSConstantImprovement.ActualSourceCurvatureMean405
#print axioms KLSConstantImprovement.ActualSourceCurvatureMean405.actual_connection_curvature_entry_mean
#print axioms KLSConstantImprovement.ActualSourceCurvatureMean405.actual_connection_curvature_mean_eq_one
