import KLSConstantImprovement.ActualKatoJointPointwise405
import KLSConstantImprovement.ActualDualBumpDerivative405

/-! Removing the actual common dual cutoff costs only a locally L1
product of the paid metric regularized mass flux and the genuine dual
cutoff derivative. The error vanishes by dominated convergence. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualKatoCutoffError405
open KLS ActualBoundedCanonicalSource ActualNaturalDualJoint405 ActualDualBumpControl405
open ActualDualBumpDerivative405 ActualKatoJointPointwise405 ActualKatoNonlinearDomains405
open ActualSourceNaturalGaffney405 ActualSourceNaturalHessian405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_dual_bump_integral_tendsto (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hm : ∀ k, AEStronglyMeasurable (dualSource d g (dualBump k)) (potentialMeasure d.potential))
    {f : Space n → ℝ} (hf : Integrable f (potentialMeasure d.potential)) :
    (∀ k, Integrable (fun x => dualSource d g (dualBump k) x * f x) (potentialMeasure d.potential)) ∧
      Tendsto (fun k => ∫ x, dualSource d g (dualBump k) x * f x ∂potentialMeasure d.potential)
        atTop (𝓝 (∫ x, f x ∂potentialMeasure d.potential)) := by
  have hb (k : ℕ) (x : Space n) : ‖dualSource d g (dualBump k) x * f x‖ ≤ ‖f x‖ := by
    rw [norm_mul]
    change ‖dualBump k (fun a => dualValue d g a x)‖ * ‖f x‖ ≤ _
    rw [Real.norm_of_nonneg (dualBump_nonnegative_le_one k _).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (dualBump_nonnegative_le_one k _).2
  have hme (k : ℕ) := (hm k).mul hf.aestronglyMeasurable
  refine ⟨fun k => hf.norm.mono' (hme k) (Eventually.of_forall (hb k)), ?_⟩
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖) hme hf.norm
    (fun k => Eventually.of_forall (hb k))
  exact Eventually.of_forall fun x => by
    apply tendsto_const_nhds.congr'
    filter_upwards [dualBump_eventually_one_nhds (fun a => dualValue d g a x)] with k hk
    change f x = dualBump k _ * f x
    rw [hk.eq_of_nhds, one_mul]

theorem actual_Kato_bump_error_tendsto_zero (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    (hC : ∀ i a E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i a) 2 (volume.restrict E))
    {ε : ℝ}
    (hFlux : ∀ a E, IsCompact E → MemLp (naturalKatoMetricFlux d g Du ε a) 2 (volume.restrict E))
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∀ k, Integrable (naturalKatoBumpError d g Du ε k ψ) (potentialMeasure d.potential)) ∧
      Tendsto (fun k => ∫ x, naturalKatoBumpError d g Du ε k ψ x ∂potentialMeasure d.potential)
        atTop (𝓝 0) := by
  obtain ⟨L, hL⟩ := dualBump_uniform_lipschitz (n := n)
  let R (x : Space n) := ∑ a : Fin n, ‖naturalKatoMetricFlux d g Du ε a x‖ *
    ((L : ℝ) * dualDerivativeNormSum d g Du a x)
  have hR : LocallyIntegrable R volume := by
    apply locallyIntegrable_iff.mpr
    intro E hE
    apply integrable_finsetSum Finset.univ
    intro a _
    exact (hFlux a E hE).norm.integrable_mul
      ((dualDerivativeNormSum_local_L2 d g Du hDu hC a E hE).const_mul (L : ℝ))
  have hDom : Integrable (fun x => ‖ψ x‖ * R x) (potentialMeasure d.potential) := by
    have he := integrable_raw_mul_compact_potential d.source_C1.continuous hR hψ.continuous.norm hc.norm
    exact he.congr (Eventually.of_forall fun x => mul_comm _ _)
  have hDb (k : ℕ) := actual_dual_compact_chain d g Du hu hDu hw hC
    (dualBump_contDiff k) (dualBump_compact k)
  have hEi (k : ℕ) : Integrable (naturalKatoBumpError d g Du ε k ψ) (potentialMeasure d.potential) := by
    have hloc : LocallyIntegrable (fun x => ∑ a : Fin n, naturalKatoMetricFlux d g Du ε a x *
        dualSourceDerivative d g Du (dualBump k) a x) volume := by
      apply locallyIntegrable_iff.mpr
      intro E hE
      exact integrable_finsetSum Finset.univ fun a _ =>
        (hFlux a E hE).integrable_mul ((hDb k).2.2.1 a E hE)
    have he := integrable_raw_mul_compact_potential d.source_C1.continuous hloc hψ.continuous hc
    exact he.congr (Eventually.of_forall fun x => mul_comm _ _)
  have hbound (k : ℕ) (x : Space n) : ‖naturalKatoBumpError d g Du ε k ψ x‖ ≤ ‖ψ x‖ * R x := by
    unfold naturalKatoBumpError
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      _ ≤ ∑ a : Fin n, ‖naturalKatoMetricFlux d g Du ε a x *
          dualSourceDerivative d g Du (dualBump k) a x‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun a _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (dualBump_directional_bound hL k _ _) (norm_nonneg _)
  refine ⟨hEi, ?_⟩
  have hlim : ∀ᵐ x ∂potentialMeasure d.potential, Tendsto
      (fun k => naturalKatoBumpError d g Du ε k ψ x) atTop (𝓝 (0 : ℝ)) :=
    Eventually.of_forall fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [actual_dual_bump_eventually d g Du x] with k hk
      simp only [naturalKatoBumpError, hk.2, mul_zero, Finset.sum_const_zero]
  have ht := tendsto_integral_of_dominated_convergence (fun x => ‖ψ x‖ * R x)
    (fun k => (hEi k).aestronglyMeasurable) hDom
    (fun k => Eventually.of_forall (hbound k)) hlim
  simpa only [integral_zero] using ht

end KLSConstantImprovement.ActualKatoCutoffError405
#print axioms KLSConstantImprovement.ActualKatoCutoffError405.actual_dual_bump_integral_tendsto
#print axioms KLSConstantImprovement.ActualKatoCutoffError405.actual_Kato_bump_error_tendsto_zero
