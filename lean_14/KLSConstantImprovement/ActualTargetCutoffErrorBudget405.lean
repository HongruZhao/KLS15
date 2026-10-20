import KLSConstantImprovement.ActualGrowingTargetCutoffDomains405
import KLSConstantImprovement.ActualSourceNaturalGaffney405
import KLSConstantImprovement.ActualSourceBoundedMassCutoffs405
import KLSConstantImprovement.ActualSourceCompactConnectionAbsorption405

/-! The actual natural mass pays target cutoff errors uniformly along
the soft-target family.  Only the unconditional Gaffney L1 bound is used;
there is no bounded-natural-mass premise. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualTargetCutoffErrorBudget405
open KLS ActualBoundedCanonicalSource ActualCompactTargetExtensions405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualSourceBoundedMassCutoffs405 ActualSourceCompactConnectionAbsorption405
open ActualTargetPullbackCutoffEnergy405 ActualSourcePullbackMetricGradient405
open ActualCenteredTargetForcing405 ActualCompactRawMetricGraph
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_natural_mass_integrable_and_bound
    (d : SourceData μ) (hn : 1 ≤ n) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) :
    Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g))
        (potentialMeasure d.potential) ∧
      (∫ x, sourceVectorMass d.potential (naturalCanonicalFlux d g) x
        ∂potentialMeasure d.potential) ≤ ‖g‖^2 := by
  obtain ⟨Du, _hu, _hDu, _hw, hcomp, hMi, hQi, hb, _hdiv⟩ :=
    exists_naturalCanonicalFlux_gaffney d hn g hg
  refine ⟨hMi, le_trans ?_ hb⟩
  apply integral_mono_ae hMi (hMi.add hQi)
  filter_upwards [sourceVectorJacobianEnergy_nonnegative_ae d Du hcomp] with x hx
  exact le_add_of_nonneg_right hx

theorem actual_natural_mass_pullback_cutoff_bound
    (d : SourceData μ) (hn : 1 ≤ n) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ)
    {c G : ℝ} (hc : 0 < c) (hκ : c ≤ d.targetConvexityConstant)
    (hG : 0 ≤ G) (hgrad : ∀ x, ‖gradient χ x‖ ≤ G) :
    Integrable (fun x => sourceVectorMass d.potential (naturalCanonicalFlux d g) x *
      pullbackMetricSquare d χ x) (potentialMeasure d.potential) ∧
      (∫ x, sourceVectorMass d.potential (naturalCanonicalFlux d g) x *
        pullbackMetricSquare d χ x ∂potentialMeasure d.potential) ≤ (16/c)*G^2*‖g‖^2 := by
  obtain ⟨hMi, hMb⟩ := actual_natural_mass_integrable_and_bound d hn g hg
  have hΓ : MemLp (pullbackMetricSquare d χ) ∞ (potentialMeasure d.potential) := by
    change MemLp (fun x => ∑ i : Fin n,
      rawCanonicalMetricDerivative d.potential (pullbackRawGradient d χ) i x ^ 2) ∞ _
    apply memLp_finsetSum Finset.univ
    intro i _
    have hi := pullback_raw_metric_gradient_memLp_top d hχ i
    have hh : MemLp (fun x =>
        rawCanonicalMetricDerivative d.potential (pullbackRawGradient d χ) i x *
        rawCanonicalMetricDerivative d.potential (pullbackRawGradient d χ) i x) ∞
        (potentialMeasure d.potential) := hi.mul hi
    simpa only [pow_two] using hh
  have hI : Integrable (fun x => sourceVectorMass d.potential (naturalCanonicalFlux d g) x *
      pullbackMetricSquare d χ x) (potentialMeasure d.potential) := hMi.mul_of_top_left hΓ
  have hMn : ∀ᵐ x ∂potentialMeasure d.potential,
      0 ≤ sourceVectorMass d.potential (naturalCanonicalFlux d g) x := by
    filter_upwards [naturalCanonicalMass_square_ae d g] with x hx
    rw [← hx]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hQn : 0 ≤ (16/c)*G^2 := mul_nonneg (div_nonneg (by norm_num) hc.le) (sq_nonneg G)
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ x, ((16/c)*G^2)*sourceVectorMass d.potential (naturalCanonicalFlux d g) x
        ∂potentialMeasure d.potential := by
      apply integral_mono_ae hI (hMi.const_mul _)
      filter_upwards [hMn, centeredTargetDatum_metric_square_uniform d hχ hc hκ hG hgrad]
        with x hx hγ
      change _ * pullbackMetricSquare d χ x ≤ _
      simpa only [pullbackMetricSquare, mul_comm] using
        (mul_le_mul_of_nonneg_left hγ hx)
    _ = ((16/c)*G^2)*(∫ x, sourceVectorMass d.potential (naturalCanonicalFlux d g) x
        ∂potentialMeasure d.potential) := integral_const_mul _ _
    _ ≤ (16/c)*G^2*‖g‖^2 := mul_le_mul_of_nonneg_left hMb hQn

theorem actual_centered_target_family_cutoff_error_budget
    {ρ : ℕ → Measure (Space n)} (d : ∀ k, SourceData (ρ k)) (hn : 1 ≤ n)
    {c : ℝ} (hc : 0 < c) (hκ : ∀ k, c ≤ (d k).targetConvexityConstant)
    {F : Space n → ℝ} (hF : Continuous F) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ y, ‖F y‖ ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m k : ℕ,
      Integrable (fun x => sourceVectorMass (d k).potential
        (naturalCanonicalFlux (d k) (centeredTargetDatum (d k) F hF)) x *
          pullbackMetricSquare (d k) (smoothCutoff n m) x) (potentialMeasure (d k).potential) ∧
      (∫ x, sourceVectorMass (d k).potential
        (naturalCanonicalFlux (d k) (centeredTargetDatum (d k) F hF)) x *
          pullbackMetricSquare (d k) (smoothCutoff n m) x ∂potentialMeasure (d k).potential)
        ≤ (16/c)*K^2*C^2*(cutoffScale m)^2 := by
  obtain ⟨K, hK, hgrad⟩ := smoothCutoff_gradient_bound (n := n)
  refine ⟨K, hK, fun m k => ?_⟩
  have hb := actual_natural_mass_pullback_cutoff_bound (d k) hn
    (centeredTargetDatum (d k) F hF) (centeredTargetDatum_mean_zero (d k) F hF)
    (smoothCutoff_contDiff m) hc (hκ k)
    (mul_nonneg (cutoffScale_pos m).le hK) (hgrad m)
  have hnC : ‖centeredTargetDatum (d k) F hF‖^2 ≤ C^2 :=
    (sq_le_sq₀ (norm_nonneg _) hC).mpr (centeredTargetDatum_norm_le (d k) F hF hC hbound)
  refine ⟨hb.1, hb.2.trans ?_⟩
  calc
    _ ≤ (16/c)*(cutoffScale m*K)^2*C^2 :=
      mul_le_mul_of_nonneg_left hnC (by positivity)
    _ = _ := by ring

end KLSConstantImprovement.ActualTargetCutoffErrorBudget405
#print axioms KLSConstantImprovement.ActualTargetCutoffErrorBudget405.actual_natural_mass_integrable_and_bound
#print axioms KLSConstantImprovement.ActualTargetCutoffErrorBudget405.actual_natural_mass_pullback_cutoff_bound
#print axioms KLSConstantImprovement.ActualTargetCutoffErrorBudget405.actual_centered_target_family_cutoff_error_budget
