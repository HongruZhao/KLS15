import KLSConstantImprovement.ActualLocalRadialConnectionAbsorption405
import KLSConstantImprovement.ActualUniformIntegralFatou405

/-! Positive radial Fatou pays the actual natural connection locally,
without a bounded mass hypothesis. The final theorem constructs its raw Du
internally from the accepted unconditional natural Gaffney theorem. -/
noncomputable section
open MeasureTheory Set Filter Matrix Metric
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualNaturalLocalConnectionDomain405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualSourceConnectionFields405 ActualSourceRadialConnectionDomains405
open ActualLocalRadialConnectionAbsorption405 ActualUniformIntegralFatou405
open ActualRadialMatrixCalculus405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_compact_connectionGamma_integrable (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (hQi : Integrable (sourceVectorJacobianEnergy Du) (potentialMeasure d.potential))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hb : ∀ x, ‖χ x‖ ≤ 1) :
    Integrable (fun x => χ x ^ 2 * sourceConnectionGamma d (naturalCanonicalFlux d g) x)
      (potentialMeasure d.potential) := by
  let ν := potentialMeasure d.potential
  let u := naturalCanonicalFlux d g
  obtain ⟨c, _hc0, hbound⟩ :=
    actual_uniform_compact_radial_connection_absorption d g Du hDu hw hcomp hMi hQi hχ hc hb
  let C : ℝ :=
    4 * (∫ x, χ x ^ 2 * sourceVectorMass d.potential u x ∂ν) +
    16 * (1 + c) * (∫ x, χ x ^ 2 * sourceVectorJacobianEnergy Du x ∂ν) +
    16 * (∫ x, sourceVectorMass d.potential u x * inverseHessianGradientForm d.potential χ x ∂ν)
  let F (k : ℕ) (x : Space n) : ℝ := χ x ^ 2 * sourceConnectionGamma d u x /
    radialDenom (cutoffScale k) (fun a => u a x)
  let f (x : Space n) : ℝ := χ x ^ 2 * sourceConnectionGamma d u x
  have hF (k : ℕ) : Integrable (F k) ν := by
    obtain ⟨_, _, _, _, _, hG⟩ :=
      actual_compact_radial_connection_fields_integrable d g (cutoffScale_pos k) Du hDu hχ hc
    exact hG
  have hlim (x : Space n) : Tendsto (fun k => F k x) atTop (𝓝 (f x)) := by
    have hd : Tendsto (fun k => radialDenom (cutoffScale k) (fun a => u a x))
        atTop (𝓝 (1 : ℝ)) := by
      simpa only [radialDenom, zero_mul, add_zero] using
        tendsto_const_nhds.add (cutoffScale_tendsto_zero.mul_const (radialSquare (fun a => u a x)))
    have hn : Tendsto (fun _k : ℕ => χ x ^ 2 * sourceConnectionGamma d u x)
        atTop (𝓝 (χ x ^ 2 * sourceConnectionGamma d u x)) := tendsto_const_nhds
    have ht := hn.div hd one_ne_zero
    change Tendsto (fun k => χ x ^ 2 * sourceConnectionGamma d u x /
      radialDenom (cutoffScale k) (fun a => u a x)) atTop
      (𝓝 ((χ x ^ 2 * sourceConnectionGamma d u x) / 1)) at ht
    simpa only [F, f, div_one] using ht
  have hf : AEStronglyMeasurable f ν := aestronglyMeasurable_of_tendsto_ae atTop
    (fun k => (hF k).aestronglyMeasurable) (Eventually.of_forall hlim)
  have hnorm (k : ℕ) : (∫ x, ‖F k x‖ ∂ν) = ∫ x, F k x ∂ν := by
    apply integral_congr_ae
    filter_upwards [sourceConnectionGamma_nonnegative_ae d u] with x hx
    exact Real.norm_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg (χ x)) hx)
      (radialDenom_positive (cutoffScale_pos k).le _).le)
  have hbnd (k : ℕ) : (∫ x, ‖F k x‖ ∂ν) ≤ max C 0 := by
    rw [hnorm]
    exact (hbound (cutoffScale k) (cutoffScale_pos k)).trans (le_max_left _ _)
  exact (integrable_and_integral_norm_le_of_tendsto_uniform_bound hf hF
    (Eventually.of_forall hlim) (le_max_right C 0) hbnd).1

theorem actual_connectionGamma_local_domains (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (hQi : Integrable (sourceVectorJacobianEnergy Du) (potentialMeasure d.potential))
    (E : Set (Space n)) (hE : IsCompact E) :
    Integrable (sourceConnectionGamma d (naturalCanonicalFlux d g)) ((potentialMeasure d.potential).restrict E) ∧
      Integrable (sourceConnectionGamma d (naturalCanonicalFlux d g)) (volume.restrict E) := by
  obtain ⟨R, hR, hER⟩ := hE.isBounded.subset_ball_lt 0 (0 : Space n)
  let χ : ContDiffBump (0 : Space n) := ⟨R, R + 1, hR, by linarith⟩
  have hone (x : Space n) (hx : x ∈ E) : χ x = 1 :=
    χ.one_of_mem_closedBall (ball_subset_closedBall (hER hx))
  have hb (x : Space n) : ‖χ x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg χ.nonneg]
    exact χ.le_one
  have hχ := actual_compact_connectionGamma_integrable d g Du hDu hw hcomp hMi hQi
    (show ContDiff ℝ 1 (χ : Space n → ℝ) from χ.contDiff) χ.hasCompactSupport hb
  have heq : (fun x => χ x ^ 2 * sourceConnectionGamma d (naturalCanonicalFlux d g) x)
      =ᵐ[(potentialMeasure d.potential).restrict E] sourceConnectionGamma d (naturalCanonicalFlux d g) := by
    filter_upwards [ae_restrict_mem hE.measurableSet] with x hx
    rw [hone x hx, one_pow, one_mul]
  have hvol := KLS.MemLp.restrict_volume_of_potentialMeasure
    (memLp_one_iff_integrable.mpr hχ) d.source_C1.continuous hE
  refine ⟨(hχ.restrict (s := E)).congr heq, ?_⟩
  apply (memLp_one_iff_integrable.mp hvol).congr
  filter_upwards [ae_restrict_mem hE.measurableSet] with x hx
  rw [hone x hx, one_pow, one_mul]

theorem actual_natural_connectionGamma_local (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) :
    ∀ E : Set (Space n), IsCompact E →
      Integrable (sourceConnectionGamma d (naturalCanonicalFlux d g)) ((potentialMeasure d.potential).restrict E) ∧
      Integrable (sourceConnectionGamma d (naturalCanonicalFlux d g)) (volume.restrict E) := by
  obtain ⟨Du, _hu, hDu, hw, hcomp, hMi, hQi, _hEnergy, _hdiv⟩ :=
    exists_naturalCanonicalFlux_gaffney d hn g hg
  exact actual_connectionGamma_local_domains d g Du hDu hw hcomp hMi hQi

end KLSConstantImprovement.ActualNaturalLocalConnectionDomain405
#print axioms KLSConstantImprovement.ActualNaturalLocalConnectionDomain405.actual_compact_connectionGamma_integrable
#print axioms KLSConstantImprovement.ActualNaturalLocalConnectionDomain405.actual_connectionGamma_local_domains
#print axioms KLSConstantImprovement.ActualNaturalLocalConnectionDomain405.actual_natural_connectionGamma_local
