import KLSConstantImprovement.ActualNaturalLocalConnectionDomain405
import KLSConstantImprovement.ActualSourceNaturalTargetCurvatureDomain405

/-! The untruncated local H-evolution balance for the actual natural
inverse. Positive local Gamma is paid first. Every signed term then has
an actual domain, and the radial derivative error vanishes by dominated
convergence. There is no bounded-mass premise or spatial limit here. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualNaturalLocalConnectionBalance405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualSourceConnectionFields405 ActualSourceConnectionPointwise405
open ActualSourceRadialConnectionDomains405 ActualSourceRadialConnectionBalance405
open ActualSourceCompactMetricCondition405 ActualSourceCompactCutoffBound405
open ActualSourceCompactConnectionAbsorption405 ActualRadialMatrixCalculus405
open ActualNaturalLocalConnectionDomain405 ActualSourceNaturalTargetCurvatureDomain405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem radial_denominator_tendsto_one (u : Fin n → Space n → ℝ) (x : Space n) :
    Tendsto (fun k => radialDenom (cutoffScale k) (fun i => u i x)) atTop (𝓝 (1 : ℝ)) := by
  simpa only [radialDenom, zero_mul, add_zero] using
    tendsto_const_nhds.add (cutoffScale_tendsto_zero.mul_const (radialSquare (fun i => u i x)))

theorem radial_quotient_tendsto (u : Fin n → Space n → ℝ) (v : Space n → ℝ) (x : Space n) :
    Tendsto (fun k => v x / radialDenom (cutoffScale k) (fun i => u i x)) atTop (𝓝 (v x)) := by
  have h := (tendsto_const_nhds (x := v x)).div (radial_denominator_tendsto_one u x) one_ne_zero
  change Tendsto (fun k => v x / radialDenom (cutoffScale k) (fun i => u i x)) atTop (𝓝 (v x / 1)) at h
  simpa only [div_one] using h

theorem integral_radial_quotient_tendsto {ν : Measure (Space n)}
    (u : Fin n → Space n → ℝ) {v : Space n → ℝ} (hv : Integrable v ν)
    (hseq : ∀ k, Integrable (fun x => v x / radialDenom (cutoffScale k) (fun i => u i x)) ν) :
    Tendsto (fun k => ∫ x, v x / radialDenom (cutoffScale k) (fun i => u i x) ∂ν)
      atTop (𝓝 (∫ x, v x ∂ν)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖v x‖)
    (fun k => (hseq k).aestronglyMeasurable) hv.norm
  · intro k
    exact Eventually.of_forall fun x => by
      have hden : 1 ≤ radialDenom (cutoffScale k) (fun i => u i x) :=
        le_add_of_nonneg_right (mul_nonneg (cutoffScale_pos k).le (radialSquare_nonnegative _))
      rw [norm_div, Real.norm_of_nonneg (le_trans zero_le_one hden)]
      exact div_le_self (norm_nonneg _) hden
  · exact Eventually.of_forall (radial_quotient_tendsto u v)

theorem actual_untruncated_compact_connection_fields (d : SourceData μ)
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
    Integrable (fun x => χ x ^ 2 * sourceConnectionCross d (naturalCanonicalFlux d g) Du x) (potentialMeasure d.potential) ∧
    Integrable (fun x => χ x * sourceConnectionBoundary d χ (naturalCanonicalFlux d g) x) (potentialMeasure d.potential) ∧
    Integrable (fun x => χ x ^ 2 * sourceVectorMass d.potential (naturalCanonicalFlux d g) x) (potentialMeasure d.potential) ∧
    Integrable (fun x => χ x ^ 2 * sourceConnectionTarget d (naturalCanonicalFlux d g) x) (potentialMeasure d.potential) ∧
    Integrable (fun x => χ x ^ 2 * sourceConnectionGamma d (naturalCanonicalFlux d g) x) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let ν := potentialMeasure d.potential
  let u := naturalCanonicalFlux d g
  have hG := actual_compact_connectionGamma_integrable d g Du hDu hw hcomp hMi hQi hχ hc hb
  have hχtop : MemLp χ ∞ ν := hχ.continuous.memLp_of_hasCompactSupport hc
  have hχsq : MemLp (fun x => χ x ^ 2) ∞ ν := by
    have h : MemLp (χ * χ) ∞ ν := hχtop.mul hχtop
    change MemLp (fun x => χ x * χ x) ∞ ν at h
    simpa only [pow_two] using h
  have hQ : Integrable (fun x => χ x ^ 2 * sourceVectorJacobianEnergy Du x) ν :=
    hQi.mul_of_top_right hχsq
  have hM : Integrable (fun x => χ x ^ 2 * sourceVectorMass d.potential u x) ν :=
    hMi.mul_of_top_right hχsq
  have hP : Integrable (fun x => χ x ^ 2 * sourceConnectionTarget d u x) ν :=
    (natural_targetCurvature_integrable d g).mul_of_top_right hχsq
  have hZ := actual_compact_mass_cutoff_integrable d g hMi hχ hc
  have hseq (k : ℕ) := actual_compact_radial_connection_fields_integrable d g
    (cutoffScale_pos k) Du hDu hχ hc
  have hXm : AEStronglyMeasurable (fun x => χ x ^ 2 * sourceConnectionCross d u Du x) ν :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hseq k).1.aestronglyMeasurable)
      (Eventually.of_forall (radial_quotient_tendsto u _))
  have hBm : AEStronglyMeasurable (fun x => χ x * sourceConnectionBoundary d χ u x) ν :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hseq k).2.2.1.aestronglyMeasurable)
      (Eventually.of_forall (radial_quotient_tendsto u _))
  have hX : Integrable (fun x => χ x ^ 2 * sourceConnectionCross d u Du x) ν := by
    apply ((hG.const_mul (1/4 : ℝ)).add (hQ.const_mul 4)).mono' hXm
    filter_upwards [sourceConnectionCross_abs_le_ae d u Du hcomp] with x hx
    change ‖χ x ^ 2 * sourceConnectionCross d u Du x‖ ≤
      (1/4 : ℝ) * (χ x ^ 2 * sourceConnectionGamma d u x) + 4 * (χ x ^ 2 * sourceVectorJacobianEnergy Du x)
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    nlinarith only [mul_le_mul_of_nonneg_left hx (sq_nonneg (χ x))]
  have hB : Integrable (fun x => χ x * sourceConnectionBoundary d χ u x) ν := by
    apply ((hG.const_mul (1/4 : ℝ)).add (hZ.const_mul 4)).mono' hBm
    filter_upwards [sourceConnectionBoundary_abs_le_ae d u χ] with x hx
    change ‖χ x * sourceConnectionBoundary d χ u x‖ ≤
      (1/4 : ℝ) * (χ x ^ 2 * sourceConnectionGamma d u x) +
        4 * (sourceVectorMass d.potential u x * inverseHessianGradientForm d.potential χ x)
    rw [Real.norm_eq_abs]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hx
    linarith [abs_nonneg (χ x * sourceConnectionBoundary d χ u x)]
  exact ⟨hX, hB, hM, hP, hG⟩

theorem actual_untruncated_compact_connection_balance (d : SourceData μ)
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
    (∫ x, χ x ^ 2 * (sourceConnectionTarget d (naturalCanonicalFlux d g) x +
      sourceConnectionGamma d (naturalCanonicalFlux d g) x) ∂potentialMeasure d.potential) =
      (∫ x, χ x ^ 2 * sourceVectorMass d.potential (naturalCanonicalFlux d g) x ∂potentialMeasure d.potential) -
      (∫ x, χ x ^ 2 * sourceConnectionCross d (naturalCanonicalFlux d g) Du x ∂potentialMeasure d.potential) -
      2 * (∫ x, χ x * sourceConnectionBoundary d χ (naturalCanonicalFlux d g) x ∂potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let ν := potentialMeasure d.potential
  let u := naturalCanonicalFlux d g
  let f (k : ℕ) (x : Space n) := radialDenom (cutoffScale k) (fun a => u a x)
  obtain ⟨hX, hB, hM, hP, hG⟩ :=
    actual_untruncated_compact_connection_fields d g Du hDu hw hcomp hMi hQi hχ hc hb
  change Integrable (fun x => χ x ^ 2 * sourceConnectionCross d u Du x) ν at hX
  change Integrable (fun x => χ x * sourceConnectionBoundary d χ u x) ν at hB
  change Integrable (fun x => χ x ^ 2 * sourceVectorMass d.potential u x) ν at hM
  change Integrable (fun x => χ x ^ 2 * sourceConnectionTarget d u x) ν at hP
  change Integrable (fun x => χ x ^ 2 * sourceConnectionGamma d u x) ν at hG
  have hPG : Integrable (fun x => χ x ^ 2 * (sourceConnectionTarget d u x + sourceConnectionGamma d u x)) ν := by
    apply (hP.add hG).congr
    exact Eventually.of_forall fun x => by dsimp only [Pi.add_apply]; ring
  have hseq (k : ℕ) := actual_compact_radial_connection_fields_integrable d g
    (cutoffScale_pos k) Du hDu hχ hc
  have hL := integral_radial_quotient_tendsto u hPG (fun k => by
    apply ((hseq k).2.2.2.2.1.add (hseq k).2.2.2.2.2).congr
    exact Eventually.of_forall fun x => by dsimp only [Pi.add_apply]; ring)
  have hML := integral_radial_quotient_tendsto u hM (fun k => (hseq k).2.2.2.1)
  have hXL := integral_radial_quotient_tendsto u hX (fun k => (hseq k).1)
  have hBL := integral_radial_quotient_tendsto u hB (fun k => (hseq k).2.2.1)
  obtain ⟨c, hc0, hExtra⟩ := exists_actual_compact_radial_extra_bound d g Du hcomp (tsupport χ) hc
  have hχtop : MemLp χ ∞ ν := hχ.continuous.memLp_of_hasCompactSupport hc
  have hχsq : MemLp (fun x => χ x ^ 2) ∞ ν := by
    have h : MemLp (χ * χ) ∞ ν := hχtop.mul hχtop
    change MemLp (fun x => χ x * χ x) ∞ ν at h
    simpa only [pow_two] using h
  have hQ : Integrable (fun x => χ x ^ 2 * sourceVectorJacobianEnergy Du x) ν :=
    hQi.mul_of_top_right hχsq
  let Y (k : ℕ) (x : Space n) := 2 * cutoffScale k *
    (χ x ^ 2 * sourceRadialExtra d u Du x / f k x ^ 2)
  have hY (k : ℕ) : Integrable (Y k) ν := (hseq k).2.1.const_mul (2 * cutoffScale k)
  have hDom : Integrable (fun x => (1/4 : ℝ) * (χ x ^ 2 * sourceConnectionGamma d u x) +
      4 * c * (χ x ^ 2 * sourceVectorJacobianEnergy Du x)) ν := by
    have h1 : Integrable (fun x => (1/4 : ℝ) * (χ x ^ 2 * sourceConnectionGamma d u x)) ν :=
      hG.const_mul (1/4 : ℝ)
    have h2 : Integrable (fun x => 4 * c * (χ x ^ 2 * sourceVectorJacobianEnergy Du x)) ν :=
      hQ.const_mul (4 * c)
    exact h1.add h2
  have hYL : Tendsto (fun k => ∫ x, Y k x ∂ν) atTop (𝓝 0) := by
    have ht : Tendsto (fun k => ∫ x, Y k x ∂ν) atTop (𝓝 (∫ x, (0 : ℝ) ∂ν)) := by
      apply tendsto_integral_of_dominated_convergence
        (fun x => (1/4 : ℝ) * (χ x ^ 2 * sourceConnectionGamma d u x) +
          4 * c * (χ x ^ 2 * sourceVectorJacobianEnergy Du x))
        (fun k => (hY k).aestronglyMeasurable)
        hDom
      · intro k
        have he := (ae_restrict_iff' hc.measurableSet).mp (hExtra (cutoffScale k) (cutoffScale_pos k).le)
        filter_upwards [he, sourceConnectionGamma_nonnegative_ae d u,
          sourceVectorJacobianEnergy_nonnegative_ae d Du hcomp] with x hx hΓ hQn
        by_cases hs : x ∈ tsupport χ
        · have hfn : 1 ≤ f k x := le_add_of_nonneg_right
            (mul_nonneg (cutoffScale_pos k).le (radialSquare_nonnegative _))
          have hgdiv := div_le_self hΓ hfn
          have hqdiv := div_le_self hQn hfn
          have hxc := mul_le_mul_of_nonneg_left (hx hs) (sq_nonneg (χ x))
          change ‖Y k x‖ ≤ _
          dsimp only [Y]
          rw [Real.norm_eq_abs]
          have hn : |2 * cutoffScale k * (χ x ^ 2 * sourceRadialExtra d u Du x / f k x ^ 2)| =
              χ x ^ 2 * |2 * cutoffScale k * sourceRadialExtra d u Du x / f k x ^ 2| := by
            rw [show 2 * cutoffScale k * (χ x ^ 2 * sourceRadialExtra d u Du x / f k x ^ 2) =
              χ x ^ 2 * (2 * cutoffScale k * sourceRadialExtra d u Du x / f k x ^ 2) by ring,
              abs_mul, abs_of_nonneg (sq_nonneg _)]
          rw [hn]
          have ha := mul_le_mul_of_nonneg_left hgdiv (by positivity : 0 ≤ χ x ^ 2 / 4)
          have hb' := mul_le_mul_of_nonneg_left hqdiv (by positivity : 0 ≤ χ x ^ 2 * (4 * c))
          have hxc' : χ x ^ 2 * |2 * cutoffScale k * sourceRadialExtra d u Du x / f k x ^ 2| ≤
              (χ x ^ 2 / 4) * (sourceConnectionGamma d u x / f k x) +
                (χ x ^ 2 * (4 * c)) * (sourceVectorJacobianEnergy Du x / f k x) := by
            convert hxc using 1 <;> ring
          nlinarith only [hxc', ha, hb']
        · have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport hs
          simp only [Y, hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, zero_div,
            mul_zero, norm_zero]
          positivity
      · exact Eventually.of_forall fun x => by
          have hd := (radial_denominator_tendsto_one u x).pow 2
          have hn := (cutoffScale_tendsto_zero.const_mul 2).mul_const
            (χ x ^ 2 * sourceRadialExtra d u Du x)
          have hh := hn.div hd (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
          change Tendsto (fun k => 2 * cutoffScale k * (χ x ^ 2 * sourceRadialExtra d u Du x) /
            f k x ^ 2) atTop (𝓝 ((2 * 0 * (χ x ^ 2 * sourceRadialExtra d u Du x)) / 1 ^ 2)) at hh
          simpa only [Y, mul_div_assoc, zero_mul, mul_zero, zero_div, one_pow] using hh
    simpa only [integral_zero] using ht
  have hbal (k : ℕ) := actual_compact_radial_connection_balance d g (cutoffScale_pos k)
    Du hDu hw hχ hc hb
  have hright : Tendsto (fun k => ∫ x, χ x ^ 2 *
      (sourceConnectionTarget d u x + sourceConnectionGamma d u x) / f k x ∂ν) atTop
      (𝓝 ((∫ x, χ x ^ 2 * sourceVectorMass d.potential u x ∂ν) -
        (∫ x, χ x ^ 2 * sourceConnectionCross d u Du x ∂ν) -
        2 * (∫ x, χ x * sourceConnectionBoundary d χ u x ∂ν))) := by
    have hyi (k : ℕ) : (∫ x, Y k x ∂ν) = (2 * cutoffScale k) *
        ∫ x, χ x ^ 2 * sourceRadialExtra d u Du x / f k x ^ 2 ∂ν := integral_const_mul _ _
    have hseqeq (k : ℕ) :
        ((∫ x, χ x ^ 2 * sourceVectorMass d.potential u x / f k x ∂ν) -
          (∫ x, χ x ^ 2 * sourceConnectionCross d u Du x / f k x ∂ν) +
          (∫ x, Y k x ∂ν)) - 2 * (∫ x, χ x * sourceConnectionBoundary d χ u x / f k x ∂ν) =
            ∫ x, χ x ^ 2 * (sourceConnectionTarget d u x + sourceConnectionGamma d u x) / f k x ∂ν := by
      rw [hyi]
      exact (hbal k).symm
    have hh := (((hML.sub hXL).add hYL).sub (hBL.const_mul 2)).congr hseqeq
    simpa only [add_zero] using hh
  exact tendsto_nhds_unique hL hright

end KLSConstantImprovement.ActualNaturalLocalConnectionBalance405
#print axioms KLSConstantImprovement.ActualNaturalLocalConnectionBalance405.integral_radial_quotient_tendsto
#print axioms KLSConstantImprovement.ActualNaturalLocalConnectionBalance405.actual_untruncated_compact_connection_fields
#print axioms KLSConstantImprovement.ActualNaturalLocalConnectionBalance405.actual_untruncated_compact_connection_balance
