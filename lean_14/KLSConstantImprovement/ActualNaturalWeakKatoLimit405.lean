import KLSConstantImprovement.ActualNaturalKatoFluxLimit405
import KLSConstantImprovement.ActualLocalDominatedWeakClosure405
import KLSConstantImprovement.ActualWeakKatoCompactExcess405

/-! Pass the actual regularized weak Kato inequalities to the literal
square root of natural mass. All compact pairings use paid local L1
dominators and the actual density; no strong operator core, subsequence
or bounded natural mass is needed. The regularized inequality is explicit
until supplied by the separate actual nonlinear Bochner theorem. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualNaturalWeakKatoLimit405
open KLS ActualBoundedCanonicalSource ActualNaturalKatoFluxLimit405 ActualNaturalSqrtMass405
open ActualKatoLocalDomains405 ActualKatoNonlinearDomains405 ActualLocalDominatedWeakClosure405
open ActualWeakKatoCompactExcess405 ActualNaturalCovariantEnergy405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceNaturalHessian405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem compact_weighted_dominated_pairing_tendsto
    (d : SourceData μ) {f : ℕ → Space n → ℝ} {u : Space n → ℝ}
    (hf : ∀ k, LocallyIntegrable (f k) volume)
    (hlim : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto (fun k => f k x) atTop (𝓝 (u x)))
    (hdom : ∀ E : Set (Space n), IsCompact E → ∃ b : Space n → ℝ,
      Integrable b (volume.restrict E) ∧ ∀ k, ∀ᵐ x ∂volume.restrict E, ‖f k x‖ ≤ b x)
    {ψ : Space n → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Tendsto (fun k => ∫ x, f k x*ψ x ∂potentialMeasure d.potential) atTop
      (𝓝 (∫ x, u x*ψ x ∂potentialMeasure d.potential)) := by
  have hρ : Continuous (fun x => Real.exp (-d.potential x)) :=
    Real.continuous_exp.comp d.source_C1.continuous.neg
  have hct : Continuous (fun x => ψ x*Real.exp (-d.potential x)) := hψ.mul hρ
  have hcc : HasCompactSupport (fun x => ψ x*Real.exp (-d.potential x)) := hcψ.mul_right
  obtain ⟨C, hC⟩ := hcc.exists_bound_of_continuous hct
  have ht := local_dominated_compact_pairing_tendsto hf hlim hdom hct.aestronglyMeasurable hcc
    ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩
  simpa only [integral_potentialMeasure d.source_C1.continuous.measurable, mul_assoc] using ht

theorem natural_weak_Kato_of_regularized
    (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hC : ∀ i a E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i a) 2 (volume.restrict E))
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (hEloc : LocallyIntegrable (naturalCovariantEnergy d g Du) volume)
    (B : ℝ)
    (hweak : ∀ (k : ℕ) (ψ : Space n → ℝ), ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∀ x, 0 ≤ ψ x) →
      (∑ i, ∫ x, naturalKatoMetricFlux d g Du (cutoffScale k) i x * coordinateDerivative ψ i x
        ∂potentialMeasure d.potential) ≤
      ∫ x, (B+Real.sqrt (cutoffScale k)/2-naturalKatoValue d g (cutoffScale k) x/2)*ψ x
        ∂potentialMeasure d.potential) :
    ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
      (∑ i, ∫ x, rawKatoFlux d (naturalSqrtMassDerivative d g Du) i x * coordinateDerivative ψ i x
        ∂potentialMeasure d.potential) ≤
      ∫ x, (B-naturalSqrtMass d g x/2)*ψ x ∂potentialMeasure d.potential := by
  have hvol : (volume : Measure (Space n)) ≪ potentialMeasure d.potential :=
    volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous
  have hfv (k : ℕ) := naturalKatoValue_local_L2 d g hMi (cutoffScale_pos k)
  have hDv (k : ℕ) (a : Fin n) :=
    naturalKatoDerivative_local_L2 d g Du hu hDu hC hcomp hMi hEloc (cutoffScale_pos k) a
  have hFlux (k : ℕ) (i : Fin n) :
      LocallyIntegrable (naturalKatoMetricFlux d g Du (cutoffScale k) i) volume :=
    locallyIntegrable_of_memLp_two_on_compacts
      (naturalKatoMetricFlux_local_L2 d g Du (hDv k) i)
  have hvalLim := (naturalKatoValue_tendsto_ae d g).filter_mono hvol.ae_le
  have hroot : Tendsto (fun k : ℕ => Real.sqrt (cutoffScale k)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp cutoffScale_tendsto_zero
  let b (k : ℕ) (x : Space n) : ℝ :=
    B+Real.sqrt (cutoffScale k)/2-naturalKatoValue d g (cutoffScale k) x/2
  have hbLocal (k : ℕ) : LocallyIntegrable (b k) volume := by
    apply locallyIntegrable_of_memLp_two_on_compacts
    intro E hE
    letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
    have hh : MemLp (fun x => (B+Real.sqrt (cutoffScale k)/2)-
        (1/2 : ℝ)*naturalKatoValue d g (cutoffScale k) x) 2 (volume.restrict E) :=
      (memLp_const (B+Real.sqrt (cutoffScale k)/2)).sub ((hfv k E hE).const_mul (1/2 : ℝ))
    convert hh using 1
    funext x
    dsimp only [b]
    ring
  have hbLim : ∀ᵐ x ∂(volume : Measure (Space n)),
      Tendsto (fun k => b k x) atTop (𝓝 (B-naturalSqrtMass d g x/2)) := by
    filter_upwards [hvalLim] with x hx
    simpa only [b, zero_div, add_zero] using
      (tendsto_const_nhds.add (hroot.div_const 2)).sub (hx.div_const 2)
  have hbDom : ∀ E : Set (Space n), IsCompact E → ∃ c : Space n → ℝ,
      Integrable c (volume.restrict E) ∧ ∀ k, ∀ᵐ x ∂volume.restrict E, ‖b k x‖ ≤ c x := by
    intro E hE
    letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
    obtain ⟨c, hc, hcb⟩ := naturalKatoValue_locally_dominated d g hMi E hE
    refine ⟨fun x => (‖B‖+1)+‖c x‖, (integrable_const (‖B‖+1)).add hc.norm, fun k => ?_⟩
    filter_upwards [hcb k] with x hx
    have hcs : Real.sqrt (cutoffScale k) ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (cutoffScale_le_one k)
    have hs := Real.sqrt_nonneg (cutoffScale k)
    have h0 := norm_nonneg (c x)
    have hv : ‖naturalKatoValue d g (cutoffScale k) x‖ ≤ ‖c x‖ := hx.trans (Real.le_norm_self _)
    have hn : ‖b k x‖ ≤ ‖B‖ + ‖Real.sqrt (cutoffScale k)/2‖ +
        ‖naturalKatoValue d g (cutoffScale k) x/2‖ := by
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    rw [norm_div, norm_div, Real.norm_of_nonneg hs] at hn
    norm_num at hn
    simp only [Real.norm_eq_abs] at hv h0 ⊢
    nlinarith only [hn, hcs, hv, h0]
  intro ψ hψ hcψ hnψ
  have hleft (i : Fin n) :
      Tendsto (fun k => ∫ x, naturalKatoMetricFlux d g Du (cutoffScale k) i x *
        coordinateDerivative ψ i x ∂potentialMeasure d.potential) atTop
        (𝓝 (∫ x, rawKatoFlux d (naturalSqrtMassDerivative d g Du) i x *
          coordinateDerivative ψ i x ∂potentialMeasure d.potential)) := by
    have hd : Continuous (coordinateDerivative ψ i) :=
      (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous
    have hcd : HasCompactSupport (coordinateDerivative ψ i) := hasCompactSupport_coordinateDerivative hcψ i
    exact compact_weighted_dominated_pairing_tendsto d (fun k => hFlux k i)
      (naturalKatoMetricFlux_tendsto_ae d g Du i)
      (naturalKatoMetricFlux_locally_dominated d g Du hcomp hEloc i) hd hcd
  have hright := compact_weighted_dominated_pairing_tendsto d hbLocal hbLim hbDom hψ.continuous hcψ
  exact le_of_tendsto_of_tendsto (tendsto_finsetSum Finset.univ fun i _ => hleft i)
    hright (Eventually.of_forall fun k => hweak k ψ hψ hcψ hnψ)

end KLSConstantImprovement.ActualNaturalWeakKatoLimit405
#print axioms KLSConstantImprovement.ActualNaturalWeakKatoLimit405.compact_weighted_dominated_pairing_tendsto
#print axioms KLSConstantImprovement.ActualNaturalWeakKatoLimit405.natural_weak_Kato_of_regularized
