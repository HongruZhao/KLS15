import KLSConstantImprovement.ActualNaturalSqrtMass405
import KLSConstantImprovement.ActualKatoNonlinearDomains405
import KLSConstantImprovement.ActualResponseLocalEquations405

/-! Actual local dominators for the square-root regularizers and their
metric fluxes, and the literal almost-everywhere flux limit. Compact
inverse bounds are paid by the canonical Monge-Ampere source data. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualNaturalKatoFluxLimit405
open KLS ActualBoundedCanonicalSource ActualNaturalSqrtMass405
open ActualKatoLocalDomains405 ActualKatoNonlinearDomains405 ActualResponseLocalEquations405
open ActualNaturalMassWeakDerivative405 ActualNaturalCovariantEnergy405 ActualSmoothKatoRegularizer405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem memLp_top_exists_ae_norm_bound {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {f : α → ℝ} (hf : MemLp f ∞ ν) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂ν, ‖f x‖ ≤ C := by
  have hs : eLpNormEssSup f ν < ⊤ := by
    simpa only [eLpNorm_exponent_top hf.aestronglyMeasurable] using hf.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hs
  refine ⟨(C : ℝ), NNReal.coe_nonneg C, ?_⟩
  filter_upwards [hC] with x hx
  exact_mod_cast hx

theorem naturalKatoValue_locally_dominated (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential)) :
    ∀ E : Set (Space n), IsCompact E → ∃ b : Space n → ℝ,
      Integrable b (volume.restrict E) ∧ ∀ k, ∀ᵐ x ∂volume.restrict E,
        ‖naturalKatoValue d g (cutoffScale k) x‖ ≤ b x := by
  intro E hE
  letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
  have hM := memLp_one_iff_integrable.mp (KLS.MemLp.restrict_volume_of_potentialMeasure
    (memLp_one_iff_integrable.mpr hMi) d.source_C1.continuous hE)
  refine ⟨fun x => ‖sourceVectorMass d.potential (naturalCanonicalFlux d g) x‖+2,
    hM.norm.add (integrable_const 2), fun k => Eventually.of_forall fun x => ?_⟩
  have hs := katoRegularizer_square_bound (cutoffScale_pos k)
    (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)
  have he : ‖naturalKatoValue d g (cutoffScale k) x‖^2 ≤
      ‖sourceVectorMass d.potential (naturalCanonicalFlux d g) x‖+1 := by
    simpa only [naturalKatoValue, Real.norm_eq_abs, sq_abs] using hs.trans
      (add_le_add (le_refl _) (cutoffScale_le_one k))
  nlinarith [sq_nonneg (‖naturalKatoValue d g (cutoffScale k) x‖-(1/2 : ℝ))]

theorem naturalKatoMetricFlux_tendsto_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (a : Fin n) :
    ∀ᵐ x ∂(volume : Measure (Space n)),
      Tendsto (fun k => naturalKatoMetricFlux d g Du (cutoffScale k) a x) atTop
        (𝓝 (((coordinateHessian d.potential x)⁻¹ *ᵥ
          (fun b => naturalSqrtMassDerivative d g Du b x)) a)) := by
  have hvol : (volume : Measure (Space n)) ≪ potentialMeasure d.potential :=
    volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous
  have hh : ∀ b : Fin n, ∀ᵐ x ∂(volume : Measure (Space n)),
      Tendsto (fun k => naturalKatoDerivative d g Du (cutoffScale k) b x) atTop
        (𝓝 (naturalSqrtMassDerivative d g Du b x)) :=
    fun b => (naturalKatoDerivative_tendsto_ae d g Du b).filter_mono hvol.ae_le
  filter_upwards [ae_all_iff.mpr hh] with x hx
  exact tendsto_finsetSum Finset.univ fun b _ =>
    (hx b).const_mul ((coordinateHessian d.potential x)⁻¹ a b)

theorem naturalKatoMetricFlux_locally_dominated (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm)
    (hEloc : LocallyIntegrable (naturalCovariantEnergy d g Du) volume) (a : Fin n) :
    ∀ E : Set (Space n), IsCompact E → ∃ b : Space n → ℝ,
      Integrable b (volume.restrict E) ∧ ∀ k, ∀ᵐ x ∂volume.restrict E,
        ‖naturalKatoMetricFlux d g Du (cutoffScale k) a x‖ ≤ b x := by
  intro E hE
  letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
  have hB : 0 ≤ 16/d.targetConvexityConstant := div_nonneg (by norm_num) d.target_convexity_pos.le
  have hb (b : Fin n) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂volume.restrict E,
      ‖(coordinateHessian d.potential x)⁻¹ a b‖ ≤ C :=
    memLp_top_exists_ae_norm_bound (sourceInverse_entry_local_top d a b E hE)
  choose C hC hbound using hb
  let D (x : Space n) : ℝ := (16/d.targetConvexityConstant)*‖naturalCovariantEnergy d g Du x‖+1
  have hDnonneg (x : Space n) : 0 ≤ D x := by dsimp only [D]; positivity
  have hDI : Integrable D (volume.restrict E) :=
    ((locallyIntegrable_iff.mp hEloc E hE).norm.const_mul _).add (integrable_const 1)
  refine ⟨fun x => (∑ b, C b)*D x, hDI.const_mul _, fun k => ?_⟩
  have hvol : (volume : Measure (Space n)) ≪ potentialMeasure d.potential :=
    volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous
  have he := (naturalKatoDerivative_energy_ae d g Du hcomp (cutoffScale_pos k)).filter_mono hvol.ae_le
  filter_upwards [ae_all_iff.mpr hbound, ae_restrict_of_ae he] with x hxJ hxD
  have hD (b : Fin n) : ‖naturalKatoDerivative d g Du (cutoffScale k) b x‖ ≤ D x := by
    have hs : ‖naturalKatoDerivative d g Du (cutoffScale k) b x‖^2 ≤
        (16/d.targetConvexityConstant)*‖naturalCovariantEnergy d g Du x‖ := by
      simpa only [Real.norm_eq_abs, sq_abs] using (hxD.2 b).trans
        (mul_le_mul_of_nonneg_left (le_abs_self _) hB)
    dsimp only [D]
    nlinarith [sq_nonneg (‖naturalKatoDerivative d g Du (cutoffScale k) b x‖-(1/2 : ℝ))]
  change ‖∑ b : Fin n, (coordinateHessian d.potential x)⁻¹ a b *
      naturalKatoDerivative d g Du (cutoffScale k) b x‖ ≤ (∑ b, C b)*D x
  calc
    _ ≤ ∑ b : Fin n, ‖(coordinateHessian d.potential x)⁻¹ a b *
        naturalKatoDerivative d g Du (cutoffScale k) b x‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin n, C b*D x := by
      apply Finset.sum_le_sum
      intro b _
      rw [norm_mul]
      exact mul_le_mul (hxJ b) (hD b) (norm_nonneg _) (hC b)
    _ = _ := by rw [Finset.sum_mul]

end KLSConstantImprovement.ActualNaturalKatoFluxLimit405
#print axioms KLSConstantImprovement.ActualNaturalKatoFluxLimit405.memLp_top_exists_ae_norm_bound
#print axioms KLSConstantImprovement.ActualNaturalKatoFluxLimit405.naturalKatoValue_locally_dominated
#print axioms KLSConstantImprovement.ActualNaturalKatoFluxLimit405.naturalKatoMetricFlux_tendsto_ae
#print axioms KLSConstantImprovement.ActualNaturalKatoFluxLimit405.naturalKatoMetricFlux_locally_dominated
