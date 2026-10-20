import KLSConstantImprovement.ActualKatoRegularizedWeakChain405
import KLSConstantImprovement.ActualKatoCoefficientBounds405
import KLSConstantImprovement.ActualLocalDominatedWeakClosure405

/-! The zero-regularization limit is the actual square root of natural
mass. Its literal raw derivative and local L2 domains follow from genuine
compact weak pairings and the uniform covariant energy bound. No mass
boundedness, subsequence or level-set derivative assertion is assumed. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualNaturalSqrtMass405
open KLS ActualBoundedCanonicalSource ActualKatoLocalDomains405
open ActualKatoRegularizedWeakChain405 ActualKatoCoefficientBounds405
open ActualLocalDominatedWeakClosure405 ActualSmoothKatoRegularizer405
open ActualNaturalMassWeakDerivative405 ActualNaturalCovariantEnergy405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceNaturalHessian405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

def naturalSqrtMass (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (x : Space n) : ℝ :=
  Real.sqrt (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)

def naturalSqrtMassDerivative (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (a : Fin n) (x : Space n) : ℝ :=
  (if sourceVectorMass d.potential (naturalCanonicalFlux d g) x = 0 then 0
    else 1 / (2 * Real.sqrt (sourceVectorMass d.potential (naturalCanonicalFlux d g) x))) *
      naturalMassRawDerivative d g Du a x

theorem naturalKatoValue_tendsto_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      Tendsto (fun k => naturalKatoValue d g (cutoffScale k) x) atTop (𝓝 (naturalSqrtMass d g x)) := by
  filter_upwards [natural_mass_nonnegative_ae d g] with x hx
  exact katoRegularizer_tendsto hx

theorem naturalKatoDerivative_tendsto_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (a : Fin n) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      Tendsto (fun k => naturalKatoDerivative d g Du (cutoffScale k) a x) atTop
        (𝓝 (naturalSqrtMassDerivative d g Du a x)) := by
  filter_upwards [natural_mass_nonnegative_ae d g] with x hx
  exact (katoFirst_tendsto hx).mul_const (naturalMassRawDerivative d g Du a x)

theorem naturalSqrtMass_local_L2 (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (naturalSqrtMass d g) 2 (volume.restrict E) := by
  have hM := memLp_one_iff_integrable.mp (KLS.MemLp.restrict_volume_of_potentialMeasure
    (memLp_one_iff_integrable.mpr hMi) d.source_C1.continuous hE)
  have hm : AEStronglyMeasurable (naturalSqrtMass d g) (volume.restrict E) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hM.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply hM.norm.mono' (hm.pow 2)
  exact Eventually.of_forall fun x => by
    change ‖Real.sqrt (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)^2‖ ≤
      ‖sourceVectorMass d.potential (naturalCanonicalFlux d g) x‖
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    by_cases hx : 0 ≤ sourceVectorMass d.potential (naturalCanonicalFlux d g) x
    · rw [Real.sq_sqrt hx]
      exact le_abs_self _
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hx)]
      simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using abs_nonneg
        (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)

theorem naturalSqrtMassDerivative_energy_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm)
    (a : Fin n) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      naturalSqrtMassDerivative d g Du a x^2 ≤
        (16/d.targetConvexityConstant)*naturalCovariantEnergy d g Du x := by
  have hb : ∀ k : ℕ, ∀ᵐ x ∂potentialMeasure d.potential,
      naturalKatoDerivative d g Du (cutoffScale k) a x^2 ≤
        (16/d.targetConvexityConstant)*naturalCovariantEnergy d g Du x :=
    fun k => (naturalKatoDerivative_energy_ae d g Du hcomp (cutoffScale_pos k)).mono fun _ hx => hx.2 a
  filter_upwards [naturalKatoDerivative_tendsto_ae d g Du a, ae_all_iff.mpr hb] with x hx hbx
  exact le_of_tendsto (hx.pow 2) (Eventually.of_forall hbx)

theorem naturalSqrtMass_raw_H1 (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    (hC : ∀ i a E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i a) 2 (volume.restrict E))
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (hEloc : LocallyIntegrable (naturalCovariantEnergy d g Du) volume) :
    (∀ a E, IsCompact E → MemLp (naturalSqrtMassDerivative d g Du a) 2 (volume.restrict E)) ∧
      ∀ a, HasLocalWeakCoordinateDerivative (naturalSqrtMass d g) (naturalSqrtMassDerivative d g Du a) a := by
  have hvol : (volume : Measure (Space n)) ≪ potentialMeasure d.potential :=
    volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous
  have hfv (k : ℕ) := naturalKatoValue_local_L2 d g hMi (cutoffScale_pos k)
  have hDv (k : ℕ) (a : Fin n) :=
    naturalKatoDerivative_local_L2 d g Du hu hDu hC hcomp hMi hEloc (cutoffScale_pos k) a
  have hlim := (naturalKatoValue_tendsto_ae d g).filter_mono hvol.ae_le
  have hDlim (a : Fin n) := (naturalKatoDerivative_tendsto_ae d g Du a).filter_mono hvol.ae_le
  have hDm (a : Fin n) : AEStronglyMeasurable (naturalSqrtMassDerivative d g Du a) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (locallyIntegrable_of_memLp_two_on_compacts (hDv k a)).aestronglyMeasurable) (hDlim a)
  have hDlocal (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (naturalSqrtMassDerivative d g Du a) 2 (volume.restrict E) := by
    have hm : AEStronglyMeasurable (naturalSqrtMassDerivative d g Du a) (volume.restrict E) :=
      (hDm a).mono_measure Measure.restrict_le_self
    apply (memLp_two_iff_integrable_sq hm).mpr
    apply ((locallyIntegrable_iff.mp hEloc E hE).const_mul (16/d.targetConvexityConstant)).mono' (hm.pow 2)
    filter_upwards [ae_restrict_of_ae
      ((naturalSqrtMassDerivative_energy_ae d g Du hcomp a).filter_mono hvol.ae_le)] with x hx
    change ‖naturalSqrtMassDerivative d g Du a x^2‖ ≤
      (16/d.targetConvexityConstant)*naturalCovariantEnergy d g Du x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hx
  have hdom : ∀ E : Set (Space n), IsCompact E → ∃ b : Space n → ℝ,
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
  have hB : 0 ≤ 16/d.targetConvexityConstant :=
    div_nonneg (by norm_num) d.target_convexity_pos.le
  have hDdom (a : Fin n) : ∀ E : Set (Space n), IsCompact E → ∃ b : Space n → ℝ,
      Integrable b (volume.restrict E) ∧ ∀ k, ∀ᵐ x ∂volume.restrict E,
        ‖naturalKatoDerivative d g Du (cutoffScale k) a x‖ ≤ b x := by
    intro E hE
    letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
    refine ⟨fun x => (16/d.targetConvexityConstant)*‖naturalCovariantEnergy d g Du x‖+1,
      ((locallyIntegrable_iff.mp hEloc E hE).norm.const_mul _).add (integrable_const 1), fun k => ?_⟩
    have hb := (naturalKatoDerivative_energy_ae d g Du hcomp (cutoffScale_pos k)).filter_mono hvol.ae_le
    filter_upwards [ae_restrict_of_ae hb] with x hx
    have hs : ‖naturalKatoDerivative d g Du (cutoffScale k) a x‖^2 ≤
        (16/d.targetConvexityConstant)*‖naturalCovariantEnergy d g Du x‖ := by
      simpa only [Real.norm_eq_abs, sq_abs] using (hx.2 a).trans
        (mul_le_mul_of_nonneg_left (le_abs_self _) hB)
    nlinarith [sq_nonneg (‖naturalKatoDerivative d g Du (cutoffScale k) a x‖-(1/2 : ℝ))]
  refine ⟨hDlocal, fun a => ?_⟩
  exact local_weak_derivative_of_dominated_limits
    (fun k => locallyIntegrable_of_memLp_two_on_compacts (hfv k))
    (fun k => locallyIntegrable_of_memLp_two_on_compacts (hDv k a))
    (fun k => naturalKatoValue_hasLocalWeakDerivative d g Du hu hDu hw hC hcomp hMi hEloc (cutoffScale_pos k) a)
    hlim (hDlim a) hdom (hDdom a)

end KLSConstantImprovement.ActualNaturalSqrtMass405
#print axioms KLSConstantImprovement.ActualNaturalSqrtMass405.naturalKatoValue_tendsto_ae
#print axioms KLSConstantImprovement.ActualNaturalSqrtMass405.naturalKatoDerivative_tendsto_ae
#print axioms KLSConstantImprovement.ActualNaturalSqrtMass405.naturalSqrtMass_local_L2
#print axioms KLSConstantImprovement.ActualNaturalSqrtMass405.naturalSqrtMassDerivative_energy_ae
#print axioms KLSConstantImprovement.ActualNaturalSqrtMass405.naturalSqrtMass_raw_H1
