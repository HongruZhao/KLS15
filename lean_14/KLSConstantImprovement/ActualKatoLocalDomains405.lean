import KLSConstantImprovement.ActualKatoFluxAlgebra405
import KLSConstantImprovement.ActualDualKatoMultiplier405

/-! Actual local L2 domains for smooth square-root regularization of the
natural inverse mass. The derivative energy is uniform in the positive
regularization parameter. These are literal raw functions, before the
nonlinear weak derivative is passed through the common compact cutoffs. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualKatoLocalDomains405
open KLS ActualBoundedCanonicalSource ActualKatoFluxAlgebra405 ActualSmoothKatoRegularizer405
open ActualNaturalMassWeakDerivative405 ActualNaturalCovariantEnergy405 ActualCovariantKatoAlgebra405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceConnectionFields405
open ActualSourceConnectionPointwise405 ActualCompatibleConnectionYoung405 ActualSourceNaturalHessian405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def naturalKatoValue (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (ε : ℝ) (x : Space n) : ℝ :=
  katoRegularizer ε (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)

def naturalKatoDerivative (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (ε : ℝ) (a : Fin n) (x : Space n) : ℝ :=
  katoFirst ε (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) * naturalMassRawDerivative d g Du a x

theorem katoRegularizer_square_bound {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    katoRegularizer ε t ^ 2 ≤ |t| + ε := by
  rw [katoRegularizer_square]
  unfold katoRho
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [sq_abs t, mul_nonneg (abs_nonneg t) hε.le]

theorem natural_mass_nonnegative_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ sourceVectorMass d.potential (naturalCanonicalFlux d g) x := by
  filter_upwards [d.hessian_ae_source] with x hx
  rw [sourceVectorMass, matrix_quadratic_sum_eq_dotProduct]
  exact hx.1.posSemidef.dotProduct_mulVec_nonneg _

theorem natural_covariant_energy_nonnegative_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ naturalCovariantEnergy d g Du x := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, hcomp.filter_mono hac.ae_le,
    sourceThirdAlong_isSymm_ae d (naturalCanonicalFlux d g)] with x hH hB hN
  have hC := covariantHessian_isSymm (coordinateHessian d.potential x)
    (Matrix.of (fun i a => Du i a x)) (sourceThirdAlong d (naturalCanonicalFlux d g) x) hB hN
  change 0 ≤ ((coordinateHessian d.potential x)⁻¹ * naturalCovariantHessian d g Du x *
    (coordinateHessian d.potential x)⁻¹ * naturalCovariantHessian d g Du x).trace
  rw [← whitened_connection_square (coordinateHessian d.potential x)
    (naturalCovariantHessian d g Du x) hH.1 hC]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem naturalKatoDerivative_energy_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (fun a => naturalKatoDerivative d g Du ε a x) ⬝ᵥ
          ((coordinateHessian d.potential x)⁻¹ *ᵥ (fun a => naturalKatoDerivative d g Du ε a x)) ≤
        naturalCovariantEnergy d g Du x ∧
      ∀ a : Fin n, naturalKatoDerivative d g Du ε a x ^ 2 ≤
        (16 / d.targetConvexityConstant) * naturalCovariantEnergy d g Du x := by
  filter_upwards [d.hessian_ae_source, natural_mass_nonnegative_ae d g,
    natural_covariant_energy_nonnegative_ae d g Du hcomp,
    natural_covariant_mass_kato_ae d g Du hcomp] with x hH hM hE hK
  have he := regularized_mass_gradient_energy (coordinateHessian d.potential x)
    hH.1 hε hM hE (fun a => naturalMassRawDerivative d g Du a x) hK
  refine ⟨he.1, fun a => (he.2 a).trans ?_⟩
  have hb := coordinateHessian_entry_bound_of_gradient_lipschitz d.gradient_lipschitz x a a
  exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans hb) hE

theorem naturalKatoValue_local_L2 (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    {ε : ℝ} (hε : 0 < ε) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (naturalKatoValue d g ε) 2 (volume.restrict E) := by
  letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
  have hM := (memLp_one_iff_integrable.mp (KLS.MemLp.restrict_volume_of_potentialMeasure
    (memLp_one_iff_integrable.mpr hMi) d.source_C1.continuous hE))
  have hm : AEStronglyMeasurable (naturalKatoValue d g ε) (volume.restrict E) :=
    (katoRegularizer_contDiff hε).continuous.comp_aestronglyMeasurable hM.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (hM.norm.add (integrable_const ε)).mono' (hm.pow 2)
  exact Eventually.of_forall fun x => by
    change ‖naturalKatoValue d g ε x ^ 2‖ ≤ ‖sourceVectorMass d.potential (naturalCanonicalFlux d g) x‖ + ε
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    exact katoRegularizer_square_bound hε _

theorem naturalKatoDerivative_local_L2 (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hC : ∀ i a E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i a) 2 (volume.restrict E))
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (hEloc : LocallyIntegrable (naturalCovariantEnergy d g Du) volume)
    {ε : ℝ} (hε : 0 < ε) (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (naturalKatoDerivative d g Du ε a) 2 (volume.restrict E) := by
  have hM := memLp_one_iff_integrable.mp (KLS.MemLp.restrict_volume_of_potentialMeasure
    (memLp_one_iff_integrable.mpr hMi) d.source_C1.continuous hE)
  have hD := locallyIntegrable_iff.mp (natural_mass_derivative_local_integrable d g Du hu hDu hC a) E hE
  have hm : AEStronglyMeasurable (naturalKatoDerivative d g Du ε a) (volume.restrict E) :=
    ((ActualDualKatoMultiplier405.katoFirst_contDiff hε).continuous.comp_aestronglyMeasurable
      hM.aestronglyMeasurable).mul hD.aestronglyMeasurable
  have hvol : (volume : Measure (Space n)) ≪ potentialMeasure d.potential :=
    volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous
  have hb := (naturalKatoDerivative_energy_ae d g Du hcomp hε).filter_mono hvol.ae_le
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply ((locallyIntegrable_iff.mp hEloc E hE).const_mul (16 / d.targetConvexityConstant)).mono' (hm.pow 2)
  filter_upwards [ae_restrict_of_ae hb] with x hx
  change ‖naturalKatoDerivative d g Du ε a x ^ 2‖ ≤ (16 / d.targetConvexityConstant) * naturalCovariantEnergy d g Du x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hx.2 a

end KLSConstantImprovement.ActualKatoLocalDomains405
#print axioms KLSConstantImprovement.ActualKatoLocalDomains405.katoRegularizer_square_bound
#print axioms KLSConstantImprovement.ActualKatoLocalDomains405.natural_covariant_energy_nonnegative_ae
#print axioms KLSConstantImprovement.ActualKatoLocalDomains405.naturalKatoDerivative_energy_ae
#print axioms KLSConstantImprovement.ActualKatoLocalDomains405.naturalKatoValue_local_L2
#print axioms KLSConstantImprovement.ActualKatoLocalDomains405.naturalKatoDerivative_local_L2
