import KLSConstantImprovement.ActualKatoRegularizedWeakChain405
import KLSConstantImprovement.ActualKatoCoefficientBounds405
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Every limiting nonlinear Bochner term has a paid local domain for the
actual natural inverse. The connection is kept as one aggregate, and
|F''(M)| M is bounded at fixed epsilon before metric Kato is used. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualKatoNonlinearDomains405
open KLS ActualBoundedCanonicalSource ActualKatoLocalDomains405 ActualKatoCoefficientBounds405
open ActualNaturalMassWeakDerivative405 ActualNaturalCovariantEnergy405 ActualSmoothKatoRegularizer405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceConnectionFields405
open ActualSourceNaturalHessian405 ActualSourceNaturalTargetCurvatureDomain405 ActualJointWeakBochner405
open ActualDualKatoMultiplier405 ActualSourceHessianEvolution405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
variable {n : ℕ} {μ : Measure (Space n)}

def naturalMassMetricSquare (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  (fun a => naturalMassRawDerivative d g Du a x) ⬝ᵥ
    ((coordinateHessian d.potential x)⁻¹ *ᵥ (fun a => naturalMassRawDerivative d g Du a x))

def naturalKatoMetricFlux (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (ε : ℝ) (a : Fin n) (x : Space n) : ℝ :=
  ((coordinateHessian d.potential x)⁻¹ *ᵥ (fun b => naturalKatoDerivative d g Du ε b x)) a

def naturalKatoDensity (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (ε : ℝ) (x : Space n) : ℝ :=
  2 * katoFirst ε (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) *
    sourceBochnerDensity d (naturalCanonicalFlux d g) Du x +
      katoSecond ε (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) * naturalMassMetricSquare d g Du x

theorem sourceBochnerDensity_local_integrable (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (hEloc : LocallyIntegrable (naturalCovariantEnergy d g Du) volume)
    (hΓloc : LocallyIntegrable (sourceConnectionGamma d (naturalCanonicalFlux d g)) volume) :
    LocallyIntegrable (sourceBochnerDensity d (naturalCanonicalFlux d g) Du) volume := by
  apply locallyIntegrable_iff.mpr
  intro E hE
  have hM := memLp_one_iff_integrable.mp (KLS.MemLp.restrict_volume_of_potentialMeasure
    (memLp_one_iff_integrable.mpr hMi) d.source_C1.continuous hE)
  have hP := memLp_one_iff_integrable.mp (KLS.MemLp.restrict_volume_of_potentialMeasure
    (memLp_one_iff_integrable.mpr (natural_targetCurvature_integrable d g)) d.source_C1.continuous hE)
  have hsum := ((locallyIntegrable_iff.mp hEloc E hE).add ((hM.add hP).div_const 2)).add
    ((locallyIntegrable_iff.mp hΓloc E hE).div_const 4)
  have he := (natural_Bochner_density_covariant_ae d g Du).filter_mono
    (volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous).ae_le
  apply hsum.congr
  filter_upwards [ae_restrict_of_ae he] with x hx
  exact hx.symm

theorem naturalKatoMetricFlux_local_L2 (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) {ε : ℝ}
    (hG : ∀ a E, IsCompact E → MemLp (naturalKatoDerivative d g Du ε a) 2 (volume.restrict E))
    (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (naturalKatoMetricFlux d g Du ε a) 2 (volume.restrict E) := by
  obtain ⟨hJ, _hDJ, _hwJ⟩ := actual_mongeAmpere_inverse_hasLocalWeakDerivative
    (T := sourceThirdMatrix d) d.source_C1 (d.target_smooth.of_le (by simp))
    d.gradient_lipschitz (d.hessian_ae.mono fun _ hx => hx.2.1)
    d.third_local_L2 d.third_weak_derivative
  unfold naturalKatoMetricFlux
  simp only [Matrix.mulVec, dotProduct]
  apply memLp_finsetSum Finset.univ
  intro b _
  exact (hJ a b E hE).mul (hG b E hE)

theorem naturalKatoDensity_local_integrable (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hC : ∀ i a E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i a) 2 (volume.restrict E))
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (hEloc : LocallyIntegrable (naturalCovariantEnergy d g Du) volume)
    (hΓloc : LocallyIntegrable (sourceConnectionGamma d (naturalCanonicalFlux d g)) volume)
    {ε : ℝ} (hε : 0 < ε) :
    LocallyIntegrable (naturalKatoDensity d g Du ε) volume := by
  obtain ⟨hJ, _hDJ, _hwJ⟩ := actual_mongeAmpere_inverse_hasLocalWeakDerivative
    (T := sourceThirdMatrix d) d.source_C1 (d.target_smooth.of_le (by simp))
    d.gradient_lipschitz (d.hessian_ae.mono fun _ hx => hx.2.1)
    d.third_local_L2 d.third_weak_derivative
  have hvol : (volume : Measure (Space n)) ≪ potentialMeasure d.potential :=
    volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous
  have hMn := (natural_mass_nonnegative_ae d g).filter_mono hvol.ae_le
  have hEn := (natural_covariant_energy_nonnegative_ae d g Du hcomp).filter_mono hvol.ae_le
  have hK := (natural_covariant_mass_kato_ae d g Du hcomp).filter_mono hvol.ae_le
  have hsecond : Continuous (katoSecond ε) := by
    have he : deriv (katoFirst ε) = katoSecond ε := funext fun t => (katoFirst_hasDerivAt hε t).deriv
    rw [← he]
    exact (katoFirst_contDiff hε).continuous_deriv_one
  apply locallyIntegrable_iff.mpr
  intro E hE
  let M := sourceVectorMass d.potential (naturalCanonicalFlux d g)
  let D := naturalMassMetricSquare d g Du
  let C : ℝ := 1 / (2 * Real.sqrt ε)
  have hM := memLp_one_iff_integrable.mp (KLS.MemLp.restrict_volume_of_potentialMeasure
    (memLp_one_iff_integrable.mpr hMi) d.source_C1.continuous hE)
  have hD (a : Fin n) := locallyIntegrable_iff.mp (natural_mass_derivative_local_integrable d g Du hu hDu hC a) E hE
  have hDm : AEStronglyMeasurable D (volume.restrict E) := by
    unfold D naturalMassMetricSquare
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.aestronglyMeasurable_fun_sum Finset.univ fun a _ =>
      Finset.aestronglyMeasurable_fun_sum Finset.univ fun b _ =>
        (hD a).aestronglyMeasurable.mul ((hJ a b E hE).aestronglyMeasurable.mul (hD b).aestronglyMeasurable)
  have hFtop : MemLp (fun x => katoFirst ε (M x)) ∞ (volume.restrict E) := by
    apply memLp_top_of_bound ((katoFirst_contDiff hε).continuous.comp_aestronglyMeasurable
      hM.aestronglyMeasurable) C
    filter_upwards [ae_restrict_of_ae hMn] with x hx
    rw [Real.norm_of_nonneg (katoFirst_fixed_bound hε hx).1]
    exact (katoFirst_fixed_bound hε hx).2
  have hfirst : Integrable (fun x => 2 * katoFirst ε (M x) *
      sourceBochnerDensity d (naturalCanonicalFlux d g) Du x) (volume.restrict E) := by
    have hi := (locallyIntegrable_iff.mp
      (sourceBochnerDensity_local_integrable d g Du hMi hEloc hΓloc) E hE).mul_of_top_right (hFtop.const_mul 2)
    exact hi
  have hsm : AEStronglyMeasurable (fun x => katoSecond ε (M x) * D x) (volume.restrict E) :=
    (hsecond.comp_aestronglyMeasurable hM.aestronglyMeasurable).mul hDm
  have hsec : Integrable (fun x => katoSecond ε (M x) * D x) (volume.restrict E) := by
    apply ((locallyIntegrable_iff.mp hEloc E hE).const_mul (4 * C)).mono' hsm
    filter_upwards [ae_restrict_of_ae hMn, ae_restrict_of_ae hEn,
      ae_restrict_of_ae hK, ae_restrict_of_ae d.hessian_ae] with x hmx hex hkx hHx
    have hDn : 0 ≤ D x := hHx.1.inv.posSemidef.dotProduct_mulVec_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hDn]
    calc
      _ ≤ |katoSecond ε (M x)| * (4 * M x * naturalCovariantEnergy d g Du x) :=
        mul_le_mul_of_nonneg_left hkx (abs_nonneg _)
      _ = 4 * (|katoSecond ε (M x)| * M x) * naturalCovariantEnergy d g Du x := by ring
      _ ≤ 4 * C * naturalCovariantEnergy d g Du x :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (katoSecond_mass_fixed_bound hε hmx) (by norm_num)) hex
  exact hfirst.add hsec

end KLSConstantImprovement.ActualKatoNonlinearDomains405
#print axioms KLSConstantImprovement.ActualKatoNonlinearDomains405.sourceBochnerDensity_local_integrable
#print axioms KLSConstantImprovement.ActualKatoNonlinearDomains405.naturalKatoMetricFlux_local_L2
#print axioms KLSConstantImprovement.ActualKatoNonlinearDomains405.naturalKatoDensity_local_integrable
