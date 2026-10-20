import KLSConstantImprovement.ActualDensityInverseWeakCompactness405
import KLSConstantImprovement.ActualRawPoissonIdentification405
import KLSConstantImprovement.ActualSourceNaturalGaffney405
import KLSConstantImprovement.ActualSourceLimitMetricRelations405

/-! Identify the density-weighted limiting fields by their literal raw
derivative and compact Poisson equations. All local/global form domains
are paid by the actual source and the fixed Lebesgue L2 limit. The equations
remain explicit until the source-family passage supplies them. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
namespace KLSConstantImprovement.ActualDensityLimitInverseIdentification405
open KLS ActualBoundedCanonicalSource ActualDensityWeightedL2405 ActualDensityInverseWeakCompactness405
open ActualSourceRegularizedEnergyVector405 ActualSourceLimitFluxDomains405
open ActualSourceLimitMetricRelations405 ActualSourceLimitGaffneyEnergy405
open ActualRawPoissonIdentification405 ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricInverse
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

def densityLimitScalar (d : SourceData μ) (W : DensityInverseAmbient n) :
    Lp ℝ 2 (potentialMeasure d.potential) := fromVolumeL2 d.source_C1.continuous (W 0)

/-- Only the first block is used; the unused algebraic block is zero.
No actual Jacobian or its derivative is claimed by this padding. -/
def densityLimitMetricBlock (d : SourceData μ) (W : DensityInverseAmbient n) : GaffneyEnergyAmbient d :=
  WithLp.toLp 2 (Sum.elim (fun i => fromVolumeL2 d.source_C1.continuous (W i.succ)) (fun _ => 0))

def densityLimitRawGradient (d : SourceData μ) (W : DensityInverseAmbient n) : Fin n → Space n → ℝ :=
  energyLimitScalarGradient d (densityLimitMetricBlock d W)

theorem density_limit_inverse_of_raw_equations (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (W : DensityInverseAmbient n)
    (hw : ∀ i, HasLocalWeakCoordinateDerivative
      (densityLimitScalar d W) (densityLimitRawGradient d W i) i)
    (heq : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ x, ∑ a, ∑ b, (coordinateHessian d.potential x)⁻¹ a b *
        densityLimitRawGradient d W a x * coordinateDerivative ψ b x ∂potentialMeasure d.potential) =
        ∫ x, g x * ψ x ∂potentialMeasure d.potential) :
    (sourceMetricInverse d g : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      (fun x => densityLimitScalar d W x - ∫ y, densityLimitScalar d W y ∂potentialMeasure d.potential) ∧
      ∀ i, (canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential]
          (fromVolumeL2 d.source_C1.continuous (W i.succ) : Space n → ℝ) := by
  have hloc (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (densityLimitRawGradient d W i) 2 (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure
      (energyLimitScalarGradient_memLp d (densityLimitMetricBlock d W) i) d.source_C1.continuous hE
  obtain ⟨hv, hd⟩ := exists_actual_inverse_of_raw_compact_equation d g hg
    (Lp.memLp (densityLimitScalar d W)) hloc hw
    (energyLimitScalarGradient_energy_integrable d (densityLimitMetricBlock d W)) heq
  refine ⟨hv, fun i => ?_⟩
  exact (hd i).trans (energyLimitScalarGradient_raw_metric_ae d (densityLimitMetricBlock d W) i)

theorem actual_natural_mass_bound_of_density_coordinate_bound
    (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (W : DensityInverseAmbient n)
    (hgrad : ∀ i, (canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential]
        (fromVolumeL2 d.source_C1.continuous (W i.succ) : Space n → ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i : Fin n, ∀ᵐ x ∂(volume : Measure (Space n)),
      |W i.succ x| ≤ C * densityHalf d.potential x) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ n * C ^ 2 := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  have hcap (i : Fin n) : ∀ᵐ x ∂potentialMeasure d.potential,
      |fromVolumeL2 d.source_C1.continuous (W i.succ) x| ≤ C := by
    filter_upwards [fromVolumeL2_ae d.source_C1.continuous (W i.succ),
      (hb i).filter_mono hac.ae_le] with x hx hy
    rw [hx, abs_mul, abs_of_pos (show 0 < inverseDensityHalf d.potential x from Real.exp_pos _)]
    have he : inverseDensityHalf d.potential x * (C * densityHalf d.potential x) = C := by
      calc
        _ = C * (densityHalf d.potential x * inverseDensityHalf d.potential x) := by ring
        _ = _ := by rw [densityHalf_inverseDensityHalf, mul_one]
    exact (mul_le_mul_of_nonneg_left hy
      (show 0 ≤ inverseDensityHalf d.potential x from Real.exp_nonneg _)).trans_eq he
  have hflux (i : Fin n) : naturalCanonicalFlux d g i =ᵐ[potentialMeasure d.potential]
      energyLimitFlux d (densityLimitMetricBlock d W) i := by
    filter_upwards [ae_all_iff.mpr hgrad] with x hx
    exact Finset.sum_congr rfl fun a _ => congrArg
      (fun t : ℝ => canonicalMetricRoot d.potential x i a * t) (hx a)
  filter_upwards [ae_all_iff.mpr hflux, ae_all_iff.mpr hcap,
    energyLimitFlux_mass_square_ae d (densityLimitMetricBlock d W)] with x hf hc hm
  have he : sourceVectorMass d.potential (naturalCanonicalFlux d g) x =
      sourceVectorMass d.potential (energyLimitFlux d (densityLimitMetricBlock d W)) x := by
    unfold sourceVectorMass
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hf i, hf j]
  rw [he, ← hm]
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    (sq_le_sq₀ (abs_nonneg (fromVolumeL2 d.source_C1.continuous (W i.succ) x)) hC).mpr (hc i)
  simpa only [densityLimitMetricBlock, PiLp.toLp_apply, Sum.elim_inl, sq_abs,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs

end KLSConstantImprovement.ActualDensityLimitInverseIdentification405
#print axioms KLSConstantImprovement.ActualDensityLimitInverseIdentification405.density_limit_inverse_of_raw_equations
#print axioms KLSConstantImprovement.ActualDensityLimitInverseIdentification405.actual_natural_mass_bound_of_density_coordinate_bound
