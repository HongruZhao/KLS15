import KLSConstantImprovement.ActualNaturalFluxTargetNeumann405
import KLSConstantImprovement.ActualCompactRawH1L2Tests405

/-! Actual unbounded compact H1 row tests and the local natural-flux
energy identity. Every nonlinear factor is admitted through its genuine
weak derivative and local L2 domain, without a natural mass bound. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualNaturalRowEnergyLocal405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405
open ActualNaturalFluxTargetNeumann405 ActualNaturalFluxRowEquation405
open ActualSourceNaturalTargetCurvatureDomain405 ActualSourceLocalizedGaffney405
open ActualCompactRawH1L2Tests405 ActualPotentialWeakTests405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
variable {n : ℕ} {μ : Measure (Space n)}

theorem natural_row_unbounded_compact_rawH1_test (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i j) j)
    {Dg : Space n → ℝ} {j : Fin n}
    (hgw : HasLocalWeakCoordinateDerivative (g : Space n → ℝ) Dg j)
    (hDg : MemLp Dg 2 (potentialMeasure d.potential))
    {f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E))
    (hc : HasCompactSupport f)
    (hF : ∀ a E, IsCompact E → MemLp (F a) 2 (volume.restrict E))
    (hFw : ∀ a, HasLocalWeakCoordinateDerivative f (F a) a) :
    (∀ i, Integrable (fun x => Du i j x * F i x) (potentialMeasure d.potential)) ∧
      Integrable (fun x => (Dg x - naturalCanonicalRawGradient d g j x) * f x)
        (potentialMeasure d.potential) ∧
      (∑ i : Fin n, ∫ x, Du i j x * F i x ∂potentialMeasure d.potential) =
        ∫ x, (Dg x - naturalCanonicalRawGradient d g j x) * f x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hp := naturalCanonicalRawGradient_memLp d g j
  have hDr : MemLp (fun x => Dg x - naturalCanonicalRawGradient d g j x) 2
      (potentialMeasure d.potential) := hDg.sub hp
  apply potential_divergence_compact_raw_H1_L2_test d
    (fun i E hE => hDu i j E hE)
    (fun E hE => KLS.MemLp.restrict_volume_of_potentialMeasure hDr d.source_C1.continuous hE)
    (fun ψ hψ hψc => ?_) hf hc hF hFw
  have he := natural_flux_differentiated_compact_equation d hn g hg Du hu hDu hw hgw
    (hψ.of_le (by norm_num)) hψc
  have hHi (i : Fin n) : Integrable (fun x => coordinateHessian d.potential x i j *
      naturalCanonicalFlux d g i x * ψ x) (potentialMeasure d.potential) :=
    integrable_raw_mul_compact_potential d.source_C1.continuous
      (locallyIntegrable_of_memLp_two_on_compacts fun E hE =>
        (KLS.MemLp.restrict_volume_of_potentialMeasure (d.hessian_entry_memLp i j ∞)
          d.source_C1.continuous hE).mul (hu i E hE)) hψ.continuous hψc
  have hψ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ.continuous hψc
  have hDi : Integrable (fun x => Dg x * ψ x) (potentialMeasure d.potential) := hDg.integrable_mul hψ2
  have hpi : Integrable (fun x => naturalCanonicalRawGradient d g j x * ψ x)
      (potentialMeasure d.potential) := hp.integrable_mul hψ2
  have hmass : (∑ i : Fin n, ∫ x, coordinateHessian d.potential x i j * naturalCanonicalFlux d g i x * ψ x
      ∂potentialMeasure d.potential) =
      ∫ x, naturalCanonicalRawGradient d g j x * ψ x ∂potentialMeasure d.potential := by
    rw [← integral_finsetSum Finset.univ (fun i _ => hHi i)]
    apply integral_congr_ae
    filter_upwards [hessian_column_flux_eq_rawGradient_ae d g j] with x hx
    rw [← Finset.sum_mul, hx]
  have hsplit : (∫ x, (Dg x - naturalCanonicalRawGradient d g j x) * ψ x ∂potentialMeasure d.potential) =
      (∫ x, Dg x * ψ x ∂potentialMeasure d.potential) -
        ∫ x, naturalCanonicalRawGradient d g j x * ψ x ∂potentialMeasure d.potential := by
    rw [← integral_sub hDi hpi]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [hmass] at he
  rw [hsplit]
  linarith

def naturalRowBoundary (u : Fin n → Space n → ℝ)
    (Du : Fin n → Fin n → Space n → ℝ) (α : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ j : Fin n, ∑ i : Fin n, coordinateDerivative α i x * Du i j x * u j x

theorem natural_local_row_energy (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i j) j)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (hQi : Integrable (sourceVectorJacobianEnergy Du) (potentialMeasure d.potential))
    (Dg : Fin n → Space n → ℝ)
    (hgw : ∀ j, HasLocalWeakCoordinateDerivative (g : Space n → ℝ) (Dg j) j)
    (hDg : ∀ j, MemLp (Dg j) 2 (potentialMeasure d.potential))
    {α : Space n → ℝ} (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α) :
    Integrable (naturalRowBoundary (naturalCanonicalFlux d g) Du α) (potentialMeasure d.potential) ∧
      Integrable (fun x => α x * (∑ j : Fin n, Dg j x * naturalCanonicalFlux d g j x))
        (potentialMeasure d.potential) ∧
      (∫ x, α x * sourceVectorJacobianEnergy Du x ∂potentialMeasure d.potential) +
        (∫ x, α x * sourceVectorMass d.potential (naturalCanonicalFlux d g) x ∂potentialMeasure d.potential) +
        (∫ x, naturalRowBoundary (naturalCanonicalFlux d g) Du α x ∂potentialMeasure d.potential) =
          ∫ x, α x * (∑ j : Fin n, Dg j x * naturalCanonicalFlux d g j x) ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let ν := potentialMeasure d.potential
  let u := naturalCanonicalFlux d g
  let p := naturalCanonicalRawGradient d g
  let F (j i : Fin n) (x : Space n) := coordinateDerivative α i x * u j x + α x * Du j i x
  have hαloc (E : Set (Space n)) (hE : IsCompact E) : MemLp α 2 (volume.restrict E) :=
    memLp_continuous_on_compact hα.continuous hE
  have hDα (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (coordinateDerivative α i) 2 (volume.restrict E) :=
    memLp_continuous_on_compact (contDiff_coordinateDerivative hα (m := 0) (by norm_num) i).continuous hE
  have hf (j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => α x * u j x) 2 (volume.restrict E) :=
    memLp_continuous_mul_on_compact hE (hu j E hE) hα.continuous
  have hF (j i : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (F j i) 2 (volume.restrict E) := by
    have h1 := memLp_continuous_mul_on_compact hE (hu j E hE)
      (contDiff_coordinateDerivative hα (m := 0) (by norm_num) i).continuous
    have h2 := memLp_continuous_mul_on_compact hE (hDu j i E hE) hα.continuous
    exact h1.add h2
  have hFw (j i : Fin n) : HasLocalWeakCoordinateDerivative (fun x => α x * u j x) (F j i) i :=
    (hasLocalWeakCoordinateDerivative_of_contDiff hα i).mul (hw j i)
      hαloc (hu j) (hDα i) (hDu j i)
  have hr (j : Fin n) := natural_row_unbounded_compact_rawH1_test d hn g hg Du hu hDu hw
    (hgw j) (hDg j) (hf j) hc.mul_right (hF j) (hFw j)
  have hαtop : MemLp α ∞ ν := hα.continuous.memLp_of_hasCompactSupport hc
  have hQ : Integrable (fun x => α x * sourceVectorJacobianEnergy Du x) ν := hQi.mul_of_top_right hαtop
  have hM : Integrable (fun x => α x * sourceVectorMass d.potential u x) ν := hMi.mul_of_top_right hαtop
  have hAij (j i : Fin n) : Integrable
      (fun x => coordinateDerivative α i x * Du i j x * u j x) ν := by
    have hl : LocallyIntegrable (fun x => Du i j x * u j x) volume := by
      apply locallyIntegrable_iff.mpr
      intro E hE
      exact (hDu i j E hE).integrable_mul (hu j E hE)
    have ht := integrable_raw_mul_compact_potential d.source_C1.continuous hl
      (contDiff_coordinateDerivative hα (m := 0) (by norm_num) i).continuous
      (hasCompactSupport_coordinateDerivative hc i)
    exact ht.congr (Eventually.of_forall fun x => by dsimp only; ring)
  have hA : Integrable (naturalRowBoundary u Du α) ν :=
    integrable_finsetSum Finset.univ fun j _ => integrable_finsetSum Finset.univ fun i _ => hAij j i
  have hRj (j : Fin n) : Integrable (fun x => α x * (Dg j x * u j x)) ν := by
    have hl : LocallyIntegrable (fun x => Dg j x * u j x) volume := by
      apply locallyIntegrable_iff.mpr
      intro E hE
      exact (KLS.MemLp.restrict_volume_of_potentialMeasure (hDg j) d.source_C1.continuous hE).integrable_mul (hu j E hE)
    have ht := integrable_raw_mul_compact_potential d.source_C1.continuous hl hα.continuous hc
    exact ht.congr (Eventually.of_forall fun x => mul_comm _ _)
  have hR : Integrable (fun x => α x * (∑ j : Fin n, Dg j x * u j x)) ν := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ fun j _ => hRj j
  have hleft : (∑ j : Fin n, ∑ i : Fin n, ∫ x, Du i j x * F j i x ∂ν) =
      (∫ x, α x * sourceVectorJacobianEnergy Du x ∂ν) +
        ∫ x, naturalRowBoundary u Du α x ∂ν := by
    have hinner (j : Fin n) : (∑ i : Fin n, ∫ x, Du i j x * F j i x ∂ν) =
        ∫ x, ∑ i : Fin n, Du i j x * F j i x ∂ν :=
      (integral_finsetSum Finset.univ fun i _ => (hr j).1 i).symm
    simp_rw [hinner]
    rw [← integral_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ fun i _ => (hr j).1 i), ← integral_add hQ hA]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      have hpoint (j i : Fin n) : Du i j x * F j i x =
          α x * (Du j i x * Du i j x) + coordinateDerivative α i x * Du i j x * u j x := by
        dsimp only [F]
        ring
      simp_rw [hpoint]
      simp only [sourceVectorJacobianEnergy, naturalRowBoundary, Finset.sum_add_distrib, Finset.mul_sum]
  have hright : (∑ j : Fin n, ∫ x, (Dg j x - p j x) * (α x * u j x) ∂ν) =
      (∫ x, α x * (∑ j : Fin n, Dg j x * u j x) ∂ν) -
        ∫ x, α x * sourceVectorMass d.potential u x ∂ν := by
    rw [← integral_finsetSum Finset.univ (fun j _ => (hr j).2.1), ← integral_sub hR hM]
    apply integral_congr_ae
    filter_upwards [hessian_mul_naturalCanonicalFlux_ae d g] with x hx
    have he : (∑ j : Fin n, p j x * u j x) = sourceVectorMass d.potential u x := by
      have hp (j : Fin n) : p j x = (coordinateHessian d.potential x *ᵥ (fun i => u i x)) j :=
        (congrFun hx j).symm
      simp_rw [hp]
      simp only [sourceVectorMass, Matrix.mulVec, dotProduct, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    calc
      _ = α x * ((∑ j : Fin n, Dg j x * u j x) - ∑ j : Fin n, p j x * u j x) := by
        simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by rw [he]; ring
  have hsum : (∑ j : Fin n, ∑ i : Fin n, ∫ x, Du i j x * F j i x ∂ν) =
      ∑ j : Fin n, ∫ x, (Dg j x - p j x) * (α x * u j x) ∂ν :=
    Finset.sum_congr rfl fun j _ => (hr j).2.2
  rw [hleft, hright] at hsum
  exact ⟨hA, hR, by linarith⟩

end KLSConstantImprovement.ActualNaturalRowEnergyLocal405
#print axioms KLSConstantImprovement.ActualNaturalRowEnergyLocal405.natural_row_unbounded_compact_rawH1_test
#print axioms KLSConstantImprovement.ActualNaturalRowEnergyLocal405.natural_local_row_energy
