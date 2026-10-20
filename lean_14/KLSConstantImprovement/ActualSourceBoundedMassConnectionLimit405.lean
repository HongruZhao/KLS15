import KLSConstantImprovement.ActualSourceBoundedMassGammaDomain405
import KLSConstantImprovement.ActualSourceNaturalTargetCurvatureDomain405
import KLSConstantImprovement.ActualSquareDominatedBoundaryLimit405

/-! The actual radius limit of the signed connection balance under an
explicit bounded natural mass. Global Gamma is paid first by positive
Fatou; only then is the true mass-weighted boundary sent to zero. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualSourceBoundedMassConnectionLimit405
open KLS ActualBoundedCanonicalSource ActualSourceConnectionFields405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceBoundedMassCutoffs405
open ActualSourceCompactConnectionDomains405 ActualSourceCompactConnectionBalance405
open ActualSourceCompactConnectionAbsorption405 ActualSourceConnectionPointwise405
open ActualSourceBoundedMassGammaDomain405 ActualSourceNaturalTargetCurvatureDomain405
open ActualSquareDominatedBoundaryLimit405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_actual_boundedMass_connection_cutoffs (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C)
    (hG : Integrable (sourceConnectionGamma d (naturalCanonicalFlux d g)) (potentialMeasure d.potential)) :
    ∃ χ : ℕ → Space n → ℝ,
      (∀ k, ContDiff ℝ 1 (χ k) ∧ HasCompactSupport (χ k) ∧ ∀ x, χ k x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, Tendsto (fun k => χ k x) atTop (𝓝 1)) ∧
      (∀ k, Integrable (fun x => χ k x * sourceConnectionBoundary d (χ k) (naturalCanonicalFlux d g) x)
        (potentialMeasure d.potential)) ∧
      Tendsto (fun k => ∫ x, |χ k x * sourceConnectionBoundary d (χ k) (naturalCanonicalFlux d g) x|
        ∂potentialMeasure d.potential) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ x, χ k x * sourceConnectionBoundary d (χ k) (naturalCanonicalFlux d g) x
        ∂potentialMeasure d.potential) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let u := naturalCanonicalFlux d g
  let ν := potentialMeasure d.potential
  obtain ⟨χ, hχ, hlim, hEi, hElim⟩ := exists_actual_mass_weighted_energy_cutoffs d g hC hM
  have huTop (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (u i) ∞ (volume.restrict E) :=
    naturalCanonicalFlux_local_top_of_mass_bound d g hC hM i hE
  have hBi (k : ℕ) : Integrable (fun x => χ k x * sourceConnectionBoundary d (χ k) u x) ν := by
    have hs := integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun a _ =>
        (compact_connection_boundary_summand_memLp d huTop (hχ k).1 (hχ k).2.1 i j a).integrable (by norm_num))))
    simpa only [sourceConnectionBoundary, Finset.mul_sum] using hs
  have he0 (k : ℕ) : ∀ᵐ x ∂ν, 0 ≤ sourceVectorMass d.potential u x * inverseHessianGradientForm d.potential (χ k) x := by
    filter_upwards [d.hessian_ae_source, sourceVectorMass_nonnegative_ae d u] with x hp hm
    exact mul_nonneg hm (inverseHessianGradientForm_nonneg_at (χ k) hp.1)
  have hs (k : ℕ) : ∀ᵐ x ∂ν, (χ k x * sourceConnectionBoundary d (χ k) u x) ^ 2 ≤
      (sourceVectorMass d.potential u x * inverseHessianGradientForm d.potential (χ k) x) *
        sourceConnectionGamma d u x := by
    filter_upwards [sourceConnectionBoundary_square_le_ae d u (χ k)] with x hb
    have hχsq : χ k x ^ 2 ≤ 1 := by obtain ⟨hlo, hhi⟩ := (hχ k).2.2 x; nlinarith
    have hc : (χ k x * sourceConnectionBoundary d (χ k) u x) ^ 2 ≤ sourceConnectionBoundary d (χ k) u x ^ 2 := by
      rw [mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) hχsq
    exact hc.trans (by simpa only [mul_comm, mul_left_comm, mul_assoc] using hb)
  obtain ⟨habs, hsign⟩ := integral_tendsto_zero_of_square_domination hBi hEi hG he0
    (sourceConnectionGamma_nonnegative_ae d u) hs hElim
  exact ⟨χ, hχ, hlim, hBi, habs, hsign⟩

theorem actual_connectionCross_integrable_of_mass_bound (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x)).IsSymm)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (hQi : Integrable (sourceVectorJacobianEnergy Du) (potentialMeasure d.potential)) :
    Integrable (sourceConnectionCross d (naturalCanonicalFlux d g) Du) (potentialMeasure d.potential) := by
  let u := naturalCanonicalFlux d g
  let ν := potentialMeasure d.potential
  have hG := (actual_Gamma_integrable_of_bounded_natural_mass d g hC hM Du hu hDu hw hcomp hMi hQi).1
  obtain ⟨χ, hχ, hlim, _, _⟩ := exists_actual_mass_weighted_energy_cutoffs d g hC hM
  have hXi (k : ℕ) : Integrable (fun x => χ k x ^ 2 * sourceConnectionCross d u Du x) ν :=
    (compact_connection_fields_integrable d g hC hM Du hu hDu hw (hχ k).1 (hχ k).2.1).1
  have hXm : AEStronglyMeasurable (sourceConnectionCross d u Du) ν :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hXi k).aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        simpa only [one_pow, one_mul] using ((hlim x).pow 2).mul_const (sourceConnectionCross d u Du x))
  apply ((hG.const_mul (1/4)).add (hQi.const_mul 4)).mono' hXm
  filter_upwards [sourceConnectionCross_abs_le_ae d u Du hcomp] with x hx
  simpa only [Real.norm_eq_abs, Pi.add_apply, u] using hx

theorem integral_actual_global_connection_balance_of_mass_bound (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x)).IsSymm)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (hQi : Integrable (sourceVectorJacobianEnergy Du) (potentialMeasure d.potential)) :
    (∫ x, sourceConnectionTarget d (naturalCanonicalFlux d g) x +
        sourceConnectionGamma d (naturalCanonicalFlux d g) x ∂potentialMeasure d.potential) =
      (∫ x, sourceVectorMass d.potential (naturalCanonicalFlux d g) x ∂potentialMeasure d.potential) -
        (∫ x, sourceConnectionCross d (naturalCanonicalFlux d g) Du x ∂potentialMeasure d.potential) := by
  let u := naturalCanonicalFlux d g
  let ν := potentialMeasure d.potential
  have hG : Integrable (sourceConnectionGamma d u) ν :=
    (actual_Gamma_integrable_of_bounded_natural_mass d g hC hM Du hu hDu hw hcomp hMi hQi).1
  have hP : Integrable (sourceConnectionTarget d u) ν := natural_targetCurvature_integrable d g
  have hX : Integrable (sourceConnectionCross d u Du) ν :=
    actual_connectionCross_integrable_of_mass_bound d g hC hM Du hu hDu hw hcomp hMi hQi
  have hPG : Integrable (fun x => sourceConnectionTarget d u x + sourceConnectionGamma d u x) ν := hP.add hG
  obtain ⟨χ, hχ, hlim, _, _, hBlim⟩ := exists_actual_boundedMass_connection_cutoffs d g hC hM hG
  have hleft := (integral_cutoff_square_tendsto (fun k => (hχ k).1.continuous)
    (fun k => (hχ k).2.2) hlim hPG).2
  have hMlim := (integral_cutoff_square_tendsto (fun k => (hχ k).1.continuous)
    (fun k => (hχ k).2.2) hlim hMi).2
  have hXlim := (integral_cutoff_square_tendsto (fun k => (hχ k).1.continuous)
    (fun k => (hχ k).2.2) hlim hX).2
  have hbalance (k : ℕ) := integral_actual_compact_connection_balance d g hC hM Du hu hDu hw (hχ k).1 (hχ k).2.1
  have hright : Tendsto (fun k => ∫ x, χ k x ^ 2 *
      (sourceConnectionTarget d u x + sourceConnectionGamma d u x) ∂ν) atTop
      (𝓝 ((∫ x, sourceVectorMass d.potential u x ∂ν) - (∫ x, sourceConnectionCross d u Du x ∂ν))) := by
    have hh := ((hMlim.sub hXlim).sub (hBlim.const_mul 2)).congr (fun k => (hbalance k).symm)
    simpa only [u, ν, mul_zero, sub_zero] using hh
  exact tendsto_nhds_unique hleft hright

end KLSConstantImprovement.ActualSourceBoundedMassConnectionLimit405
#print axioms KLSConstantImprovement.ActualSourceBoundedMassConnectionLimit405.exists_actual_boundedMass_connection_cutoffs
#print axioms KLSConstantImprovement.ActualSourceBoundedMassConnectionLimit405.actual_connectionCross_integrable_of_mass_bound
#print axioms KLSConstantImprovement.ActualSourceBoundedMassConnectionLimit405.integral_actual_global_connection_balance_of_mass_bound
