import KLSConstantImprovement.ActualSourceNaturalGaffney405
import KLSConstantImprovement.ActualWeakCanonicalMetricCutoffs

/-! Consequences of a separately proved bounded natural mass.  The mass
bound remains explicit here.  It supplies local L-infinity vector products
and the actual mass-weighted vanishing cutoff error needed for connection
integration; neither conclusion is inferred from first-order energy alone. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceBoundedMassCutoffs405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405
open ActualSourceLocalizedGaffney405 ActualSourceLimitFluxDomains405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricOrdinaryGraph ActualWeakCanonicalMetricInverse
open ActualWeakCanonicalMetricCutoffs ActualSourceMetricFaithfulness405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem naturalCanonicalMass_square_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    (fun x => ∑ i : Fin n, canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x ^ 2)
      =ᵐ[potentialMeasure d.potential] sourceVectorMass d.potential (naturalCanonicalFlux d g) := by
  filter_upwards [d.hessian_ae_source] with x hp
  let S := canonicalMetricUnroot d.potential x
  let u : Fin n → ℝ := fun i => naturalCanonicalFlux d g i x
  let v : Fin n → ℝ := fun i => canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x
  have hu : S *ᵥ u = v := by
    change canonicalMetricUnroot d.potential x *ᵥ (canonicalMetricRoot d.potential x *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, canonicalMetricUnroot_mul_root_at hp.1, Matrix.one_mulVec]
  have he : (S *ᵥ u) ⬝ᵥ (S *ᵥ u) = u ⬝ᵥ (coordinateHessian d.potential x *ᵥ u) := by
    rw [← Matrix.dotProduct_transpose_mulVec S u (S *ᵥ u), Matrix.mulVec_mulVec,
      canonicalMetricUnroot_gram_at hp.1]
  calc
    _ = v ⬝ᵥ v := by simp only [v, dotProduct, pow_two]
    _ = (S *ᵥ u) ⬝ᵥ (S *ᵥ u) := by rw [hu]
    _ = _ := he
    _ = _ := (KLS.matrix_quadratic_sum_eq_dotProduct
      (coordinateHessian d.potential x) u).symm

theorem naturalCanonicalGradient_memLp_top_of_mass_bound (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential, sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C)
    (i : Fin n) :
    MemLp (canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g)) ∞
      (potentialMeasure d.potential) := by
  apply memLp_top_of_bound (Lp.memLp _).aestronglyMeasurable (C + 1)
  filter_upwards [naturalCanonicalMass_square_ae d g, hM] with x hs hm
  have hi : canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x ^ 2 ≤ C := by
    calc
      _ ≤ ∑ a : Fin n, canonicalMetricGradient d.potential a (sourceMetricInverseH1 d g) x ^ 2 :=
        Finset.single_le_sum (fun a _ => sq_nonneg (canonicalMetricGradient d.potential a (sourceMetricInverseH1 d g) x))
          (Finset.mem_univ i)
      _ ≤ C := hs.le.trans hm
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs (canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x),
    abs_nonneg (canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x), sq_nonneg C]

theorem naturalCanonicalFlux_local_top_of_mass_bound (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential, sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C)
    (i : Fin n) {E : Set (Space n)} (hE : IsCompact E) :
    MemLp (naturalCanonicalFlux d g i) ∞ (volume.restrict E) := by
  have hv (a : Fin n) : MemLp (canonicalMetricGradient d.potential a (sourceMetricInverseH1 d g)) ∞
      (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure
      (naturalCanonicalGradient_memLp_top_of_mass_bound d g hC hM a) d.source_C1.continuous hE
  exact memLp_finsetSum Finset.univ fun a _ => (actualRoot_entry_top_on_compact d hE i a).mul (hv a)

theorem exists_actual_mass_weighted_energy_cutoffs (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential, sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C) :
    ∃ χ : ℕ → Space n → ℝ,
      (∀ k, ContDiff ℝ 1 (χ k) ∧ HasCompactSupport (χ k) ∧ ∀ x, χ k x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, Tendsto (fun k => χ k x) atTop (𝓝 1)) ∧
      (∀ k, Integrable (fun x => sourceVectorMass d.potential (naturalCanonicalFlux d g) x *
        inverseHessianGradientForm d.potential (χ k) x) (potentialMeasure d.potential)) ∧
      Tendsto (fun k => ∫ x, sourceVectorMass d.potential (naturalCanonicalFlux d g) x *
        inverseHessianGradientForm d.potential (χ k) x ∂potentialMeasure d.potential) atTop (𝓝 0) := by
  obtain ⟨x₀, _, hc, _, hp, _, _, hEi, hEconv⟩ := d.exists_metric_energy_cutoffs
  let χ := hessianMetricCutoffSequence d.potential x₀
  have hMnonneg : ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ sourceVectorMass d.potential (naturalCanonicalFlux d g) x := by
    filter_upwards [naturalCanonicalMass_square_ae d g] with x hx
    rw [← hx]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hmassI : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential) :=
    (integrable_finsetSum Finset.univ (fun i _ =>
      (Lp.memLp (canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g))).integrable_sq)).congr
      (naturalCanonicalMass_square_ae d g)
  have hMnorm : ∀ᵐ x ∂potentialMeasure d.potential, ‖sourceVectorMass d.potential (naturalCanonicalFlux d g) x‖ ≤ C := by
    filter_upwards [hMnonneg, hM] with x hx hy
    rwa [Real.norm_of_nonneg hx]
  have hprod (k : ℕ) : Integrable (fun x => sourceVectorMass d.potential (naturalCanonicalFlux d g) x *
      inverseHessianGradientForm d.potential (χ k) x) (potentialMeasure d.potential) :=
    (hEi k).bdd_mul hmassI.aestronglyMeasurable hMnorm
  have hePos (k : ℕ) : ∀ᵐ x ∂potentialMeasure d.potential,
      0 ≤ inverseHessianGradientForm d.potential (χ k) x :=
    d.hessian_ae_source.mono fun x hx => inverseHessianGradientForm_nonneg_at (χ k) hx.1
  refine ⟨χ, hc, hp, hprod, ?_⟩
  apply squeeze_zero
    (fun k => integral_nonneg_of_ae (by
      filter_upwards [hMnonneg, hePos k] with x hx hy
      exact mul_nonneg hx hy))
    (fun k => ?_)
    (show Tendsto (fun k => C * ∫ x, inverseHessianGradientForm d.potential (χ k) x
      ∂potentialMeasure d.potential) atTop (𝓝 0) by simpa only [mul_zero] using hEconv.const_mul C)
  rw [← integral_const_mul]
  apply integral_mono_ae (hprod k) ((hEi k).const_mul C)
  filter_upwards [hM, hePos k] with x hx hy
  exact mul_le_mul_of_nonneg_right hx hy

end KLSConstantImprovement.ActualSourceBoundedMassCutoffs405
#print axioms KLSConstantImprovement.ActualSourceBoundedMassCutoffs405.naturalCanonicalMass_square_ae
#print axioms KLSConstantImprovement.ActualSourceBoundedMassCutoffs405.naturalCanonicalGradient_memLp_top_of_mass_bound
#print axioms KLSConstantImprovement.ActualSourceBoundedMassCutoffs405.naturalCanonicalFlux_local_top_of_mass_bound
#print axioms KLSConstantImprovement.ActualSourceBoundedMassCutoffs405.exists_actual_mass_weighted_energy_cutoffs
