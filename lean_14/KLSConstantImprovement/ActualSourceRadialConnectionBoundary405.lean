import KLSConstantImprovement.ActualSourceConnectionPointwise405
import KLSConstantImprovement.ActualSourceCompactConnectionDomains405
import KLSConstantImprovement.ActualRadialMatrixCalculus405
import KLSConstantImprovement.ActualSquareDominatedBoundaryLimit405

/-! Actual global domains and spatial boundary limits at a fixed Euclidean
radial scale.  The natural flux need not have bounded mass.  The already
proved L1 third-Gram entries and the bounded radial vector pay the global
curvature before the spatial cutoff is removed.  No uniform radial-scale
estimate or natural inverse-mass bound is asserted. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualSourceRadialConnectionBoundary405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405
open ActualSourceConnectionFields405 ActualSourceConnectionPointwise405
open ActualSourceCompactConnectionDomains405 ActualSourceCurvatureDomains405
open ActualSourceHessianEvolution405 ActualSourceLocalizedGaffney405
open ActualSourceLimitFluxDomains405 ActualSourceBoundedMassCutoffs405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricInverse
open ActualWeakCanonicalMetricCutoffs ActualRadialMatrixCalculus405
open ActualSquareDominatedBoundaryLimit405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def radialBoundedVector (δ : ℝ) (u : Fin n → Space n → ℝ)
    (i : Fin n) (x : Space n) : ℝ :=
  u i x / Real.sqrt (radialDenom δ (fun a => u a x))

theorem naturalCanonicalFlux_local_L2 (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E) := by
  apply memLp_finsetSum Finset.univ
  intro a _
  exact (actualRoot_entry_top_on_compact d hE i a).mul
    (KLS.MemLp.restrict_volume_of_potentialMeasure (Lp.memLp _)
      d.source_C1.continuous hE)

theorem naturalCanonicalFlux_aestronglyMeasurable (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (i : Fin n) :
    AEStronglyMeasurable (naturalCanonicalFlux d g i) (potentialMeasure d.potential) := by
  exact (locallyIntegrable_of_memLp_two_on_compacts
    (naturalCanonicalFlux_local_L2 d g i)).aestronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous _ _)

theorem radialBoundedVector_product {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Fin n → Space n → ℝ) (i j : Fin n) (x : Space n) :
    radialBoundedVector δ u i x * radialBoundedVector δ u j x =
      u i x * u j x / radialDenom δ (fun a => u a x) := by
  have hd := (radialDenom_positive hδ (fun a => u a x)).le
  simp only [radialBoundedVector, div_mul_div_comm, ← pow_two, Real.sq_sqrt hd]

theorem radialBoundedVector_memLp_top_source (d : SourceData μ)
    {δ : ℝ} (hδ : 0 < δ) {u : Fin n → Space n → ℝ}
    (hu : ∀ i, AEStronglyMeasurable (u i) (potentialMeasure d.potential)) (i : Fin n) :
    MemLp (radialBoundedVector δ u i) ∞ (potentialMeasure d.potential) := by
  have hden : AEStronglyMeasurable
      (fun x => radialDenom δ (fun a => u a x)) (potentialMeasure d.potential) := by
    exact aestronglyMeasurable_const.add
      ((Finset.aestronglyMeasurable_fun_sum Finset.univ (fun a _ => (hu a).pow 2)).const_mul δ)
  have hm : AEStronglyMeasurable (radialBoundedVector δ u i) (potentialMeasure d.potential) :=
    ((hu i).aemeasurable.div (Real.continuous_sqrt.comp_aestronglyMeasurable hden).aemeasurable).aestronglyMeasurable
  apply memLp_top_of_bound hm (δ⁻¹ + 1)
  exact Eventually.of_forall fun x => by
    have hs : radialBoundedVector δ u i x ^ 2 ≤ δ⁻¹ := by
      rw [pow_two, radialBoundedVector_product hδ.le]
      exact (le_abs_self _).trans (radialMatrixEntry_bound hδ i i (fun a => u a x))
    rw [Real.norm_eq_abs]
    have hdn : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    nlinarith [sq_abs (radialBoundedVector δ u i x),
      abs_nonneg (radialBoundedVector δ u i x), sq_nonneg (δ⁻¹)]

theorem radialBoundedVector_contractions {δ : ℝ} (hδ : 0 ≤ δ)
    (d : SourceData μ) (u : Fin n → Space n → ℝ) (χ : Space n → ℝ) (x : Space n) :
    sourceVectorMass d.potential (radialBoundedVector δ u) x =
        sourceVectorMass d.potential u x / radialDenom δ (fun a => u a x) ∧
      sourceConnectionGamma d (radialBoundedVector δ u) x =
        sourceConnectionGamma d u x / radialDenom δ (fun a => u a x) ∧
      sourceConnectionBoundary d χ (radialBoundedVector δ u) x =
        sourceConnectionBoundary d χ u x / radialDenom δ (fun a => u a x) := by
  have hp (i j : Fin n) := radialBoundedVector_product hδ u i j x
  constructor
  · simp only [sourceVectorMass, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_assoc, hp]
    ring
  constructor
  · simp only [sourceConnectionGamma, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_assoc, hp]
    ring
  · simp only [sourceConnectionBoundary, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    rw [hp]
    ring

theorem actual_radial_connectionGamma_integrable (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x => sourceConnectionGamma d (naturalCanonicalFlux d g) x /
      radialDenom δ (fun a => naturalCanonicalFlux d g a x)) (potentialMeasure d.potential) := by
  let u := naturalCanonicalFlux d g
  let v := radialBoundedVector δ u
  have hv (i : Fin n) : MemLp (v i) ∞ (potentialMeasure d.potential) :=
    radialBoundedVector_memLp_top_source d hδ (naturalCanonicalFlux_aestronglyMeasurable d g) i
  have hi : Integrable (sourceConnectionGamma d v) (potentialMeasure d.potential) := by
    apply integrable_finsetSum Finset.univ
    intro i _
    apply integrable_finsetSum Finset.univ
    intro j _
    exact ((actual_third_gram_entry_integrable d i j).mul_of_top_left (hv i)).mul_of_top_left (hv j)
  apply hi.congr
  exact Eventually.of_forall fun x => (radialBoundedVector_contractions hδ.le d u 0 x).2.1

theorem actual_radial_mass_memLp_top (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {δ : ℝ} (hδ : 0 < δ) :
    MemLp (fun x => sourceVectorMass d.potential (naturalCanonicalFlux d g) x /
      radialDenom δ (fun a => naturalCanonicalFlux d g a x)) ∞ (potentialMeasure d.potential) := by
  let u := naturalCanonicalFlux d g
  let v := radialBoundedVector δ u
  have hv (i : Fin n) : MemLp (v i) ∞ (potentialMeasure d.potential) :=
    radialBoundedVector_memLp_top_source d hδ (naturalCanonicalFlux_aestronglyMeasurable d g) i
  have hi : MemLp (sourceVectorMass d.potential v) ∞ (potentialMeasure d.potential) := by
    apply memLp_finsetSum Finset.univ
    intro i _
    apply memLp_finsetSum Finset.univ
    intro j _
    have hp : MemLp (fun x => coordinateHessian d.potential x i j * v i x) ∞
        (potentialMeasure d.potential) := (d.hessian_entry_memLp i j ∞).mul (hv i)
    exact hp.mul (hv j)
  apply (memLp_congr_ae (Eventually.of_forall fun x =>
    (radialBoundedVector_contractions hδ.le d u 0 x).1)).mp hi

theorem exists_actual_radial_connection_boundary_cutoffs (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ χ : ℕ → Space n → ℝ,
      (∀ k, ContDiff ℝ 1 (χ k) ∧ HasCompactSupport (χ k) ∧ ∀ x, χ k x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, Tendsto (fun k => χ k x) atTop (𝓝 1)) ∧
      (∀ k, Integrable (fun x => χ k x * sourceConnectionBoundary d (χ k) (naturalCanonicalFlux d g) x /
        radialDenom δ (fun a => naturalCanonicalFlux d g a x)) (potentialMeasure d.potential)) ∧
      Tendsto (fun k => ∫ x, |χ k x * sourceConnectionBoundary d (χ k) (naturalCanonicalFlux d g) x /
        radialDenom δ (fun a => naturalCanonicalFlux d g a x)| ∂potentialMeasure d.potential) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ x, χ k x * sourceConnectionBoundary d (χ k) (naturalCanonicalFlux d g) x /
        radialDenom δ (fun a => naturalCanonicalFlux d g a x) ∂potentialMeasure d.potential) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let ν := potentialMeasure d.potential
  let u := naturalCanonicalFlux d g
  let v := radialBoundedVector δ u
  have hv (i : Fin n) : MemLp (v i) ∞ ν :=
    radialBoundedVector_memLp_top_source d hδ (naturalCanonicalFlux_aestronglyMeasurable d g) i
  have hvloc (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (v i) ∞ (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure (hv i) d.source_C1.continuous hE
  have hG : Integrable (sourceConnectionGamma d v) ν := by
    apply (actual_radial_connectionGamma_integrable d g hδ).congr
    exact Eventually.of_forall fun x => ((radialBoundedVector_contractions hδ.le d u 0 x).2.1).symm
  have hMt : MemLp (sourceVectorMass d.potential v) ∞ ν := by
    apply (memLp_congr_ae (Eventually.of_forall fun x =>
      ((radialBoundedVector_contractions hδ.le d u 0 x).1).symm)).mp
      (actual_radial_mass_memLp_top d g hδ)
  let C : ℝ := lpNorm (sourceVectorMass d.potential v) ∞ ν
  have hC : 0 ≤ C := lpNorm_nonneg
  have hM : ∀ᵐ x ∂ν, sourceVectorMass d.potential v x ≤ C := by
    filter_upwards [ae_le_lpNorm_exponent_top hMt] with x hx
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hx)
  obtain ⟨x₀, _, hc, _, hp, _, _, hEi, hEconv⟩ := d.exists_metric_energy_cutoffs
  let χ := hessianMetricCutoffSequence d.potential x₀
  have hBi (k : ℕ) : Integrable (fun x => χ k x * sourceConnectionBoundary d (χ k) v x) ν := by
    simpa only [sourceConnectionBoundary, Finset.mul_sum] using
      integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun a _ =>
          (compact_connection_boundary_summand_memLp d hvloc (hc k).1 (hc k).2.1 i j a).integrable (by norm_num))))
  have he0 (k : ℕ) : ∀ᵐ x ∂ν, 0 ≤ C * inverseHessianGradientForm d.potential (χ k) x :=
    d.hessian_ae_source.mono fun x hx => mul_nonneg hC (inverseHessianGradientForm_nonneg_at (χ k) hx.1)
  have hs (k : ℕ) : ∀ᵐ x ∂ν, (χ k x * sourceConnectionBoundary d (χ k) v x) ^ 2 ≤
      (C * inverseHessianGradientForm d.potential (χ k) x) * sourceConnectionGamma d v x := by
    filter_upwards [d.hessian_ae_source, hM, sourceConnectionGamma_nonnegative_ae d v,
      sourceConnectionBoundary_square_le_ae d v (χ k)] with x hx hm hq hb
    have hc2 : χ k x ^ 2 ≤ 1 := by obtain ⟨hlo, hhi⟩ := (hc k).2.2 x; nlinarith
    have he : 0 ≤ inverseHessianGradientForm d.potential (χ k) x :=
      inverseHessianGradientForm_nonneg_at (χ k) hx.1
    calc
      _ ≤ sourceConnectionBoundary d (χ k) v x ^ 2 := by
        rw [mul_pow]
        exact mul_le_of_le_one_left (sq_nonneg _) hc2
      _ ≤ inverseHessianGradientForm d.potential (χ k) x * sourceVectorMass d.potential v x *
          sourceConnectionGamma d v x := hb
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm he) hq
        simpa only [mul_comm, mul_left_comm, mul_assoc] using hh
  have heconv : Tendsto (fun k => ∫ x, C * inverseHessianGradientForm d.potential (χ k) x ∂ν)
      atTop (𝓝 0) := by
    simpa only [integral_const_mul, mul_zero] using hEconv.const_mul C
  obtain ⟨habs, hsign⟩ := integral_tendsto_zero_of_square_domination hBi
    (fun k => (hEi k).const_mul C) hG he0 (sourceConnectionGamma_nonnegative_ae d v) hs heconv
  have hbeq (k : ℕ) : (fun x => χ k x * sourceConnectionBoundary d (χ k) v x) =
      (fun x => χ k x * sourceConnectionBoundary d (χ k) u x /
        radialDenom δ (fun a => u a x)) := by
    funext x
    rw [(radialBoundedVector_contractions hδ.le d u (χ k) x).2.2]
    ring
  refine ⟨χ, hc, hp, ?_, ?_, ?_⟩
  · intro k
    rw [← hbeq k]
    exact hBi k
  · apply habs.congr
    intro k
    exact congrArg (fun b : Space n → ℝ => ∫ x, |b x| ∂ν) (hbeq k)
  · apply hsign.congr
    intro k
    exact congrArg (fun b : Space n → ℝ => ∫ x, b x ∂ν) (hbeq k)

end KLSConstantImprovement.ActualSourceRadialConnectionBoundary405
#print axioms KLSConstantImprovement.ActualSourceRadialConnectionBoundary405.naturalCanonicalFlux_local_L2
#print axioms KLSConstantImprovement.ActualSourceRadialConnectionBoundary405.radialBoundedVector_product
#print axioms KLSConstantImprovement.ActualSourceRadialConnectionBoundary405.radialBoundedVector_memLp_top_source
#print axioms KLSConstantImprovement.ActualSourceRadialConnectionBoundary405.radialBoundedVector_contractions
#print axioms KLSConstantImprovement.ActualSourceRadialConnectionBoundary405.actual_radial_connectionGamma_integrable
#print axioms KLSConstantImprovement.ActualSourceRadialConnectionBoundary405.actual_radial_mass_memLp_top
#print axioms KLSConstantImprovement.ActualSourceRadialConnectionBoundary405.exists_actual_radial_connection_boundary_cutoffs
