import KLSConstantImprovement.ActualRawMetricGraphContinuity
import KLSConstantImprovement.ActualWeakCanonicalMetricCutoffs
import KLS.LocalL2CompactPairings
import KLS.SubgradientLocalMass

/-!
Bounded finite-energy raw H1 functions in the actual canonical form graph.

This is the raw weak-gradient counterpart of the locally Lipschitz form
construction. It applies to actual source Hessian entries with their weak
third derivatives and never substitutes their total classical fderiv.
Only form membership and its actual gradient coordinates are asserted.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualBoundedRawMetricDomain
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualWeakCanonicalMetricCore ActualWeakCanonicalMetricCutoffs
open ActualCompactRawMetricGraph ActualRawMetricGraphContinuity
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem memLp_potentialMeasure_of_compact_localL2
    {φ f : Space n → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport f)
    (hf : ∀ E : Set (Space n), IsCompact E → MemLp f 2 (volume.restrict E)) :
    MemLp f 2 (potentialMeasure φ) := by
  have hfV := memLp_compact_of_localL2 hf hc
  obtain ⟨D, _, hD, hle⟩ := exists_restrict_potentialMeasure_le_smul_volume
    hφ hc.measurableSet hc.isBounded
  have hfr : MemLp f 2 ((potentialMeasure φ).restrict (tsupport f)) :=
    (hfV.smul_measure hD.ne).mono_measure hle
  have hi : MemLp ((tsupport f).indicator f) 2 (potentialMeasure φ) :=
    (memLp_indicator_iff_restrict hc.measurableSet.nullMeasurableSet).mpr hfr
  have he : (tsupport f).indicator f = f := by
    funext x
    by_cases hx : x ∈ tsupport f
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
  rwa [he] at hi

def rawCutoffDerivative (χ f : Space n → ℝ) (F : Fin n → Space n → ℝ)
    (j : Fin n) (x : Space n) : ℝ :=
  χ x * F j x + coordinateDerivative χ j x * f x

theorem rawCanonicalMetricDerivative_cutoff (φ χ f : Space n → ℝ)
    (F : Fin n → Space n → ℝ) (i : Fin n) (x : Space n) :
    rawCanonicalMetricDerivative φ (rawCutoffDerivative χ f F) i x =
      χ x * rawCanonicalMetricDerivative φ F i x + f x * canonicalMetricDerivative φ χ i x := by
  simp only [rawCanonicalMetricDerivative, rawCutoffDerivative, canonicalMetricDerivative,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.raw_metric_derivative_measurable
    {μ : Measure (Space n)} (d : SourceData μ) {F : Fin n → Space n → ℝ}
    (hFloc : ∀ j E, IsCompact E → MemLp (F j) 2 (volume.restrict E)) (i : Fin n) :
    AEStronglyMeasurable (rawCanonicalMetricDerivative d.potential F i)
      (potentialMeasure d.potential) := by
  have hroot := inverseSqrtMatrix_aestronglyMeasurable_of_ae_posDef
    (measurable_coordinateHessian d.potential) (d.hessian_ae_source.mono fun _ hx => hx.1)
  unfold rawCanonicalMetricDerivative canonicalMetricRoot
  exact Finset.univ.aestronglyMeasurable_fun_sum fun j _ =>
    ((continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hroot)).mul
      ((locallyIntegrable_of_memLp_two_on_compacts (hFloc j)).aestronglyMeasurable.mono_ac
        (withDensity_absolutelyContinuous _ _))

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.raw_metric_derivative_sq_ae
    {μ : Measure (Space n)} (d : SourceData μ) (F : Fin n → Space n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (∑ i, rawCanonicalMetricDerivative d.potential F i x ^ 2) =
        rawInverseHessianGradientForm d.potential F x := by
  filter_upwards [d.hessian_ae_source] with x hx
  let R := canonicalMetricRoot d.potential x
  let a : Fin n → ℝ := fun i => F i x
  have he : (R *ᵥ a) ⬝ᵥ (R *ᵥ a) =
      a ⬝ᵥ ((coordinateHessian d.potential x)⁻¹ *ᵥ a) := by
    rw [← Matrix.dotProduct_transpose_mulVec R a (R *ᵥ a),
      Matrix.mulVec_mulVec, canonicalMetricRoot_gram_at hx.1]
  change (∑ i, (R *ᵥ a) i ^ 2) = _
  calc
    _ = (R *ᵥ a) ⬝ᵥ (R *ᵥ a) := by simp only [dotProduct, pow_two]
    _ = _ := he
    _ = _ := (matrix_quadratic_sum_eq_dotProduct (coordinateHessian d.potential x)⁻¹ a).symm

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.raw_metric_derivative_memLp_of_energy
    {μ : Measure (Space n)} (d : SourceData μ) {F : Fin n → Space n → ℝ}
    (hFloc : ∀ j E, IsCompact E → MemLp (F j) 2 (volume.restrict E))
    (he : Integrable (rawInverseHessianGradientForm d.potential F) (potentialMeasure d.potential))
    (i : Fin n) :
    MemLp (rawCanonicalMetricDerivative d.potential F i) 2 (potentialMeasure d.potential) := by
  have hm := d.raw_metric_derivative_measurable hFloc i
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply he.mono' (hm.pow 2)
  filter_upwards [d.raw_metric_derivative_sq_ae F] with x hx
  change ‖rawCanonicalMetricDerivative d.potential F i x ^ 2‖ ≤
    rawInverseHessianGradientForm d.potential F x
  rw [Real.norm_of_nonneg (sq_nonneg _), ← hx]
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin n => (rawCanonicalMetricDerivative d.potential F j x) ^ 2)
    (fun j _ => sq_nonneg (rawCanonicalMetricDerivative d.potential F j x)) (Finset.mem_univ i)

private theorem cutoff_L2_convergence {ρ : Measure (Space n)}
    {χ : ℕ → Space n → ℝ}
    (hχm : ∀ k, AEStronglyMeasurable (χ k) ρ)
    (hχb : ∀ k x, χ k x ∈ Icc (0 : ℝ) 1)
    (hχlim : ∀ x, Tendsto (fun k => χ k x) atTop (𝓝 1))
    {f : Space n → ℝ} (hf : MemLp f 2 ρ) :
    Tendsto (fun k => eLpNorm (fun x => χ k x * f x - f x) 2 ρ) atTop (𝓝 0) := by
  have hm (k : ℕ) : AEStronglyMeasurable (fun x => χ k x * f x - f x) ρ :=
    ((hχm k).mul hf.aestronglyMeasurable).sub hf.aestronglyMeasurable
  have hb (k : ℕ) (x : Space n) : (χ k x * f x - f x) ^ 2 ≤ f x ^ 2 := by
    have h0 := (hχb k x).1
    have h1 := (hχb k x).2
    have hs : (χ k x - 1) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (f x))]
  have hmem (k : ℕ) : MemLp (fun x => χ k x * f x - f x) 2 ρ :=
    (memLp_two_iff_integrable_sq (hm k)).mpr <|
      hf.integrable_sq.mono' ((hm k).pow 2) (Eventually.of_forall fun x => by
        change ‖(χ k x * f x - f x) ^ 2‖ ≤ f x ^ 2
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hb k x)
  apply tendsto_eLpNorm_zero_of_integral_sq hmem
  have ht := tendsto_integral_of_dominated_convergence (fun x => f x ^ 2)
    (fun k => (hm k).pow 2) hf.integrable_sq
    (fun k => Eventually.of_forall fun x => by
      change ‖(χ k x * f x - f x) ^ 2‖ ≤ f x ^ 2
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hb k x)
    (Eventually.of_forall fun x => by
      simpa using (((hχlim x).mul_const (f x)).sub_const (f x)).pow 2)
  simpa using ht

/-- The source's actual conservative cutoffs give form convergence for a
bounded raw H1 function with literal finite inverse-Hessian weak energy. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.bounded_raw_metric_cutoff_approximation
    {μ : Measure (Space n)} (d : SourceData μ)
    {f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hf : AEStronglyMeasurable f (potentialMeasure d.potential))
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B)
    (hFloc : ∀ j E, IsCompact E → MemLp (F j) 2 (volume.restrict E))
    (hFw : ∀ j, HasLocalWeakCoordinateDerivative f (F j) j)
    (he : Integrable (rawInverseHessianGradientForm d.potential F) (potentialMeasure d.potential)) :
    ∃ χ : ℕ → Space n → ℝ,
      (∀ k, ContDiff ℝ 1 (χ k)) ∧ (∀ k, HasCompactSupport (χ k)) ∧
      (∀ k, MemLp (fun x => χ k x * f x) 2 (potentialMeasure d.potential)) ∧
      (∀ k j, MemLp (rawCutoffDerivative (χ k) f F j) 2 (potentialMeasure d.potential)) ∧
      (∀ k j, HasLocalWeakCoordinateDerivative (fun x => χ k x * f x)
        (rawCutoffDerivative (χ k) f F j) j) ∧
      (∀ k j, tsupport (rawCutoffDerivative (χ k) f F j) ⊆ tsupport (χ k)) ∧
      (∀ k i, MemLp (rawCanonicalMetricDerivative d.potential
        (rawCutoffDerivative (χ k) f F) i) 2 (potentialMeasure d.potential)) ∧
      Tendsto (fun k => eLpNorm (fun x => χ k x * f x - f x) 2
        (potentialMeasure d.potential)) atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun k => eLpNorm
        (rawCanonicalMetricDerivative d.potential (rawCutoffDerivative (χ k) f F) i -
          rawCanonicalMetricDerivative d.potential F i) 2 (potentialMeasure d.potential))
          atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨x₀, _, hc, _, hlim, _, _, hEi, hElim⟩ := d.exists_metric_energy_cutoffs
  let χ : ℕ → Space n → ℝ := hessianMetricCutoffSequence d.potential x₀
  have hfTop : MemLp f ∞ (potentialMeasure d.potential) :=
    memLp_top_of_bound hf B (Eventually.of_forall hB)
  have hf2 : MemLp f 2 (potentialMeasure d.potential) := hfTop.mono_exponent (by simp)
  have hfloc (E : Set (Space n)) (hE : IsCompact E) : MemLp f 2 (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure hf2 d.source_C1.continuous hE
  have hd2 (i : Fin n) := d.raw_metric_derivative_memLp_of_energy hFloc he i
  have hχTop (k : ℕ) : MemLp (χ k) ∞ (potentialMeasure d.potential) :=
    memLp_top_of_bound (hc k).1.continuous.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg ((hc k).2.2 x).1]
        exact ((hc k).2.2 x).2)
  have hχd2 (k : ℕ) (i : Fin n) := d.metric_derivative_memLp ((hc k).1) (hc k).2.1 i
  have hFE (k : ℕ) (j : Fin n) :
      tsupport (rawCutoffDerivative (χ k) f F j) ⊆ tsupport (χ k) := by
    exact (tsupport_add _ _).trans
      (union_subset tsupport_mul_subset_left
        (tsupport_mul_subset_left.trans (tsupport_coordinateDerivative_subset (χ k) j)))
  have hFc (k : ℕ) (j : Fin n) : HasCompactSupport (rawCutoffDerivative (χ k) f F j) :=
    (hc k).2.1.of_isClosed_subset (isClosed_tsupport _) (hFE k j)
  have hFcloc (k : ℕ) (j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (rawCutoffDerivative (χ k) f F j) 2 (volume.restrict E) :=
    (memLp_continuous_mul_on_compact hE (hFloc j E hE) (hc k).1.continuous).add
      (memLp_continuous_mul_on_compact hE (hfloc E hE)
        (contDiff_coordinateDerivative (hc k).1 (m := 0) (by norm_num) j).continuous)
  have hFc2 (k : ℕ) (j : Fin n) : MemLp (rawCutoffDerivative (χ k) f F j) 2
      (potentialMeasure d.potential) :=
    memLp_potentialMeasure_of_compact_localL2 d.source_C1.continuous (hFc k j) (hFcloc k j)
  have hFcw (k : ℕ) (j : Fin n) : HasLocalWeakCoordinateDerivative
      (fun x => χ k x * f x) (rawCutoffDerivative (χ k) f F j) j := by
    obtain ⟨W, hW, hWe⟩ := (hFw j).compact_mul hfloc (hFloc j) (hc k).1 (hc k).2.1
    exact (show HasLocalWeakCoordinateDerivative (fun x => χ k x * f x) (fun x => W x) j from hW).congr_ae
      Filter.EventuallyEq.rfl hWe
  have hprod2 (k : ℕ) (i : Fin n) : MemLp
      (rawCanonicalMetricDerivative d.potential (rawCutoffDerivative (χ k) f F) i) 2
      (potentialMeasure d.potential) :=
    (memLp_congr_ae (Eventually.of_forall
      (rawCanonicalMetricDerivative_cutoff d.potential (χ k) f F i))).mpr
      (((hχTop k).mul (hd2 i)).add (hfTop.mul (hχd2 k i)))
  have hχdlim (i : Fin n) : Tendsto (fun k => ∫ x,
      canonicalMetricDerivative d.potential (χ k) i x ^ 2 ∂potentialMeasure d.potential)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun k => integral_nonneg fun x => sq_nonneg _)
      (fun k => integral_mono_ae (hχd2 k i).integrable_sq (hEi k) ?_) hElim
    filter_upwards [d.metric_derivative_sq_ae (χ k)] with x hx
    change (canonicalMetricDerivative d.potential (χ k) i x) ^ 2 ≤
      inverseHessianGradientForm d.potential (χ k) x
    rw [← hx]
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin n => (canonicalMetricDerivative d.potential (χ k) j x) ^ 2)
      (fun j _ => sq_nonneg (canonicalMetricDerivative d.potential (χ k) j x)) (Finset.mem_univ i)
  have hsmall (i : Fin n) : Tendsto (fun k => eLpNorm
      (fun x => f x * canonicalMetricDerivative d.potential (χ k) i x) 2
        (potentialMeasure d.potential)) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_zero_of_integral_sq (fun k => hfTop.mul (hχd2 k i))
    apply squeeze_zero (fun k => integral_nonneg fun x => sq_nonneg _)
      (fun k => ?_) (by simpa using (hχdlim i).const_mul (B ^ 2))
    calc
      _ ≤ ∫ x, B ^ 2 * canonicalMetricDerivative d.potential (χ k) i x ^ 2
          ∂potentialMeasure d.potential := by
        apply integral_mono ((hfTop.mul (hχd2 k i)).integrable_sq)
          ((hχd2 k i).integrable_sq.const_mul (B ^ 2))
        intro x
        change (f x * canonicalMetricDerivative d.potential (χ k) i x) ^ 2 ≤
          B ^ 2 * (canonicalMetricDerivative d.potential (χ k) i x) ^ 2
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have hb := hB x
        rw [Real.norm_eq_abs] at hb
        have hB0 : 0 ≤ B := (abs_nonneg (f x)).trans hb
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (f x)) hB0).mpr hb
      _ = _ := integral_const_mul _ _
  refine ⟨χ, (fun k => (hc k).1), (fun k => (hc k).2.1),
    (fun k => (hχTop k).mul hf2), hFc2, hFcw, hFE, hprod2, ?_, ?_⟩
  · exact cutoff_L2_convergence (fun k => (hc k).1.continuous.aestronglyMeasurable)
      (fun k x => (hc k).2.2 x) hlim hf2
  · intro i
    have hmain := cutoff_L2_convergence (fun k => (hc k).1.continuous.aestronglyMeasurable)
      (fun k x => (hc k).2.2 x) hlim (hd2 i)
    have hbnd (k : ℕ) : eLpNorm
        (rawCanonicalMetricDerivative d.potential (rawCutoffDerivative (χ k) f F) i -
          rawCanonicalMetricDerivative d.potential F i) 2 (potentialMeasure d.potential) ≤
        eLpNorm (fun x => χ k x * rawCanonicalMetricDerivative d.potential F i x -
          rawCanonicalMetricDerivative d.potential F i x) 2 (potentialMeasure d.potential) +
        eLpNorm (fun x => f x * canonicalMetricDerivative d.potential (χ k) i x) 2
          (potentialMeasure d.potential) := by
      have heq : rawCanonicalMetricDerivative d.potential (rawCutoffDerivative (χ k) f F) i -
          rawCanonicalMetricDerivative d.potential F i =
          (fun x => χ k x * rawCanonicalMetricDerivative d.potential F i x -
            rawCanonicalMetricDerivative d.potential F i x) +
          (fun x => f x * canonicalMetricDerivative d.potential (χ k) i x) := by
        funext x
        change rawCanonicalMetricDerivative d.potential (rawCutoffDerivative (χ k) f F) i x -
          rawCanonicalMetricDerivative d.potential F i x =
          (χ k x * rawCanonicalMetricDerivative d.potential F i x -
            rawCanonicalMetricDerivative d.potential F i x) +
          f x * canonicalMetricDerivative d.potential (χ k) i x
        rw [rawCanonicalMetricDerivative_cutoff]
        ring
      rw [heq]
      exact eLpNorm_add_le (by norm_num)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hmain.add (hsmall i)) (fun _ => bot_le) hbnd

/-- Actual global form membership with explicit raw weak metric gradient.
This includes no local Lipschitz or classical derivative premise for f. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.bounded_raw_metric_pair_mem
    {μ : Measure (Space n)} (d : SourceData μ)
    {f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hf : AEStronglyMeasurable f (potentialMeasure d.potential))
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B)
    (hFloc : ∀ j E, IsCompact E → MemLp (F j) 2 (volume.restrict E))
    (hFw : ∀ j, HasLocalWeakCoordinateDerivative f (F j) j)
    (he : Integrable (rawInverseHessianGradientForm d.potential F) (potentialMeasure d.potential)) :
    ∃ U : CanonicalMetricH1 d.potential,
      (canonicalMetricValue d.potential U : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
        (fun x => f x - ∫ y, f y ∂potentialMeasure d.potential) ∧
      ∀ i, (canonicalMetricGradient d.potential i U : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential F i := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hf2 : MemLp f 2 (potentialMeasure d.potential) :=
    MemLp.of_bound hf B (Eventually.of_forall hB)
  have hd2 (i : Fin n) := d.raw_metric_derivative_memLp_of_energy hFloc he i
  obtain ⟨χ, hχ, hχc, hχf2, hFc2, hFcw, hFE, hprod2, hv, hd⟩ :=
    d.bounded_raw_metric_cutoff_approximation hf hB hFloc hFw he
  have hpair := rawCenteredMetricPair_tendsto hχf2 hprod2 hf2 hd2 hv hd
  have hclosed : IsClosed (canonicalMetricGraph d.potential : Set (WeightedEnergyAmbient d.potential)) :=
    Submodule.isClosed_topologicalClosure _
  have hmem : rawCenteredMetricPair hf2 hd2 ∈ canonicalMetricGraph d.potential := by
    apply hclosed.mem_of_tendsto hpair
    exact Eventually.of_forall fun k => d.compact_raw_metric_pair_mem (hχc k)
      tsupport_mul_subset_left (hFE k) (hχf2 k) (hFc2 k) (hFcw k) (hprod2 k)
  exact ⟨⟨_, hmem⟩, rawCenteredMetricPair_value_ae hf2 hd2,
    rawCenteredMetricPair_derivative_ae hf2 hd2⟩

end KLSConstantImprovement.ActualBoundedRawMetricDomain
#print axioms KLSConstantImprovement.ActualBoundedRawMetricDomain.memLp_potentialMeasure_of_compact_localL2
#print axioms KLSConstantImprovement.ActualBoundedRawMetricDomain.rawCanonicalMetricDerivative_cutoff
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.raw_metric_derivative_measurable
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.raw_metric_derivative_sq_ae
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.raw_metric_derivative_memLp_of_energy
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.bounded_raw_metric_cutoff_approximation
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.bounded_raw_metric_pair_mem
