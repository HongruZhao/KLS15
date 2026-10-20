import KLSConstantImprovement.ActualWeakCanonicalMetricInverse
import KLS.HessianMetricComposition
import Mathlib.Topology.Sequences

/-!
Actual smooth companion tests for variational maximum principles. The
approximation is in the canonical form norm only. A smooth scalar
contraction produces compact companion tests with nonnegative mixed
energy and a uniform form-norm bound. No strong operator approximation
or compact operator-range density is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators ContDiff Topology RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceFormCompanions405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualWeakCanonicalMetricInverse
variable {n : ℕ} {μ : Measure (Space n)}

/-- Every actual form element has genuine compact scalar form
approximants. The statement deliberately contains no generator norm. -/
theorem exists_actual_compact_form_approximation (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) :
    ∃ f : ℕ → Space n → ℝ, ∃ W : ℕ → CanonicalMetricH1 d.potential,
      (∀ k, ContDiff ℝ 3 (f k) ∧ HasCompactSupport (f k) ∧
        (canonicalMetricValue d.potential (W k) : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
          (fun x => f k x - ∫ y, f k y ∂potentialMeasure d.potential) ∧
        ∀ i : Fin n, (canonicalMetricGradient d.potential i (W k) : Space n → ℝ)
          =ᵐ[potentialMeasure d.potential] canonicalMetricDerivative d.potential (f k) i) ∧
      Tendsto W atTop (𝓝 U) := by
  have hU : (U : WeightedEnergyAmbient d.potential) ∈
      closure (smoothCanonicalMetricGraphSet d.potential) := by
    rw [← canonicalMetricGraph_coe_eq_closure d.source_C1.continuous]
    exact U.property
  obtain ⟨A, hA, hlim⟩ := mem_closure_iff_seq_limit.mp hU
  have hAcore (k : ℕ) : A k ∈ smoothCanonicalMetricGraphSet d.potential := hA k
  choose f hf hc hv hd using hA
  let W : ℕ → CanonicalMetricH1 d.potential := fun k =>
    ⟨A k, Submodule.le_topologicalClosure _ (Submodule.subset_span (hAcore k))⟩
  refine ⟨f, W, fun k => ⟨hf k, hc k, hv k, hd k⟩, ?_⟩
  exact tendsto_subtype_rng.mpr hlim

def compactScalarCompose (η : ℝ → ℝ) (c : ℝ) (f : Space n → ℝ) (x : Space n) : ℝ :=
  η (f x - c) - η (-c)

theorem compactScalarCompose_contDiff {η : ℝ → ℝ} (hη : ContDiff ℝ 3 η)
    {f : Space n → ℝ} (hf : ContDiff ℝ 3 f) (c : ℝ) :
    ContDiff ℝ 3 (compactScalarCompose η c f) :=
  (hη.comp (hf.sub contDiff_const)).sub contDiff_const

theorem compactScalarCompose_hasCompactSupport (η : ℝ → ℝ) (c : ℝ)
    {f : Space n → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (compactScalarCompose η c f) := by
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hn
  have hz : f x = 0 := image_eq_zero_of_notMem_tsupport hn
  exact hx (by simp only [compactScalarCompose, hz, zero_sub, sub_self])

theorem compactScalarCompose_metric_derivative (φ : Space n → ℝ)
    {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) {f : Space n → ℝ} (hf : ContDiff ℝ 1 f)
    (c : ℝ) (i : Fin n) (x : Space n) :
    canonicalMetricDerivative φ (compactScalarCompose η c f) i x =
      deriv η (f x - c) * canonicalMetricDerivative φ f i x := by
  have hd (j : Fin n) : coordinateDerivative (compactScalarCompose η c f) j x =
      deriv η (f x - c) * coordinateDerivative f j x := by
    have hcη : coordinateDerivative (compactScalarCompose η c f) j x =
        coordinateDerivative (fun y => η (f y - c)) j x := by
      change fderiv ℝ (fun y => η (f y - c) - η (-c)) x (EuclideanSpace.single j 1) = _
      rw [fderiv_sub_const]
      rfl
    rw [hcη, coordinateDerivative_scalar_comp
      (hη.differentiable one_ne_zero _) ((hf.sub contDiff_const).differentiable one_ne_zero _)]
    simp only [coordinateDerivative, fderiv_sub_const]
  unfold canonicalMetricDerivative
  simp_rw [hd]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The smooth companion lies in the same actual form graph; its mixed
energy is nonnegative and its norm is bounded uniformly by that of the
original compact form element. These are the precise bounds needed to
pass the variational maximum principle through a form approximation. -/
theorem exists_actual_smooth_form_companion (d : SourceData μ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f)
    (U : CanonicalMetricH1 d.potential)
    (hU : ∀ i : Fin n, (canonicalMetricGradient d.potential i U : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] canonicalMetricDerivative d.potential f i)
    {η : ℝ → ℝ} (hη : ContDiff ℝ 3 η) (c : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hη0 : ∀ s, 0 ≤ deriv η s) (hηB : ∀ s, ‖deriv η s‖ ≤ B) :
    ∃ V : CanonicalMetricH1 d.potential,
      (canonicalMetricValue d.potential V : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
        (fun x => compactScalarCompose η c f x -
          ∫ y, compactScalarCompose η c f y ∂potentialMeasure d.potential) ∧
      (∀ i : Fin n, (canonicalMetricGradient d.potential i V : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential] fun x =>
          deriv η (f x - c) * canonicalMetricGradient d.potential i U x) ∧
      0 ≤ canonicalMetricEnergy d.potential U V ∧
      canonicalMetricEnergy d.potential V V ≤ B ^ 2 * canonicalMetricEnergy d.potential U U ∧
      ‖V‖ ≤ (2 * (B + 1)) * ‖U‖ := by
  obtain ⟨V, hv, hd⟩ := exists_sourceMetricH1_of_smoothCompact d
    (compactScalarCompose_contDiff hη hf c) (compactScalarCompose_hasCompactSupport η c hc)
  have hgrad (i : Fin n) : (canonicalMetricGradient d.potential i V : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] fun x =>
        deriv η (f x - c) * canonicalMetricGradient d.potential i U x := by
    filter_upwards [hd i, hU i] with x hx hy
    rw [hx, hy, compactScalarCompose_metric_derivative d.potential
      (hη.of_le (by norm_num)) (hf.of_le (by norm_num))]
  have hnorm (i : Fin n) : ‖canonicalMetricGradient d.potential i V‖ ≤
      B * ‖canonicalMetricGradient d.potential i U‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hgrad i] with x hx
    rw [hx, norm_mul]
    exact mul_le_mul_of_nonneg_right (hηB _) (norm_nonneg _)
  have hcross : 0 ≤ canonicalMetricEnergy d.potential U V := by
    rw [canonicalMetricEnergy_apply]
    apply Finset.sum_nonneg
    intro i _
    rw [L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [hgrad i] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial]
    change 0 ≤ deriv η (f x - c) * canonicalMetricGradient d.potential i U x *
      canonicalMetricGradient d.potential i U x
    nlinarith [mul_nonneg (hη0 (f x - c))
      (sq_nonneg (canonicalMetricGradient d.potential i U x))]
  have henergy : canonicalMetricEnergy d.potential V V ≤
      B ^ 2 * canonicalMetricEnergy d.potential U U := by
    rw [canonicalMetricEnergy_self, canonicalMetricEnergy_self, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ (B * ‖canonicalMetricGradient d.potential i U‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mpr (hnorm i)
      _ = _ := by ring
  have hUenergy : canonicalMetricEnergy d.potential U U ≤ ‖U‖ ^ 2 := by
    rw [canonicalMetricH1_norm_sq, canonicalMetricEnergy_self]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hVnorm : ‖V‖ ^ 2 ≤ 2 * canonicalMetricEnergy d.potential V V := by
    have hvBL := sourceMetricValue_norm_sq_le_energy d V
    rw [canonicalMetricH1_norm_sq, canonicalMetricEnergy_self]
    linarith
  have hnormV : ‖V‖ ≤ (2 * (B + 1)) * ‖U‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp
    have h1 := mul_le_mul_of_nonneg_left hUenergy (sq_nonneg B)
    have h2 : 2 * B ^ 2 ≤ (2 * (B + 1)) ^ 2 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖U‖)
    nlinarith
  exact ⟨V, hv, hgrad, hcross, henergy, hnormV⟩

end KLSConstantImprovement.ActualSourceFormCompanions405

#print axioms KLSConstantImprovement.ActualSourceFormCompanions405.exists_actual_compact_form_approximation
#print axioms KLSConstantImprovement.ActualSourceFormCompanions405.exists_actual_smooth_form_companion
