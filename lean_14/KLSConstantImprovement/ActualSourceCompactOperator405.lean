import KLSConstantImprovement.ActualWeakCanonicalMetricSmoothing
import KLSConstantImprovement.ActualWeakCanonicalMetricCutoffs
import KLSConstantImprovement.ActualWeakCanonicalMetricInverse

/-!
The literal compact canonical generator on the actually constructed C1,1
source. Its L2 domain, zero mean and form pairing are derived from the weak
Monge--Ampere transport. The actual inverse solves its distribution equation.
No C4 source, pointwise inverse-Hessian bound or compact strong graph core is
assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped BigOperators ContDiff Topology ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceCompactOperator405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualWeakCanonicalMetricCore ActualWeakCanonicalMetricSmoothing
open ActualWeakCanonicalMetricCutoffs ActualWeakCanonicalMetricInverse
variable {n : ℕ} {μ : Measure (Space n)}

theorem compact_inverse_entry_top (d : SourceData μ)
    {E : Set (Space n)} (hE : IsCompact E) (i j : Fin n) :
    MemLp (E.indicator (fun x => (coordinateHessian d.potential x)⁻¹ i j)) ∞
      (potentialMeasure d.potential) := by
  let a : Fin n → Space n → ℝ := fun k =>
    E.indicator (fun x => canonicalMetricRoot d.potential x k i)
  let b : Fin n → Space n → ℝ := fun k =>
    E.indicator (fun x => canonicalMetricRoot d.potential x k j)
  have hm : MemLp (fun x => ∑ k : Fin n, a k x * b k x) ∞
      (potentialMeasure d.potential) :=
    memLp_finsetSum Finset.univ fun k _ =>
      (d.compact_metricRoot_entry_top hE k i).mul (d.compact_metricRoot_entry_top hE k j)
  have he : E.indicator (fun x => (coordinateHessian d.potential x)⁻¹ i j)
      =ᵐ[potentialMeasure d.potential] fun x => ∑ k : Fin n, a k x * b k x := by
    filter_upwards [d.hessian_ae_source] with x hx
    by_cases hxE : x ∈ E
    · simp only [a, b, indicator_of_mem hxE]
      exact (congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j)
        (canonicalMetricRoot_gram_at hx.1)).symm
    · simp only [a, b, indicator_of_notMem hxE, zero_mul, Finset.sum_const_zero]
  exact (memLp_congr_ae he).mpr hm

private theorem hessian_zero_off_support {ψ : Space n → ℝ}
    {x : Space n} (hx : x ∉ tsupport ψ) (i j : Fin n) : coordinateHessian ψ x i j = 0 := by
  change coordinateDerivative (coordinateDerivative ψ j) i x = 0
  exact image_eq_zero_of_notMem_tsupport fun hi => hx
    ((tsupport_coordinateDerivative_subset _ i).trans (tsupport_coordinateDerivative_subset ψ j) hi)

theorem compact_inverse_hessian_term_memLp (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) (i j : Fin n) :
    MemLp (fun x => (coordinateHessian d.potential x)⁻¹ i j * coordinateHessian ψ x i j)
      2 (potentialMeasure d.potential) := by
  have hh : MemLp (fun x => coordinateHessian ψ x i j) 2 (potentialMeasure d.potential) :=
    memLp_of_continuous_hasCompactSupport d.source_C1.continuous
    (contDiff_coordinateHessian hψ (m := 0) (by norm_num) i j).continuous
    (hasCompactSupport_coordinateHessian hc i j)
  have hi : MemLp (fun x => (tsupport ψ).indicator (fun y =>
      (coordinateHessian d.potential y)⁻¹ i j) x * coordinateHessian ψ x i j) 2
      (potentialMeasure d.potential) := (compact_inverse_entry_top d hc i j).mul hh
  have he : (fun x => (coordinateHessian d.potential x)⁻¹ i j * coordinateHessian ψ x i j) =
      (fun x => (tsupport ψ).indicator (fun y => (coordinateHessian d.potential y)⁻¹ i j) x *
        coordinateHessian ψ x i j) := by
    funext x
    by_cases hx : x ∈ tsupport ψ
    · rw [indicator_of_mem hx]
    · rw [hessian_zero_off_support hx, mul_zero, mul_zero]
  rw [he]
  exact hi

def actualSourceOperator (d : SourceData μ) (ψ : Space n → ℝ) : Space n → ℝ :=
  fun x => -hessianMetricDiffusion d.potential d.targetPotential ψ x

theorem actualSourceOperator_memLp (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    MemLp (actualSourceOperator d ψ) 2 (potentialMeasure d.potential) := by
  have hsecond : MemLp (fun x => ∑ i : Fin n, ∑ j : Fin n,
      (coordinateHessian d.potential x)⁻¹ i j * coordinateHessian ψ x i j)
      2 (potentialMeasure d.potential) :=
    memLp_finsetSum Finset.univ fun i _ => memLp_finsetSum Finset.univ fun j _ =>
      compact_inverse_hessian_term_memLp d hψ hc i j
  have hfirst : MemLp (fun x => ∑ i : Fin n,
      coordinateDerivative d.targetPotential i (gradient d.potential x) * coordinateDerivative ψ i x)
      2 (potentialMeasure d.potential) := by
    apply memLp_finsetSum
    intro i _
    exact memLp_of_continuous_hasCompactSupport d.source_C1.continuous
      (((contDiff_coordinateDerivative (d.target_smooth.of_le (by simp) : ContDiff ℝ 1 d.targetPotential)
        (m := 0) (by norm_num) i).continuous.comp d.gradient_lipschitz.continuous).mul
          (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous)
      (hasCompactSupport_coordinateDerivative hc i).mul_left
  exact (hsecond.sub hfirst).neg

def actualSourceOperatorLp (d : SourceData μ) {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) : Lp ℝ 2 (potentialMeasure d.potential) :=
  (actualSourceOperator_memLp d hψ hc).toLp (actualSourceOperator d ψ)

theorem actualSourceOperator_mean_zero (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, actualSourceOperator d ψ x ∂potentialMeasure d.potential) = 0 := by
  letI := d.source_probability
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by norm_num)
  have hterm (i j : Fin n) :=
    (compact_inverse_hessian_term_memLp d hψ2 hc i j).integrable (by norm_num)
  have hfirst (j : Fin n) : Integrable (fun x =>
      coordinateDerivative d.targetPotential j (gradient d.potential x) * coordinateDerivative ψ j x)
      (potentialMeasure d.potential) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport d.source_C1.continuous
      (((contDiff_coordinateDerivative (d.target_smooth.of_le (by simp) : ContDiff ℝ 1 d.targetPotential)
        (m := 0) (by norm_num) j).continuous.comp d.gradient_lipschitz.continuous).mul
          (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) j).continuous)
      (hasCompactSupport_coordinateDerivative hc j).mul_left
  have hcol (j : Fin n) : (∑ i, ∫ x,
      (coordinateHessian d.potential x)⁻¹ i j * coordinateHessian ψ x i j
        ∂potentialMeasure d.potential) =
      ∫ x, coordinateDerivative d.targetPotential j (gradient d.potential x) * coordinateDerivative ψ j x
        ∂potentialMeasure d.potential :=
    weak_moment_inverseHessian_integral_column d.source_lipschitz d.source_convex
      (d.target_smooth.of_le (by simp)) d.target_convex_potential d.target_convexity_pos
      d.target_strong d.target_closed d.target_convex (d.pushforward.trans d.target_representation)
      (contDiff_coordinateDerivative hψ (m := 1) (by norm_num) j) (hasCompactSupport_coordinateDerivative hc j) j
  have hsecond : Integrable (fun x => ∑ i : Fin n, ∑ j : Fin n,
      (coordinateHessian d.potential x)⁻¹ i j * coordinateHessian ψ x i j)
      (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ => hterm i j
  unfold actualSourceOperator hessianMetricDiffusion
  rw [integral_neg, integral_sub hsecond (integrable_finsetSum Finset.univ fun j _ => hfirst j),
    integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun j _ => hterm i j),
    integral_finsetSum Finset.univ (fun j _ => hfirst j)]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hterm _ j)]
  rw [Finset.sum_comm]
  simp_rw [hcol]
  ring

private def compactOperatorTestFunctional (d : SourceData μ) {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    WeightedEnergyAmbient d.potential →L[ℝ] ℝ :=
  (∑ i : Fin n, (innerSL ℝ ((d.metric_derivative_memLp (hψ.of_le (by norm_num)) hc i).toLp
      (canonicalMetricDerivative d.potential ψ i))).comp
        (PiLp.proj 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure d.potential)) i.succ)) -
  (innerSL ℝ (actualSourceOperatorLp d (hψ.of_le (by norm_num)) hc)).comp
    (PiLp.proj 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure d.potential)) 0)

private theorem compactOperatorTestFunctional_apply (d : SourceData μ) {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) (U : WeightedEnergyAmbient d.potential) :
    compactOperatorTestFunctional d hψ hc U =
      (∑ i : Fin n, ∫ x, U i.succ x * canonicalMetricDerivative d.potential ψ i x
        ∂potentialMeasure d.potential) -
      ∫ x, U 0 x * actualSourceOperator d ψ x ∂potentialMeasure d.potential := by
  simp only [compactOperatorTestFunctional, _root_.sub_apply, _root_.sum_apply, Finset.sum_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, innerSL_apply_apply, actualSourceOperatorLp]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(d.metric_derivative_memLp (hψ.of_le (by norm_num)) hc i).coeFn_toLp] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial]
  · rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(actualSourceOperator_memLp d (hψ.of_le (by norm_num)) hc).coeFn_toLp] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial]

private theorem compact_core_subset_test_ker (d : SourceData μ) {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    smoothCanonicalMetricGraphSet d.potential ⊆
      LinearMap.ker (compactOperatorTestFunctional d hψ hc).toLinearMap := by
  letI := d.source_probability
  rintro U ⟨f, hf, hfc, hv, hd⟩
  change compactOperatorTestFunctional d hψ hc U = 0
  rw [compactOperatorTestFunctional_apply]
  have hl : (∑ i : Fin n, ∫ x, U i.succ x * canonicalMetricDerivative d.potential ψ i x
      ∂potentialMeasure d.potential) =
      ∫ x, hessianMetricGradientPair d.potential f ψ x ∂potentialMeasure d.potential := by
    simp_rw [show ∀ i : Fin n, (∫ x, U i.succ x * canonicalMetricDerivative d.potential ψ i x
        ∂potentialMeasure d.potential) = ∫ x, canonicalMetricDerivative d.potential f i x *
          canonicalMetricDerivative d.potential ψ i x ∂potentialMeasure d.potential from
      fun i => integral_congr_ae ((hd i).fun_mul EventuallyEq.rfl)]
    have hprod (i : Fin n) : Integrable (fun x =>
        canonicalMetricDerivative d.potential f i x * canonicalMetricDerivative d.potential ψ i x)
        (potentialMeasure d.potential) :=
      (d.metric_derivative_memLp (hf.of_le (by norm_num)) hfc i).integrable_mul
        (d.metric_derivative_memLp (hψ.of_le (by norm_num)) hc i)
    rw [← integral_finsetSum Finset.univ (fun i _ => hprod i)]
    apply integral_congr_ae
    filter_upwards [d.hessian_ae_source] with x hx
    let R := canonicalMetricRoot d.potential x
    let a : Fin n → ℝ := fun i => coordinateDerivative f i x
    let b : Fin n → ℝ := fun i => coordinateDerivative ψ i x
    change (R *ᵥ a) ⬝ᵥ (R *ᵥ b) = _
    rw [dotProduct_comm (R *ᵥ a) (R *ᵥ b),
      ← Matrix.dotProduct_transpose_mulVec R a (R *ᵥ b),
      Matrix.mulVec_mulVec, canonicalMetricRoot_gram_at hx.1]
    simp only [hessianMetricGradientPair, dotProduct, Matrix.mulVec, Finset.mul_sum, a, b]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hIBP := d.compact_metric_first_factor (fun j =>
    (contDiff_coordinateDerivative hψ (m := 1) (by norm_num) j).locallyLipschitz)
      (hf.of_le (by norm_num)) hfc
  have hfA : Integrable (fun x => f x * actualSourceOperator d ψ x) (potentialMeasure d.potential) :=
    (memLp_of_continuous_hasCompactSupport d.source_C1.continuous hf.continuous hfc).integrable_mul
      (actualSourceOperator_memLp d (hψ.of_le (by norm_num)) hc)
  have hAI := (actualSourceOperator_memLp d (hψ.of_le (by norm_num)) hc).integrable (by norm_num)
  have hr : (∫ x, U 0 x * actualSourceOperator d ψ x ∂potentialMeasure d.potential) =
      ∫ x, hessianMetricGradientPair d.potential f ψ x ∂potentialMeasure d.potential := by
    rw [integral_congr_ae (hv.fun_mul EventuallyEq.rfl)]
    calc
      _ = (∫ x, f x * actualSourceOperator d ψ x ∂potentialMeasure d.potential) -
          (∫ y, f y ∂potentialMeasure d.potential) *
            ∫ x, actualSourceOperator d ψ x ∂potentialMeasure d.potential := by
        rw [← integral_const_mul, ← integral_sub hfA (hAI.const_mul _)]
        apply integral_congr_ae
        exact Eventually.of_forall fun _ => by ring
      _ = _ := by
        rw [actualSourceOperator_mean_zero d hψ hc, mul_zero, sub_zero]
        unfold actualSourceOperator
        simp_rw [mul_neg]
        rw [integral_neg, hIBP.2.2, neg_neg]
        rfl
  rw [hl, hr, sub_self]

/-- The same completed inverse-Hessian graph has the actual compact PDE
pairing. It is derived by continuous extension of weak source transport. -/
theorem metricH1_compact_operator_pairing (d : SourceData μ) {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) (U : CanonicalMetricH1 d.potential) :
    (∑ i : Fin n, ∫ x, canonicalMetricGradient d.potential i U x *
      canonicalMetricDerivative d.potential ψ i x ∂potentialMeasure d.potential) =
      ∫ x, canonicalMetricValue d.potential U x * actualSourceOperator d ψ x
        ∂potentialMeasure d.potential := by
  have hs : Submodule.span ℝ (smoothCanonicalMetricGraphSet d.potential) ≤
      LinearMap.ker (compactOperatorTestFunctional d hψ hc).toLinearMap :=
    Submodule.span_le.mpr (compact_core_subset_test_ker d hψ hc)
  have hcl := Submodule.topologicalClosure_minimal _ hs
    (compactOperatorTestFunctional d hψ hc).isClosed_ker
  have hU := hcl U.property
  change compactOperatorTestFunctional d hψ hc (U : WeightedEnergyAmbient d.potential) = 0 at hU
  rw [compactOperatorTestFunctional_apply] at hU
  exact sub_eq_zero.mp hU

theorem sourceMetricInverse_weak_diffusion (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, sourceMetricInverse d g x * actualSourceOperator d ψ x ∂potentialMeasure d.potential) =
      ∫ x, g x * (ψ x - ∫ y, ψ y ∂potentialMeasure d.potential) ∂potentialMeasure d.potential := by
  change (∫ x, canonicalMetricValue d.potential (sourceMetricInverseH1 d g) x *
    actualSourceOperator d ψ x ∂potentialMeasure d.potential) = _
  rw [← metricH1_compact_operator_pairing d hψ hc]
  exact sourceMetricInverse_compact_test d g hψ hc

end KLSConstantImprovement.ActualSourceCompactOperator405

#print axioms KLSConstantImprovement.ActualSourceCompactOperator405.actualSourceOperator_memLp
#print axioms KLSConstantImprovement.ActualSourceCompactOperator405.actualSourceOperator_mean_zero
#print axioms KLSConstantImprovement.ActualSourceCompactOperator405.metricH1_compact_operator_pairing
#print axioms KLSConstantImprovement.ActualSourceCompactOperator405.sourceMetricInverse_weak_diffusion
