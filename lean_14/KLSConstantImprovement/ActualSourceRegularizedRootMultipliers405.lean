import KLSConstantImprovement.ActualSourceRegularizedRootPassage405
import KLSConstantImprovement.ActualBoundedCoefficientL2Passage405

/-! Actual compact root-product test coefficients converge strongly in
the original source L2 space. This pays the variable tests used to pass
the regularized raw Jacobian's weak identities to the actual metric. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceRegularizedRootMultipliers405
open KLS ActualBoundedCanonicalSource ActualSourceMetricRegularization405
open ActualSourceRegularizedRootPassage405 ActualBoundedCoefficientL2Passage405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricCore ActualWeakCanonicalMetricOrdinaryGraph
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem regularizedMetricRoots_continuous (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    Continuous (regularizedMetricRoot d k ε) ∧ Continuous (regularizedMetricUnroot d k ε) := by
  have hH : ContDiff ℝ 1 (regularizedMetricHessian d k ε) :=
    (regularizedMetricHessian_contDiff d k ε).of_le (by simp)
  have hR : Continuous (regularizedMetricRoot d k ε) :=
    (locallyLipschitz_inverseSqrtMatrix_comp hH.locallyLipschitz
      (regularizedMetricHessian_posDef d k hε)).continuous
  refine ⟨hR, continuous_iff_continuousAt.mpr fun x => ?_⟩
  change ContinuousAt (fun y => (regularizedMetricRoot d k ε y)⁻¹) x
  have hP : (regularizedMetricRoot d k ε x).PosDef := by
    unfold regularizedMetricRoot inverseSqrtMatrix
    exact ((CFC.sqrt_nonneg (regularizedMetricHessian d k ε x)).posSemidef.posDef_iff_isUnit.mpr
      ((CFC.isUnit_sqrt_iff _ (regularizedMetricHessian_posDef d k hε x).posSemidef.nonneg).mpr
        (regularizedMetricHessian_posDef d k hε x).isUnit)).inv
  have hinv : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℝ => A⁻¹) (regularizedMetricRoot d k ε x) :=
    matrix_inverse_continuousAt_posDef hP
  have hRx : Tendsto (regularizedMetricRoot d k ε) (𝓝 x) (𝓝 (regularizedMetricRoot d k ε x)) :=
    hR.continuousAt.tendsto
  exact hinv.tendsto.comp hRx

def compactRegularizedRootProduct (d : SourceData μ) (E : Set (Space n))
    (i a b j : Fin n) (k : ℕ) : Space n → ℝ :=
  E.indicator (fun x => regularizedMetricRoot d k (cutoffScale k) x i a *
    regularizedMetricUnroot d k (cutoffScale k) x b j)

def compactActualRootProduct (d : SourceData μ) (E : Set (Space n))
    (i a b j : Fin n) : Space n → ℝ :=
  E.indicator (fun x => canonicalMetricRoot d.potential x i a * canonicalMetricUnroot d.potential x b j)

theorem compact_root_product_mul_tendsto_L2 (d : SourceData μ)
    {E : Set (Space n)} (hE : IsCompact E) (i a b j : Fin n)
    {f : Space n → ℝ} (hf : MemLp f 2 (potentialMeasure d.potential)) :
    ∃ (hprod : ∀ k, MemLp (fun x => compactRegularizedRootProduct d E i a b j k x * f x)
        2 (potentialMeasure d.potential))
      (hlimit : MemLp (fun x => compactActualRootProduct d E i a b j x * f x)
        2 (potentialMeasure d.potential)),
      Tendsto (fun k => (hprod k).toLp (fun x => compactRegularizedRootProduct d E i a b j k x * f x)) atTop
        (𝓝 (hlimit.toLp (fun x => compactActualRootProduct d E i a b j x * f x))) := by
  let ν := potentialMeasure d.potential
  obtain ⟨B, hB, hRb⟩ := regularizedMetricRoot_uniform_compact_entry_bound d hE
  let C : ℝ := 4 / d.targetConvexityConstant + 2
  have hC : 0 < C := by have hκ := d.target_convexity_pos; dsimp only [C]; positivity
  have hε1 (k : ℕ) : cutoffScale k ≤ 1 := by
    unfold cutoffScale
    apply inv_le_one_of_one_le₀
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have ha (k : ℕ) : AEStronglyMeasurable (compactRegularizedRootProduct d E i a b j k) ν := by
    obtain ⟨hR, hS⟩ := regularizedMetricRoots_continuous d k (cutoffScale_pos k)
    have hr : Continuous (fun x => regularizedMetricRoot d k (cutoffScale k) x i a) :=
      (continuous_apply a).comp ((continuous_apply i).comp hR)
    have hs : Continuous (fun x => regularizedMetricUnroot d k (cutoffScale k) x b j) :=
      (continuous_apply j).comp ((continuous_apply b).comp hS)
    exact (hr.mul hs).aestronglyMeasurable.indicator hE.measurableSet
  have hroot := inverseSqrtMatrix_aestronglyMeasurable_of_ae_posDef
    (measurable_coordinateHessian d.potential) (d.hessian_ae_source.mono fun _ hx => hx.1)
  have hb : AEStronglyMeasurable (compactActualRootProduct d E i a b j) ν := by
    have hr : AEStronglyMeasurable (fun x => canonicalMetricRoot d.potential x i a) ν :=
      (continuous_apply a).comp_aestronglyMeasurable ((continuous_apply i).comp_aestronglyMeasurable hroot)
    have hs : AEStronglyMeasurable (fun x => canonicalMetricUnroot d.potential x b j) ν :=
      (continuous_apply j).comp_aestronglyMeasurable
        ((continuous_apply b).comp_aestronglyMeasurable (sourceMetricUnroot_aestronglyMeasurable d))
    exact (hr.mul hs).indicator hE.measurableSet
  have hbound (k : ℕ) (x : Space n) : ‖compactRegularizedRootProduct d E i a b j k x‖ ≤ B * C := by
    by_cases hx : x ∈ E
    · rw [compactRegularizedRootProduct, indicator_of_mem hx, norm_mul]
      exact mul_le_mul (hRb k (cutoffScale k) (cutoffScale_pos k) x hx i a)
        (regularizedMetricUnroot_uniform_entry_bound d k (cutoffScale_pos k) (hε1 k) x b j)
        (norm_nonneg _) hB.le
    · rw [compactRegularizedRootProduct, indicator_of_notMem hx, norm_zero]
      exact mul_nonneg hB.le hC.le
  have hac : ν ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun k => compactRegularizedRootProduct d E i a b j k x) atTop
      (𝓝 (compactActualRootProduct d E i a b j x)) := by
    filter_upwards [(regularizedMetricRoots_tendsto_ae d).filter_mono hac.ae_le] with x hx
    by_cases hxE : x ∈ E
    · have htR := (((continuous_apply a).comp (continuous_apply i)).continuousAt.tendsto.comp hx.1)
      have htS := (((continuous_apply j).comp (continuous_apply b)).continuousAt.tendsto.comp hx.2)
      simpa only [compactRegularizedRootProduct, compactActualRootProduct, indicator_of_mem hxE, Function.comp_def] using htR.mul htS
    · simp only [compactRegularizedRootProduct, compactActualRootProduct, indicator_of_notMem hxE]
      exact tendsto_const_nhds
  have hbnd : ∀ᵐ x ∂ν, ‖compactActualRootProduct d E i a b j x‖ ≤ B * C := by
    filter_upwards [hlim] with x hx
    exact le_of_tendsto hx.norm (Eventually.of_forall fun k => hbound k x)
  exact bounded_coefficient_mul_tendsto_L2 ha hb (mul_nonneg hB.le hC.le)
    (fun k => Eventually.of_forall (hbound k)) hbnd hlim hf

end KLSConstantImprovement.ActualSourceRegularizedRootMultipliers405
#print axioms KLSConstantImprovement.ActualSourceRegularizedRootMultipliers405.regularizedMetricRoots_continuous
#print axioms KLSConstantImprovement.ActualSourceRegularizedRootMultipliers405.compact_root_product_mul_tendsto_L2
