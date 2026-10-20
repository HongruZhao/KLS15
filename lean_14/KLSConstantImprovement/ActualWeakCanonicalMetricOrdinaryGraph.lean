import KLSConstantImprovement.ActualWeakCanonicalMetricInverse
import KLS.FrameHessianAlgebra
import KLS.WeightedEnergyGraphClosability
import Mathlib.MeasureTheory.Function.Holder

/-!
# The actual weak source gradient of a canonical metric graph element

The actual bounded source Hessian makes multiplication by its positive
square root a bounded L2 operator.  Applied to the metric gradient graph,
this gives the actual ordinary weighted H1 graph of the same value.  Its
weak derivatives and local Sobolev domain follow from existing proved
ordinary-graph calculus.  No smooth Poisson representative is assumed.
-/

open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped BigOperators ContDiff Topology ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace KLSConstantImprovement.ActualWeakCanonicalMetricOrdinaryGraph

open KLS
open KLSConstantImprovement.ActualBoundedCanonicalSource
open KLSConstantImprovement.ActualWeakCanonicalMetricCore
open KLSConstantImprovement.ActualCanonicalMetricEnergyGraph
open KLSConstantImprovement.ActualWeakCanonicalMetricInverse
variable {n : ℕ} {μ : Measure (Space n)}

def canonicalMetricUnroot (φ : Space n → ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ := (canonicalMetricRoot φ x)⁻¹

theorem canonicalMetricRoot_posDef_at {φ : Space n → ℝ} {x : Space n}
    (hpos : (coordinateHessian φ x).PosDef) : (canonicalMetricRoot φ x).PosDef := by
  unfold canonicalMetricRoot inverseSqrtMatrix
  exact ((CFC.sqrt_nonneg (coordinateHessian φ x)).posSemidef.posDef_iff_isUnit.mpr
    ((CFC.isUnit_sqrt_iff (coordinateHessian φ x) hpos.posSemidef.nonneg).mpr hpos.isUnit)).inv

theorem canonicalMetricUnroot_mul_root_at {φ : Space n → ℝ} {x : Space n}
    (hpos : (coordinateHessian φ x).PosDef) :
    canonicalMetricUnroot φ x * canonicalMetricRoot φ x = 1 := by
  exact Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (canonicalMetricRoot_posDef_at hpos).isUnit)

theorem canonicalMetricUnroot_gram_at {φ : Space n → ℝ} {x : Space n}
    (hpos : (coordinateHessian φ x).PosDef) :
    (canonicalMetricUnroot φ x).transpose * canonicalMetricUnroot φ x =
      coordinateHessian φ x :=
  inverseSqrtMatrix_inverse_gram hpos

private theorem inverse_aestronglyMeasurable_of_ae_posDef
    {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    {H : α → Matrix (Fin n) (Fin n) ℝ} (hH : AEStronglyMeasurable H ρ)
    (hpos : ∀ᵐ x ∂ρ, (H x).PosDef) :
    AEStronglyMeasurable (fun x => (H x)⁻¹) ρ := by
  classical
  let S : Set (Matrix (Fin n) (Fin n) ℝ) := {A | A.PosDef}
  have hinv : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℝ => A⁻¹) S :=
    locallyLipschitzOn_matrix_inverse_posDef.continuousOn
  have hm : Measurable (S.piecewise (fun A => A⁻¹) (fun _ => 0)) :=
    hinv.measurable_piecewise continuous_const.continuousOn measurableSet_posDef
  apply (hm.comp_aemeasurable hH.aemeasurable).aestronglyMeasurable.congr
  filter_upwards [hpos] with x hx
  exact S.piecewise_eq_of_mem _ _ hx

theorem sourceMetricUnroot_aestronglyMeasurable (d : SourceData μ) :
    AEStronglyMeasurable (canonicalMetricUnroot d.potential) (potentialMeasure d.potential) := by
  have hroot := inverseSqrtMatrix_aestronglyMeasurable_of_ae_posDef
    (measurable_coordinateHessian d.potential) (d.hessian_ae_source.mono fun _ hx => hx.1)
  exact inverse_aestronglyMeasurable_of_ae_posDef hroot
    (d.hessian_ae_source.mono fun _ hx => canonicalMetricRoot_posDef_at hx.1)

/-- A per-law bound only, used to pay the ordinary weak-gradient domain. -/
theorem sourceMetricUnroot_entry_bound (d : SourceData μ) (i j : Fin n) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      ‖canonicalMetricUnroot d.potential x i j‖ ≤ 16 / d.targetConvexityConstant + 1 := by
  have hM : 0 < 16 / d.targetConvexityConstant := div_pos (by norm_num) d.target_convexity_pos
  filter_upwards [d.hessian_ae_source] with x hx
  let S := canonicalMetricUnroot d.potential x
  have hgram := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A j j)
    (canonicalMetricUnroot_gram_at hx.1)
  have hsq : S i j ^ 2 ≤ coordinateHessian d.potential x j j := by
    calc
      _ ≤ ∑ k : Fin n, S k j ^ 2 :=
        Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin n => (S k j) ^ 2)
          (fun k _ => sq_nonneg (S k j)) (Finset.mem_univ i)
      _ = _ := by simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hgram
  have hentry := coordinateHessian_entry_bound_of_gradient_lipschitz d.gradient_lipschitz x j j
  change ‖coordinateHessian d.potential x j j‖ ≤ 16 / d.targetConvexityConstant at hentry
  rw [Real.norm_eq_abs] at hentry
  have hH : coordinateHessian d.potential x j j ≤ 16 / d.targetConvexityConstant :=
    (le_abs_self _).trans hentry
  rw [Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs]
  change S i j ^ 2 ≤ _
  nlinarith [sq_nonneg (16 / d.targetConvexityConstant)]

private def boundedMultiplier {α : Type*} [MeasurableSpace α] (ρ : Measure α)
    (m : α → ℝ) {C : ℝ} (hm : AEStronglyMeasurable m ρ)
    (hb : ∀ᵐ x ∂ρ, ‖m x‖ ≤ C) : Lp ℝ 2 ρ →L[ℝ] Lp ℝ 2 ρ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL ρ (⊤ : ℝ≥0∞) 2 2 ((memLp_top_of_bound hm C hb).toLp m)

def sourceUnrootMultiplier (d : SourceData μ) (i j : Fin n) :
    Lp ℝ 2 (potentialMeasure d.potential) →L[ℝ] Lp ℝ 2 (potentialMeasure d.potential) :=
  boundedMultiplier (potentialMeasure d.potential) (fun x => canonicalMetricUnroot d.potential x i j)
    ((continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable (sourceMetricUnroot_aestronglyMeasurable d)))
    (sourceMetricUnroot_entry_bound d i j)

theorem sourceUnrootMultiplier_coe (d : SourceData μ) (i j : Fin n)
    (u : Lp ℝ 2 (potentialMeasure d.potential)) :
    (sourceUnrootMultiplier d i j u : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => canonicalMetricUnroot d.potential x i j * u x := by
  let m : Space n → ℝ := fun x => canonicalMetricUnroot d.potential x i j
  let hm : MemLp m (⊤ : ℝ≥0∞) (potentialMeasure d.potential) := memLp_top_of_bound
    ((continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable (sourceMetricUnroot_aestronglyMeasurable d)))
    (16 / d.targetConvexityConstant + 1) (sourceMetricUnroot_entry_bound d i j)
  have he := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (hm.toLp m) u
  change ((ContinuousLinearMap.mul ℝ ℝ).holder 2 (hm.toLp m) u : Space n → ℝ) =ᵐ[
    potentialMeasure d.potential] fun x => m x * u x
  filter_upwards [he, hm.coeFn_toLp] with x hx hm'
  rw [hx, ContinuousLinearMap.mul_apply', hm']

def sourceOrdinaryAmbientMap (d : SourceData μ) :
    WeightedEnergyAmbient d.potential →L[ℝ] WeightedEnergyAmbient d.potential :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure d.potential))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (Fin.cases
        (PiLp.proj 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure d.potential)) 0)
        (fun i : Fin n => ∑ j : Fin n, (sourceUnrootMultiplier d i j).comp
          (PiLp.proj 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure d.potential)) j.succ))))

@[simp] theorem sourceOrdinaryAmbientMap_zero (d : SourceData μ)
    (U : WeightedEnergyAmbient d.potential) : sourceOrdinaryAmbientMap d U 0 = U 0 := rfl

@[simp] theorem sourceOrdinaryAmbientMap_succ (d : SourceData μ)
    (U : WeightedEnergyAmbient d.potential) (i : Fin n) :
    sourceOrdinaryAmbientMap d U i.succ =
      ∑ j : Fin n, sourceUnrootMultiplier d i j (U j.succ) := by
  simp [sourceOrdinaryAmbientMap]

theorem sourceOrdinaryAmbientMap_maps_core (d : SourceData μ)
    {U : WeightedEnergyAmbient d.potential}
    (hU : U ∈ smoothCanonicalMetricGraphSet d.potential) :
    sourceOrdinaryAmbientMap d U ∈ smoothCenteredGradientGraphSet d.potential := by
  obtain ⟨f, hf, hc, hv, hd⟩ := hU
  refine ⟨f, hf, hc, ?_, ?_⟩
  · simpa only [sourceOrdinaryAmbientMap_zero] using hv
  · intro i
    rw [sourceOrdinaryAmbientMap_succ]
    have hmul : ∀ᵐ x ∂potentialMeasure d.potential, ∀ j : Fin n,
        sourceUnrootMultiplier d i j (U j.succ) x =
          canonicalMetricUnroot d.potential x i j * U j.succ x :=
      ae_all_iff.mpr (fun j => sourceUnrootMultiplier_coe d i j _)
    have hderiv : ∀ᵐ x ∂potentialMeasure d.potential, ∀ j : Fin n,
        U j.succ x = canonicalMetricDerivative d.potential f j x := ae_all_iff.mpr hd
    filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun j : Fin n => sourceUnrootMultiplier d i j (U j.succ)), hmul, hderiv,
      d.hessian_ae_source] with x hx hm hd' hpos
    rw [hx]
    simp only [Finset.sum_apply]
    calc
      _ = ∑ j : Fin n, canonicalMetricUnroot d.potential x i j *
          canonicalMetricDerivative d.potential f j x := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hm j, hd' j]
      _ = _ := by
        change (canonicalMetricUnroot d.potential x *ᵥ
          (canonicalMetricRoot d.potential x *ᵥ (fun j => coordinateDerivative f j x))) i = _
        rw [Matrix.mulVec_mulVec, canonicalMetricUnroot_mul_root_at hpos.1, Matrix.one_mulVec]

theorem sourceOrdinaryAmbientMap_mem_graph (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) :
    sourceOrdinaryAmbientMap d (U : WeightedEnergyAmbient d.potential) ∈
      weightedCenteredGradientGraph d.potential := by
  have hs : Submodule.span ℝ (smoothCanonicalMetricGraphSet d.potential) ≤
      (weightedCenteredGradientGraph d.potential).comap
        (sourceOrdinaryAmbientMap d).toLinearMap := by
    apply Submodule.span_le.mpr
    intro W hW
    exact Submodule.le_topologicalClosure _
      (Submodule.subset_span (sourceOrdinaryAmbientMap_maps_core d hW))
  have hclosed : IsClosed (weightedCenteredGradientGraph d.potential :
      Set (WeightedEnergyAmbient d.potential)) := Submodule.isClosed_topologicalClosure _
  exact (Submodule.topologicalClosure_minimal _ hs
    (hclosed.preimage (sourceOrdinaryAmbientMap d).continuous)) U.property

/- The construction is hidden behind its ambient-value specification. This
keeps every later weak-identity conversion from reducing the complete
codRestrict / finite-product / Holder multiplication implementation. -/
private theorem exists_sourceOrdinaryH1Embedding (d : SourceData μ) :
    ∃ E : CanonicalMetricH1 d.potential →L[ℝ] WeightedCenteredH1 d.potential,
      ∀ U, (E U : WeightedEnergyAmbient d.potential) =
        sourceOrdinaryAmbientMap d (U : WeightedEnergyAmbient d.potential) := by
  let E : CanonicalMetricH1 d.potential →L[ℝ] WeightedCenteredH1 d.potential :=
    ((sourceOrdinaryAmbientMap d).comp (canonicalMetricGraph d.potential).subtypeL).codRestrict
      (weightedCenteredGradientGraph d.potential) (sourceOrdinaryAmbientMap_mem_graph d)
  exact ⟨E, fun _ => rfl⟩

/-- Actual ordinary weak-gradient domain of the same canonical form value.
Its named specification exposes exactly the ambient graph coordinates. -/
def sourceOrdinaryH1Embedding (d : SourceData μ) :
    CanonicalMetricH1 d.potential →L[ℝ] WeightedCenteredH1 d.potential :=
  Classical.choose (exists_sourceOrdinaryH1Embedding d)

theorem sourceOrdinaryH1Embedding_coe (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) :
    (sourceOrdinaryH1Embedding d U : WeightedEnergyAmbient d.potential) =
      sourceOrdinaryAmbientMap d (U : WeightedEnergyAmbient d.potential) :=
  Classical.choose_spec (exists_sourceOrdinaryH1Embedding d) U

@[simp] theorem sourceOrdinaryH1Embedding_value (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) :
    weightedH1Value d.potential (sourceOrdinaryH1Embedding d U) = canonicalMetricValue d.potential U := by
  rw [weightedH1Value_apply, sourceOrdinaryH1Embedding_coe,
    sourceOrdinaryAmbientMap_zero, canonicalMetricValue_apply]

theorem sourceOrdinaryH1Embedding_derivative (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) (i : Fin n) :
    weightedH1Derivative d.potential i (sourceOrdinaryH1Embedding d U) =
      ∑ j : Fin n, sourceUnrootMultiplier d i j (canonicalMetricGradient d.potential j U) := by
  rw [weightedH1Derivative_apply, sourceOrdinaryH1Embedding_coe,
    sourceOrdinaryAmbientMap_succ]
  rfl

/-- The actual coordinate weak derivative is obtained from the metric
graph; no local H1 or smoothness of its value is assumed. -/
theorem sourceMetricH1_unweighted_weak_identity (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    (∫ x, canonicalMetricValue d.potential U x * coordinateDerivative ψ i x) =
      -(∫ x, weightedH1Derivative d.potential i (sourceOrdinaryH1Embedding d U) x * ψ x) := by
  calc
    (∫ x, canonicalMetricValue d.potential U x * coordinateDerivative ψ i x) =
        ∫ x, weightedH1Value d.potential (sourceOrdinaryH1Embedding d U) x *
          coordinateDerivative ψ i x := by
      rw [sourceOrdinaryH1Embedding_value]
    _ = _ := weightedH1_unweighted_weak_identity d.source_C1
      (sourceOrdinaryH1Embedding d U) hψ hc i

theorem sourceMetricInverse_unweighted_weak_identity (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    (∫ x, sourceMetricInverse d g x * coordinateDerivative ψ i x) =
      -(∫ x, weightedH1Derivative d.potential i
        (sourceOrdinaryH1Embedding d (sourceMetricInverseH1 d g)) x * ψ x) :=
  sourceMetricH1_unweighted_weak_identity d _ hψ hc i

end KLSConstantImprovement.ActualWeakCanonicalMetricOrdinaryGraph
end

#print axioms KLSConstantImprovement.ActualWeakCanonicalMetricOrdinaryGraph.sourceMetricUnroot_entry_bound
#print axioms KLSConstantImprovement.ActualWeakCanonicalMetricOrdinaryGraph.sourceOrdinaryAmbientMap_maps_core
#print axioms KLSConstantImprovement.ActualWeakCanonicalMetricOrdinaryGraph.sourceOrdinaryH1Embedding
#print axioms KLSConstantImprovement.ActualWeakCanonicalMetricOrdinaryGraph.sourceMetricInverse_unweighted_weak_identity
