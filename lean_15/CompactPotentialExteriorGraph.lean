import CompactPotentialCurvatureTest
import TensorExteriorCompactDomain
import OrderedOneFormKernel

/-! The actual compact weighted divergence belongs to the full exterior
operator graph, and its exterior derivative is the literal curvature curl. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators ENNReal RealInnerProductSpace LinearPMap
namespace KLS.DeterministicBridgeIntegration
open KLS
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {n r : ℕ} {φ ψ : Space n → ℝ}

def compactPotentialAdjointOneForm (φ ψ : Space n → ℝ) (r : ℕ)
    (a : TensorOneFormIndex n (r+1)) (x : Space n) : ℝ :=
  tensorAdjointDivergence φ (coordinatePotentialTensor ψ (r+3)) (Fin.cons a.2 a.1) x

lemma compactPotentialAdjointOneForm_memLp (hφ : ContDiff ℝ 2 φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (a : TensorOneFormIndex n (r+1)) :
    MemLp (compactPotentialAdjointOneForm φ ψ r a) 2 (potentialMeasure φ) :=
  memLp_of_continuous_hasCompactSupport hφ.continuous
    (contDiff_tensorAdjointDivergence hφ
      (fun I => (coordinatePotentialTensor_contDiff hψ (r+3) I).of_le (by simp)) _).continuous
    (hasCompactSupport_tensorAdjointDivergence
      (coordinatePotentialTensor_hasCompactSupport hc (r+3)) _)

lemma compactPotentialAdjointOneForm_differential (hφ : ContDiff ℝ 2 φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : TensorTwoFormIndex n (r+1)) (x : Space n) :
    tensorExteriorOneDifferential (compactPotentialAdjointOneForm φ ψ r) z x =
      tensorCurvatureCurl (coordinateHessian φ x)
        (fun I => coordinatePotentialTensor ψ (r+3) I x) z := by
  unfold tensorExteriorOneDifferential compactPotentialAdjointOneForm
  rw [tensorAdjointDivergence_curl hφ
    (fun I => (coordinatePotentialTensor_contDiff hψ (r+3) I).of_le (by simp))
    (coordinatePotentialTensor_symmetric hψ (r+3))
    (coordinatePotentialTensor_compatible hψ (r+2))]
  rfl

theorem compactPotentialAdjointOneForm_graph (hφ : ContDiff ℝ 2 φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : ∀ x, WithLp.toLp 2 (fun a => compactPotentialAdjointOneForm φ ψ r a x)
      ∈ tensorOneFormSymmetricFiber n (r+1)) :
    ∃ hy : finiteMatrixLp (compactPotentialAdjointOneForm φ ψ r)
        (compactPotentialAdjointOneForm_memLp hφ hψ hc) ∈ tensorOneFormL2Subspace φ (r+1),
    ∃ hz : compactPotentialCurvatureCurlLp hφ hψ hc r ∈ tensorTwoFormL2Subspace φ (r+1),
      (⟨_, hy⟩, ⟨_, hz⟩) ∈ (tensorExteriorOneOperator (hφ.of_le (by norm_num)) (r+1)).graph := by
  let f := compactPotentialAdjointOneForm φ ψ r
  let g := fun z x => tensorCurvatureCurl (coordinateHessian φ x)
    (fun I => coordinatePotentialTensor ψ (r+3) I x) z
  have he : tensorExteriorOneDifferential f = g :=
    funext fun z => funext fun x => compactPotentialAdjointOneForm_differential hφ hψ z x
  have hy := (finiteMatrixLp_mem_oneForm_iff
    (compactPotentialAdjointOneForm_memLp hφ hψ hc)).mpr (Eventually.of_forall hs)
  have hz : compactPotentialCurvatureCurlLp hφ hψ hc r ∈ tensorTwoFormL2Subspace φ (r+1) := by
    apply (finiteMatrixLp_mem_twoForm_iff (compactPotentialCurvatureCurl_memLp hφ hψ hc)).mpr
    exact Eventually.of_forall fun x => by
      change TensorTwoFormCompatible (fun z => g z x)
      rw [← he]
      exact tensorExteriorOneDifferential_compatible hs x
  refine ⟨hy, hz, ?_⟩
  change (⟨finiteMatrixLp f _, hy⟩, ⟨finiteMatrixLp g _, hz⟩) ∈
    (weightedMatrixFiberOperator (hφ.of_le (by norm_num))
      (tensorExteriorOneDerivativeMatrix n (r+1))
      (tensorOneFormL2Subspace φ (r+1)) (tensorTwoFormL2Subspace φ (r+1))).graph
  rw [weightedMatrixFiberOperator_graph]
  apply finiteMatrixLp_mem_weightedMatrixFiberGraph
  have hw := matrixDifferential_hasWeakMatrixDerivative (f := f)
    (tensorExteriorOneDerivativeMatrix n (r+1))
    (fun a => contDiff_tensorAdjointDivergence hφ
      (fun I => (coordinatePotentialTensor_contDiff hψ (r+3) I).of_le (by simp)) (Fin.cons a.2 a.1))
  have hd : matrixDifferential (tensorExteriorOneDerivativeMatrix n (r+1)) f = g :=
    funext fun z => funext fun x => (tensorExteriorOne_matrixDifferential f z x).trans
      (compactPotentialAdjointOneForm_differential hφ hψ z x)
  exact hd ▸ hw

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialAdjointOneForm_graph
