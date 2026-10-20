import TensorExteriorCompactDomain
import TensorExteriorWeakChain

/-! The actual closed constrained exterior operators form a Hilbert complex. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology LinearPMap
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {φ : Space n → ℝ}

theorem tensorExteriorOperators_chain (hφ : ContDiff ℝ 1 φ) (q : ℕ)
    (u : (tensorExteriorOneOperator hφ q).domain) :
    tensorExteriorOneOperator hφ q u ∈ (tensorExteriorTwoOperator hφ q).ker := by
  let v := tensorExteriorOneOperator hφ q u
  have hgraph : ((u : TensorOneFormL2 φ q), v) ∈ (tensorExteriorOneOperator hφ q).graph :=
    (tensorExteriorOneOperator hφ q).mem_graph_iff.mpr ⟨u, rfl, rfl⟩
  change ((u : TensorOneFormL2 φ q), v) ∈
    (weightedMatrixFiberOperator hφ (tensorExteriorOneDerivativeMatrix n q)
      (tensorOneFormL2Subspace φ q) (tensorTwoFormL2Subspace φ q)).graph at hgraph
  rw [weightedMatrixFiberOperator_graph, mem_weightedMatrixFiberGraph_iff] at hgraph
  have hc := hgraph.exterior_chain
  have hz (a : TensorThreeFormIndex n q) : (0 : Space n → ℝ) =ᵐ[volume]
      (fun x => ((0 : TensorThreeFormL2 φ q).val a x)) :=
    ((volume_absolutelyContinuous_potentialMeasure hφ.continuous).ae_eq
      (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := potentialMeasure φ))).symm
  have hw := hc.congr_ae (fun _ => Filter.EventuallyEq.rfl) hz
  have hb : (v, (0 : TensorThreeFormL2 φ q)) ∈ (tensorExteriorTwoOperator hφ q).graph := by
    change (v, (0 : TensorThreeFormL2 φ q)) ∈
      (weightedMatrixFiberOperator hφ (tensorExteriorTwoDerivativeMatrix n q)
        (tensorTwoFormL2Subspace φ q) ⊤).graph
    rw [weightedMatrixFiberOperator_graph, mem_weightedMatrixFiberGraph_iff]
    exact hw
  rcases (tensorExteriorTwoOperator hφ q).mem_graph_iff.mp hb with ⟨w, hwv, hwo⟩
  exact LinearPMap.mem_ker_iff.mpr ⟨w, hwv.symm, hwo⟩

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorExteriorOperators_chain
