import WeightedMatrixDerivativeOperator

/-! Actual maximal ordinary-distributional operators between fixed closed
weighted L² tensor subspaces, implemented as genuine LinearPMaps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology LinearPMap
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {φ : Space n → ℝ}
variable {ι ρ : Type*} [Fintype ι] [Fintype ρ]

def weightedMatrixFiberGraph (hφ : ContDiff ℝ 1 φ) (A : ρ → Fin n → ι → ℝ)
    (C : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ι))
    (D : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ρ)) :
    Submodule ℝ (C × D) :=
  (weightedMatrixDerivativeGraph hφ A).comap (C.subtype.prodMap D.subtype)

lemma mem_weightedMatrixFiberGraph_iff (hφ : ContDiff ℝ 1 φ)
    (A : ρ → Fin n → ι → ℝ)
    (C : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ι))
    (D : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ρ)) (p : C × D) :
    p ∈ weightedMatrixFiberGraph hφ A C D ↔
      HasWeakMatrixDerivative A (fun j x => (p.1 : CenteredL2.Family (potentialMeasure φ) ι) j x)
        (fun a x => (p.2 : CenteredL2.Family (potentialMeasure φ) ρ) a x) := by
  exact mem_weightedMatrixDerivativeGraph_iff hφ A _

lemma weightedMatrixFiberGraph_singleValued (hφ : ContDiff ℝ 1 φ)
    (A : ρ → Fin n → ι → ℝ)
    (C : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ι))
    (D : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ρ)) (p : C × D)
    (hp : p ∈ weightedMatrixFiberGraph hφ A C D) (hz : p.1 = 0) : p.2 = 0 := by
  apply Subtype.ext
  exact weightedMatrixDerivativeGraph_singleValued hφ A _ hp
    (congrArg (fun v : C => (v : CenteredL2.Family (potentialMeasure φ) ι)) hz)

lemma weightedMatrixFiberGraph_isClosed (hφ : ContDiff ℝ 1 φ)
    (A : ρ → Fin n → ι → ℝ)
    (C : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ι))
    (D : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ρ)) :
    IsClosed (weightedMatrixFiberGraph hφ A C D : Set (C × D)) :=
  (weightedMatrixDerivativeGraph_isClosed hφ A).preimage
    (C.subtypeL.continuous.prodMap D.subtypeL.continuous)

def weightedMatrixFiberOperator (hφ : ContDiff ℝ 1 φ) (A : ρ → Fin n → ι → ℝ)
    (C : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ι))
    (D : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ρ)) : C →ₗ.[ℝ] D :=
  (weightedMatrixFiberGraph hφ A C D).toLinearPMap

lemma weightedMatrixFiberOperator_graph (hφ : ContDiff ℝ 1 φ)
    (A : ρ → Fin n → ι → ℝ)
    (C : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ι))
    (D : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ρ)) :
    (weightedMatrixFiberOperator hφ A C D).graph = weightedMatrixFiberGraph hφ A C D :=
  Submodule.toLinearPMap_graph_eq _ (weightedMatrixFiberGraph_singleValued hφ A C D)

/-- Closedness belongs to the literal full distributional graph; it is
not a consequence assumed from a compact restriction. -/
theorem weightedMatrixFiberOperator_isClosed (hφ : ContDiff ℝ 1 φ)
    (A : ρ → Fin n → ι → ℝ)
    (C : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ι))
    (D : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ρ)) :
    (weightedMatrixFiberOperator hφ A C D).IsClosed := by
  rw [LinearPMap.IsClosed, weightedMatrixFiberOperator_graph]
  exact weightedMatrixFiberGraph_isClosed hφ A C D

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.weightedMatrixFiberOperator_isClosed
