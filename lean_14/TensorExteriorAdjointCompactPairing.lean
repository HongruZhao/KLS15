import WeightedLpCompactPairings

/-! The actual Hilbert adjoint satisfies the literal compact exterior
pairing, with no formal-adjoint or weak-divergence premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology LinearPMap
namespace KLS.DeterministicBridgeIntegration
variable {n q : ℕ} {φ : Space n → ℝ}

theorem tensorExteriorOne_adjoint_compact_pairing (hφ : ContDiff ℝ 1 φ)
    (w : (tensorExteriorOneOperator hφ q).adjoint.domain)
    (f : TensorOneFormIndex n q → Space n → ℝ)
    (hf : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (f a))
    (hc : ∀ a, HasCompactSupport (f a))
    (hs : ∀ x, WithLp.toLp 2 (fun a => f a x) ∈ tensorOneFormSymmetricFiber n q) :
    inner ℝ ((tensorExteriorOneOperator hφ q).adjoint w).val
      (finiteMatrixLp f (fun a => memLp_of_continuous_hasCompactSupport hφ.continuous
        (hf a).continuous (hc a))) =
    inner ℝ (w : TensorTwoFormL2 φ q).val
      (finiteMatrixLp (tensorExteriorOneDifferential f) (fun z =>
        memLp_of_continuous_hasCompactSupport hφ.continuous
          (tensorExteriorOneDifferential_contDiff hf z).continuous
          (tensorExteriorOneDifferential_compact hc z))) := by
  let flp := fun a => memLp_of_continuous_hasCompactSupport hφ.continuous (hf a).continuous (hc a)
  let dlp := fun z => memLp_of_continuous_hasCompactSupport hφ.continuous
    (tensorExteriorOneDifferential_contDiff hf z).continuous (tensorExteriorOneDifferential_compact hc z)
  have hC := (finiteMatrixLp_mem_oneForm_iff flp).mpr (Eventually.of_forall hs)
  have hD := (finiteMatrixLp_mem_twoForm_iff dlp).mpr
    (Eventually.of_forall (tensorExteriorOneDifferential_compatible hs))
  have hw : HasWeakMatrixDerivative (tensorExteriorOneDerivativeMatrix n q) f
      (tensorExteriorOneDifferential f) := by
    have he : matrixDifferential (tensorExteriorOneDerivativeMatrix n q) f =
        tensorExteriorOneDifferential f :=
      funext fun z => funext fun x => tensorExteriorOne_matrixDifferential f z x
    exact he ▸ matrixDifferential_hasWeakMatrixDerivative (tensorExteriorOneDerivativeMatrix n q)
      (fun a => (hf a).of_le (by simp))
  have hg := finiteMatrixLp_mem_weightedMatrixFiberGraph hφ
    (tensorExteriorOneDerivativeMatrix n q) (tensorOneFormL2Subspace φ q)
    (tensorTwoFormL2Subspace φ q) flp dlp hC hD hw
  have hgraph : ((⟨finiteMatrixLp f flp, hC⟩ : TensorOneFormL2 φ q),
      (⟨finiteMatrixLp (tensorExteriorOneDifferential f) dlp, hD⟩ : TensorTwoFormL2 φ q)) ∈
      (tensorExteriorOneOperator hφ q).graph := by
    change _ ∈ (weightedMatrixFiberOperator hφ (tensorExteriorOneDerivativeMatrix n q)
      (tensorOneFormL2Subspace φ q) (tensorTwoFormL2Subspace φ q)).graph
    rw [weightedMatrixFiberOperator_graph]
    exact hg
  rcases (tensorExteriorOneOperator hφ q).mem_graph_iff.mp hgraph with ⟨u, hu, hAu⟩
  have he := LinearPMap.adjoint_isFormalAdjoint (tensorExteriorOneOperator_domain_dense hφ q) w u
  rw [hu, hAu] at he
  exact he

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorExteriorOne_adjoint_compact_pairing
