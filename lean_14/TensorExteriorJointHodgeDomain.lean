import TensorExteriorAdjointWeakDomain

/-! The true joint domain of the actual closed Hilbert complex is contained
in the full distributional constrained Hodge domain, with exact graph energy. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology LinearPMap
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {φ : Space n → ℝ}

def tensorHodgeJointOutput (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (q : ℕ)
    (w : (tensorExteriorOneOperator (hφ.of_le (by simp)) q).adjoint.domain)
    (hwB : (w : TensorTwoFormL2 φ q) ∈ (tensorExteriorTwoOperator (hφ.of_le (by simp)) q).domain) :
    TensorHodgeOutputIndex n q → Space n → ℝ
  | Sum.inl z, x => ((tensorExteriorTwoOperator (hφ.of_le (by simp)) q)
      ⟨(w : TensorTwoFormL2 φ q),hwB⟩).val z x
  | Sum.inr a, x => ((tensorExteriorOneOperator (hφ.of_le (by simp)) q).adjoint w).val a x

lemma tensorHodgeJointOutput_memLp (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (q : ℕ)
    (w : (tensorExteriorOneOperator (hφ.of_le (by simp)) q).adjoint.domain)
    (hwB : (w : TensorTwoFormL2 φ q) ∈ (tensorExteriorTwoOperator (hφ.of_le (by simp)) q).domain)
    (z : TensorHodgeOutputIndex n q) :
    MemLp (tensorHodgeJointOutput hφ q w hwB z) 2 (potentialMeasure φ) := by
  cases z with
  | inl z => exact Lp.memLp _
  | inr a => exact Lp.memLp _

/-- Genuine adjoint-domain identification in the direction required by
curvature: all true joint-domain fields satisfy the literal weighted
matrix equations and every physical fiber constraint. -/
theorem tensorExterior_joint_hasWeakConstrainedHodge
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (q : ℕ)
    (w : (tensorExteriorOneOperator (hφ.of_le (by simp)) q).adjoint.domain)
    (hwB : (w : TensorTwoFormL2 φ q) ∈ (tensorExteriorTwoOperator (hφ.of_le (by simp)) q).domain) :
    HasWeakConstrainedTensorHodge φ q
      (fun z x => (w : TensorTwoFormL2 φ q).val z x) (tensorHodgeJointOutput hφ q w hwB) := by
  let v : (tensorExteriorTwoOperator (hφ.of_le (by simp)) q).domain := ⟨(w : TensorTwoFormL2 φ q),hwB⟩
  have hbgraph : ((w : TensorTwoFormL2 φ q), tensorExteriorTwoOperator (hφ.of_le (by simp)) q v) ∈
      (tensorExteriorTwoOperator (hφ.of_le (by simp)) q).graph :=
    (tensorExteriorTwoOperator (hφ.of_le (by simp)) q).mem_graph_iff.mpr ⟨v,rfl,rfl⟩
  change _ ∈ (weightedMatrixFiberOperator (hφ.of_le (by simp))
    (tensorExteriorTwoDerivativeMatrix n q) (tensorTwoFormL2Subspace φ q) ⊤).graph at hbgraph
  rw [weightedMatrixFiberOperator_graph, mem_weightedMatrixFiberGraph_iff] at hbgraph
  have ha := tensorExteriorOne_adjoint_hasWeakProjectedDivergence hφ w
  refine ⟨?_, ?_⟩
  · intro ψ hψ hc z
    cases z with
    | inl z =>
      have he := hbgraph ψ hψ hc z
      simpa only [tensorHodgeJointOutput, matrixZeroth, tensorHodgeDriftMatrix,
        zero_mul, Finset.sum_const_zero, sub_zero, tensorExteriorTwoDerivativeMatrix] using he
    | inr a => exact ha ψ hψ hc a
  · have hm : finiteMatrixLp (fun z x => (w : TensorTwoFormL2 φ q).val z x)
        (fun z => Lp.memLp ((w : TensorTwoFormL2 φ q).val z)) ∈ tensorTwoFormL2Subspace φ q := by
      rw [finiteMatrixLp_coe_eq]
      exact (w : TensorTwoFormL2 φ q).property
    have hcμ := (finiteMatrixLp_mem_constraint_iff (tensorTwoFormConstraintMatrix n q)
      (fun z => Lp.memLp ((w : TensorTwoFormL2 φ q).val z))).mp hm
    exact fun a => (volume_absolutelyContinuous_potentialMeasure hφ.continuous).ae_eq (hcμ a)

/-- Exact equality between the literal combined finite L² output energy
and the actual Hilbert-complex graph energy. -/
theorem tensorHodgeJointOutput_norm_sq
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (q : ℕ)
    (w : (tensorExteriorOneOperator (hφ.of_le (by simp)) q).adjoint.domain)
    (hwB : (w : TensorTwoFormL2 φ q) ∈ (tensorExteriorTwoOperator (hφ.of_le (by simp)) q).domain) :
    ‖finiteMatrixLp (tensorHodgeJointOutput hφ q w hwB) (tensorHodgeJointOutput_memLp hφ q w hwB)‖^2 =
      ‖(tensorExteriorOneOperator (hφ.of_le (by simp)) q).adjoint w‖^2 +
      ‖tensorExteriorTwoOperator (hφ.of_le (by simp)) q ⟨(w : TensorTwoFormL2 φ q),hwB⟩‖^2 := by
  rw [finiteMatrixLp_norm_sq, Fintype.sum_sum_type]
  have hb := finiteMatrixLp_norm_sq
    (fun z x => (tensorExteriorTwoOperator (hφ.of_le (by simp)) q
      ⟨(w : TensorTwoFormL2 φ q),hwB⟩).val z x)
    (fun z => Lp.memLp ((tensorExteriorTwoOperator (hφ.of_le (by simp)) q
      ⟨(w : TensorTwoFormL2 φ q),hwB⟩).val z))
  have ha := finiteMatrixLp_norm_sq
    (fun a x => ((tensorExteriorOneOperator (hφ.of_le (by simp)) q).adjoint w).val a x)
    (fun a => Lp.memLp (((tensorExteriorOneOperator (hφ.of_le (by simp)) q).adjoint w).val a))
  rw [finiteMatrixLp_coe_eq] at ha hb
  dsimp only [tensorHodgeJointOutput]
  rw [← ha, ← hb, add_comm]
  rfl

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorExterior_joint_hasWeakConstrainedHodge
#print axioms KLS.DeterministicBridgeIntegration.tensorHodgeJointOutput_norm_sq
