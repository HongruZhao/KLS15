import TensorExteriorHilbertOperators
import WeightedCompactFiberDensity
import ProjectedTensorDivergence
import ClosedHilbertComplexVariational

/-! Literal identification of ordered symmetric tensors with constrained
one-forms. The actual normalized distributional exterior operator has
exactly the existing compatible tensor kernel, and its projection is the
same orthogonal projection used by the compact Bochner identity. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter LinearPMap
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n q : ℕ} {φ : Space n → ℝ}

def orderedOneFormIndexEquiv (n q : ℕ) :
    OrderedTensorIndex n (q + 1) ≃ TensorOneFormIndex n q where
  toFun J := (Fin.tail J, J 0)
  invFun a := Fin.cons a.2 a.1
  left_inv J := Fin.cons_self_tail J
  right_inv a := by rcases a with ⟨I,i⟩; simp

def orderedOneFormLIE (φ : Space n → ℝ) (q : ℕ) :
    OrderedTensorField φ (q + 1) ≃ₗᵢ[ℝ]
      CenteredL2.Family (potentialMeasure φ) (TensorOneFormIndex n q) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ (Lp ℝ 2 (potentialMeasure φ))
    (orderedOneFormIndexEquiv n q)

@[simp] lemma orderedOneFormLIE_apply (F : OrderedTensorField φ (q + 1))
    (a : TensorOneFormIndex n q) :
    orderedOneFormLIE φ q F a = F (Fin.cons a.2 a.1) := rfl

@[simp] lemma orderedOneFormLIE_symm_apply
    (u : CenteredL2.Family (potentialMeasure φ) (TensorOneFormIndex n q))
    (J : OrderedTensorIndex n (q + 1)) :
    (orderedOneFormLIE φ q).symm u J = u (Fin.tail J,J 0) := by
  have he := (orderedOneFormLIE φ q).apply_symm_apply u
  simpa only [orderedOneFormLIE_apply, Fin.cons_self_tail] using
    congrArg (fun F : CenteredL2.Family (potentialMeasure φ) (TensorOneFormIndex n q) =>
      F (Fin.tail J,J 0)) he

lemma orderedOneFormLIE_mem_iff (F : OrderedTensorField φ (q + 1)) :
    orderedOneFormLIE φ q F ∈ tensorOneFormL2Subspace φ q ↔
      F ∈ orderedTensorSymmetricSubspace φ (q + 1) := by
  classical
  rw [← finiteMatrixLp_coe_eq (orderedOneFormLIE φ q F),
    finiteMatrixLp_mem_oneForm_iff, mem_orderedTensorSymmetricSubspace_iff]
  constructor
  · intro h I J hIJ
    apply Lp.ext
    filter_upwards [h] with x hx
    have he := (mem_tensorOneFormSymmetricFiber_iff _).mp hx
      (Fin.tail I,I 0) (Fin.tail J,J 0)
    simpa only [orderedOneFormLIE_apply, Fin.cons_self_tail] using
      he (by simpa only [Fin.cons_self_tail] using hIJ)
  · intro h
    have he (a b : TensorOneFormIndex n q) :
        ∀ᵐ x ∂potentialMeasure φ,
          List.Perm (List.ofFn (Fin.cons a.2 a.1)) (List.ofFn (Fin.cons b.2 b.1)) →
          orderedOneFormLIE φ q F a x = orderedOneFormLIE φ q F b x := by
      by_cases hp : List.Perm (List.ofFn (Fin.cons a.2 a.1)) (List.ofFn (Fin.cons b.2 b.1))
      · have hv := h (Fin.cons a.2 a.1) (Fin.cons b.2 b.1) hp
        exact Eventually.of_forall fun x _ => congrArg (fun v : Lp ℝ 2 (potentialMeasure φ) => v x) hv
      · exact Eventually.of_forall fun _ hh => (hp hh).elim
    have hall : ∀ᵐ x ∂potentialMeasure φ, ∀ a b,
        List.Perm (List.ofFn (Fin.cons a.2 a.1)) (List.ofFn (Fin.cons b.2 b.1)) →
          orderedOneFormLIE φ q F a x = orderedOneFormLIE φ q F b x :=
      Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr fun b => he a b
    filter_upwards [hall] with x hx
    exact (mem_tensorOneFormSymmetricFiber_iff _).mpr hx

def symmetricOrderedOneFormLIE (φ : Space n → ℝ) (q : ℕ) :
    ↥(orderedTensorSymmetricSubspace φ (q + 1)) ≃ₗᵢ[ℝ] TensorOneFormL2 φ q where
  toFun F := ⟨orderedOneFormLIE φ q F.val, (orderedOneFormLIE_mem_iff F.val).mpr F.property⟩
  invFun u := ⟨(orderedOneFormLIE φ q).symm u.val,
    (orderedOneFormLIE_mem_iff _).mp (by simpa using u.property)⟩
  left_inv F := Subtype.ext ((orderedOneFormLIE φ q).symm_apply_apply F.val)
  right_inv u := Subtype.ext ((orderedOneFormLIE φ q).apply_symm_apply u.val)
  map_add' F G := Subtype.ext ((orderedOneFormLIE φ q).map_add F.val G.val)
  map_smul' a F := Subtype.ext ((orderedOneFormLIE φ q).map_smul a F.val)
  norm_map' F := (orderedOneFormLIE φ q).norm_map F.val

@[simp] lemma symmetricOrderedOneFormLIE_coe
    (F : ↥(orderedTensorSymmetricSubspace φ (q + 1))) :
    (symmetricOrderedOneFormLIE φ q F).val = orderedOneFormLIE φ q F.val := rfl

lemma tensorExteriorOne_matrix_test (u : TensorOneFormL2 φ q)
    (ψ : Space n → ℝ) (z : TensorTwoFormIndex n q) :
    (∑ i, ∑ a, tensorExteriorOneDerivativeMatrix n q z i a *
      (∫ x, (u.val a x) * coordinateDerivative ψ i x)) =
      (1 / Real.sqrt 2) *
        ((∫ x, u.val (z.1,z.2.2) x * coordinateDerivative ψ z.2.1 x) -
         (∫ x, u.val (z.1,z.2.1) x * coordinateDerivative ψ z.2.2 x)) := by
  classical
  simp [tensorExteriorOneDerivativeMatrix, mul_sub, sub_mul,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Fintype.sum_prod_type,
    Finset.sum_ite_irrel, and_comm, ite_and]

lemma tensorExteriorOneOperator_kernel_graph_iff (hφ : ContDiff ℝ 1 φ)
    (u : TensorOneFormL2 φ q) :
    u ∈ (tensorExteriorOneOperator hφ q).ker ↔
      HasWeakMatrixDerivative (tensorExteriorOneDerivativeMatrix n q)
        (fun a x => u.val a x) (fun _ _ => 0) := by
  have hzero (z : TensorTwoFormIndex n q) :
      (fun x => ((0 : TensorTwoFormL2 φ q).val z x)) =ᵐ[volume] 0 :=
    (volume_absolutelyContinuous_potentialMeasure hφ.continuous).ae_eq
      (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := potentialMeasure φ))
  have hg : u ∈ (tensorExteriorOneOperator hφ q).ker ↔
      (u,(0 : TensorTwoFormL2 φ q)) ∈ (tensorExteriorOneOperator hφ q).graph := by
    constructor
    · intro hu
      rcases LinearPMap.mem_ker_iff.mp hu with ⟨v,hv,hAv⟩
      exact (tensorExteriorOneOperator hφ q).mem_graph_iff.mpr ⟨v,hv.symm,hAv⟩
    · intro hu
      rcases (tensorExteriorOneOperator hφ q).mem_graph_iff.mp hu with ⟨v,hv,hAv⟩
      exact LinearPMap.mem_ker_iff.mpr ⟨v,hv.symm,hAv⟩
  rw [hg]
  change (u,(0 : TensorTwoFormL2 φ q)) ∈
    (weightedMatrixFiberOperator hφ (tensorExteriorOneDerivativeMatrix n q)
      (tensorOneFormL2Subspace φ q) (tensorTwoFormL2Subspace φ q)).graph ↔ _
  rw [weightedMatrixFiberOperator_graph, mem_weightedMatrixFiberGraph_iff]
  constructor
  · intro h ψ hψ hc z
    have he := h ψ hψ hc z
    have hz : (∫ x, (0 : TensorTwoFormL2 φ q).val z x * ψ x) = 0 := by
      calc
        _ = ∫ x, (0 : ℝ) * ψ x := by
          apply integral_congr_ae
          filter_upwards [hzero z] with x hx
          rw [hx]
          rfl
        _ = 0 := by simp
    simpa only [hz, Pi.zero_apply, zero_mul, integral_zero] using he
  · intro h ψ hψ hc z
    have he := h ψ hψ hc z
    have hz : (∫ x, (0 : TensorTwoFormL2 φ q).val z x * ψ x) = 0 := by
      calc
        _ = ∫ x, (0 : ℝ) * ψ x := by
          apply integral_congr_ae
          filter_upwards [hzero z] with x hx
          rw [hx]
          rfl
        _ = 0 := by simp
    simpa only [hz, Pi.zero_apply, zero_mul, integral_zero] using he

lemma tensorExteriorOneOperator_kernel_iff (hφ : ContDiff ℝ 1 φ)
    (u : TensorOneFormL2 φ q) :
    u ∈ (tensorExteriorOneOperator hφ q).ker ↔
      (orderedOneFormLIE φ q).symm u.val ∈ compatibleSymmetricTensorSubspace hφ (q + 1) := by
  rw [tensorExteriorOneOperator_kernel_graph_iff]
  have hs : (orderedOneFormLIE φ q).symm u.val ∈ orderedTensorSymmetricSubspace φ (q + 1) :=
    (orderedOneFormLIE_mem_iff _).mp (by simpa using u.property)
  change HasWeakMatrixDerivative _ _ _ ↔
    (orderedOneFormLIE φ q).symm u.val ∈ orderedTensorSymmetricSubspace φ (q + 1) ∧
    (orderedOneFormLIE φ q).symm u.val ∈ orderedTensorCurlSubspace hφ (q + 1)
  rw [and_iff_right hs, mem_orderedTensorCurlSubspace_succ_iff]
  constructor
  · intro h I
    rw [mem_weightedCurlFreeSubspace_iff]
    intro ψ hψ hc i j
    have he := h ψ hψ hc (I,(j,i))
    rw [tensorExteriorOne_matrix_test] at he
    have hr : 1 / Real.sqrt 2 ≠ (0 : ℝ) := by positivity
    have he' : (∫ x, u.val (I,i) x * coordinateDerivative ψ j x) =
        ∫ x, u.val (I,j) x * coordinateDerivative ψ i x := by
      apply sub_eq_zero.mp
      apply (mul_eq_zero.mp (neg_eq_zero.mp (by simpa using he.symm))).resolve_left hr
    simpa only [orderedTensorSlice_apply, orderedOneFormLIE_symm_apply,
      Fin.tail_cons, Fin.cons_zero] using he'
  · intro h ψ hψ hc z
    rw [tensorExteriorOne_matrix_test]
    have he := (mem_weightedCurlFreeSubspace_iff hφ _).mp (h z.1) ψ hψ hc z.2.2 z.2.1
    simp only [orderedTensorSlice_apply, orderedOneFormLIE_symm_apply,
      Fin.tail_cons, Fin.cons_zero] at he
    simp [he]


lemma tensorCompactProjection_mem_symmetric (hφ : ContDiff ℝ 1 φ)
    (F : OrderedTensorField φ (q + 1)) :
    tensorCompactProjection hφ (q + 1) F ∈ orderedTensorSymmetricSubspace φ (q + 1) :=
  ((compatibleSymmetricTensorSubspace hφ (q + 1)).starProjection_apply_mem F).1

/-- The actual kernel projection is transported from the existing C projection. -/
theorem symmetricOrderedOneForm_kernel_projection (hφ : ContDiff ℝ 1 φ)
    (F : ↥(orderedTensorSymmetricSubspace φ (q + 1))) :
    closedPartialKernelProjection (tensorExteriorOneOperator hφ q)
      (tensorExteriorOneOperator_isClosed hφ q) (symmetricOrderedOneFormLIE φ q F) =
      symmetricOrderedOneFormLIE φ q
        ⟨tensorCompactProjection hφ (q + 1) F.val, tensorCompactProjection_mem_symmetric hφ F.val⟩ := by
  let A := tensorExteriorOneOperator hφ q
  letI : CompleteSpace A.ker :=
    (closed_partial_operator_kernel_isClosed A (tensorExteriorOneOperator_isClosed hφ q)).completeSpace_coe
  change A.ker.starProjection (symmetricOrderedOneFormLIE φ q F) = _
  apply A.ker.eq_starProjection_of_mem_of_inner_eq_zero
  · apply (tensorExteriorOneOperator_kernel_iff hφ _).mpr
    change (orderedOneFormLIE φ q).symm
      (orderedOneFormLIE φ q (tensorCompactProjection hφ (q + 1) F.val)) ∈ _
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact (compatibleSymmetricTensorSubspace hφ (q + 1)).starProjection_apply_mem F.val
  · intro v hv
    let W : ↥(orderedTensorSymmetricSubspace φ (q + 1)) := (symmetricOrderedOneFormLIE φ q).symm v
    have hW : W.val ∈ compatibleSymmetricTensorSubspace hφ (q + 1) :=
      (tensorExteriorOneOperator_kernel_iff hφ v).mp hv
    have hP := (compatibleSymmetricTensorSubspace hφ (q + 1)).starProjection_inner_eq_zero
      F.val W.val hW
    have hvW : symmetricOrderedOneFormLIE φ q W = v :=
      (symmetricOrderedOneFormLIE φ q).apply_symm_apply v
    rw [← hvW, ← (symmetricOrderedOneFormLIE φ q).map_sub,
      (symmetricOrderedOneFormLIE φ q).inner_map_map]
    exact hP

/-- In particular, the correction norm in B.2 is literally the Bochner residual norm. -/
theorem symmetricOrderedOneForm_residual_norm (hφ : ContDiff ℝ 1 φ)
    (F : ↥(orderedTensorSymmetricSubspace φ (q + 1))) :
    ‖symmetricOrderedOneFormLIE φ q F -
      closedPartialKernelProjection (tensorExteriorOneOperator hφ q)
        (tensorExteriorOneOperator_isClosed hφ q) (symmetricOrderedOneFormLIE φ q F)‖ =
      ‖F.val - tensorCompactProjection hφ (q + 1) F.val‖ := by
  rw [symmetricOrderedOneForm_kernel_projection,
    ← (symmetricOrderedOneFormLIE φ q).map_sub,
    (symmetricOrderedOneFormLIE φ q).norm_map]
  rfl

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.symmetricOrderedOneFormLIE
#print axioms KLS.DeterministicBridgeIntegration.tensorExteriorOneOperator_kernel_iff

#print axioms KLS.DeterministicBridgeIntegration.symmetricOrderedOneForm_kernel_projection
#print axioms KLS.DeterministicBridgeIntegration.symmetricOrderedOneForm_residual_norm
