import TensorSymmetrization

/-! Exact finite orthogonal projection formula onto the actual fully
symmetric one-form fiber. An auxiliary-symmetric input is symmetrized by
averaging its literal omitted-slot coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ}

lemma mem_tensorOneFormSymmetricFiber_iff
    (v : EuclideanSpace ℝ (TensorOneFormIndex n r)) :
    v ∈ tensorOneFormSymmetricFiber n r ↔
      ∀ a b, List.Perm (List.ofFn (Fin.cons a.2 a.1))
        (List.ofFn (Fin.cons b.2 b.1)) → v a = v b := by
  simp only [tensorOneFormSymmetricFiber, Submodule.mem_iInf, LinearMap.mem_ker,
    tensorOneFormDifference, ContinuousLinearMap.coe_coe, _root_.sub_apply,
    PiLp.proj_apply, sub_eq_zero]

lemma tensor_erased_slot_pairing
    (v : EuclideanSpace ℝ (TensorOneFormIndex n r))
    (hv : v ∈ tensorOneFormSymmetricFiber n r)
    (w : EuclideanSpace ℝ (TensorOneFormIndex n r)) (k : Fin (r + 1)) :
    (∑ a : OrderedTensorIndex n (r + 1),
      v (Fin.tail a, a 0) * w ((fun j => a (k.succAbove j)), a k)) =
      ∑ I : OrderedTensorIndex n r, ∑ i, v (I, i) * w (I, i) := by
  have hs (a b : OrderedTensorIndex n (r + 1))
      (hp : List.Perm (List.ofFn a) (List.ofFn b)) :
      v (Fin.tail a, a 0) = v (Fin.tail b, b 0) := by
    apply (mem_tensorOneFormSymmetricFiber_iff v).mp hv
    simpa only [Fin.cons_self_tail] using hp
  calc
    _ = ∑ p : Fin n × OrderedTensorIndex n r,
        v (Fin.tail (Fin.insertNth (α := fun _ => Fin n) k p.1 p.2),
          (Fin.insertNth (α := fun _ => Fin n) k p.1 p.2) 0) *
          w ((fun j => (Fin.insertNth (α := fun _ => Fin n) k p.1 p.2) (k.succAbove j)),
            (Fin.insertNth (α := fun _ => Fin n) k p.1 p.2) k) := by
      symm
      exact Fintype.sum_equiv (Fin.insertNthEquiv (fun _ : Fin (r + 1) => Fin n) k)
        _ _ (fun _ => rfl)
    _ = ∑ p : Fin n × OrderedTensorIndex n r, v (p.2, p.1) * w (p.2, p.1) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [hs _ _ (KLSBelow25.ofFn_insertNth_perm_cons k p.1 p.2)]
      simp
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]

lemma tensorOneFormSymmetrization_pairing
    (v : EuclideanSpace ℝ (TensorOneFormIndex n r))
    (hv : v ∈ tensorOneFormSymmetricFiber n r)
    (w : EuclideanSpace ℝ (TensorOneFormIndex n r)) :
    inner ℝ v (tensorOneFormSymmetrization w) = inner ℝ v w := by
  have he : (∑ a : OrderedTensorIndex n (r + 1),
      v (Fin.tail a, a 0) * tensorSymmetrizationValue w a) =
      ∑ I : OrderedTensorIndex n r, ∑ i, v (I, i) * w (I, i) := by
    unfold tensorSymmetrizationValue
    simp_rw [mul_left_comm (v _) (1 / (r + 1 : ℕ)), Finset.mul_sum]
    rw [Finset.sum_comm]
    have hk (k : Fin (r + 1)) :
        (∑ a : OrderedTensorIndex n (r + 1),
          (1 / (r + 1 : ℕ)) * (v (Fin.tail a, a 0) *
            w ((fun j => a (k.succAbove j)), a k))) =
        (1 / (r + 1 : ℕ)) * ∑ I : OrderedTensorIndex n r, ∑ i, v (I, i) * w (I, i) := by
      rw [← Finset.mul_sum, tensor_erased_slot_pairing v hv w k]
    simp_rw [hk]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hidx : (∑ a : OrderedTensorIndex n (r + 1),
      v (Fin.tail a, a 0) * tensorSymmetrizationValue w a) =
      ∑ I : OrderedTensorIndex n r, ∑ i,
        v (I, i) * tensorSymmetrizationValue w (Fin.cons i I) := by
    calc
      _ = ∑ p : Fin n × OrderedTensorIndex n r,
          v (p.2, p.1) * tensorSymmetrizationValue w (Fin.cons p.1 p.2) := by
        symm
        exact Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (r + 1) => Fin n))
          _ _ (fun p => by
            change v (p.2, p.1) * tensorSymmetrizationValue w (Fin.cons p.1 p.2) =
              v (Fin.tail (Fin.cons (α := fun _ : Fin (r + 1) => Fin n) p.1 p.2),
                (Fin.cons (α := fun _ : Fin (r + 1) => Fin n) p.1 p.2) 0) *
                  tensorSymmetrizationValue w (Fin.cons p.1 p.2)
            rw [Fin.tail_cons, Fin.cons_zero])
      _ = _ := by simp only [Fin.tail_cons, Fin.cons_zero, Fintype.sum_prod_type]; rw [Finset.sum_comm]
  rw [hidx] at he
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    tensorOneFormSymmetrization, PiLp.toLp_apply, Fintype.sum_prod_type, mul_comm] using he

/-- The omitted-slot average is exactly the genuine orthogonal projection,
proved by membership and its inner products against the actual fiber. -/
theorem tensorOneFormProjection_eq_symmetrization
    (w : EuclideanSpace ℝ (TensorOneFormIndex n r))
    (hw : tensorOneFormAuxiliarySymmetric w) :
    tensorOneFormProjection n r w = tensorOneFormSymmetrization w := by
  have he : (tensorOneFormSymmetricFiber n r).orthogonalProjectionOnto w =
      (⟨tensorOneFormSymmetrization w, tensorOneFormSymmetrization_mem w hw⟩ :
        ↥(tensorOneFormSymmetricFiber n r)) := by
    apply ext_inner_left ℝ
    intro v
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    change inner ℝ (v : EuclideanSpace ℝ _) w =
      inner ℝ (v : EuclideanSpace ℝ _) (tensorOneFormSymmetrization w)
    exact (tensorOneFormSymmetrization_pairing v v.property w).symm
  change Subtype.val ((tensorOneFormSymmetricFiber n r).orthogonalProjectionOnto w) = _
  exact congrArg Subtype.val he

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorOneFormProjection_eq_symmetrization
