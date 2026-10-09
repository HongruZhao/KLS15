import TensorProjectionFormula

/-! Exact finite norm identities for the full-symmetry projection and
physical Koszul row on auxiliary-symmetric one-forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ}

def tensorOneFormCross (w : EuclideanSpace ℝ (TensorOneFormIndex n (r + 1))) : ℝ :=
  ∑ I : OrderedTensorIndex n r, ∑ i, ∑ j,
    w (Fin.cons i I, j) * w (Fin.cons j I, i)

lemma tensorSymmetrizationValue_cons
    (w : EuclideanSpace ℝ (TensorOneFormIndex n (r + 1)))
    (I : OrderedTensorIndex n (r + 1)) (j : Fin n) :
    tensorSymmetrizationValue w (Fin.cons j I) = (1 / (r + 2 : ℕ)) *
      (w (I, j) + ∑ k : Fin (r + 1), w (Fin.cons j (k.removeNth I), I k)) := by
  unfold tensorSymmetrizationValue
  congr 1
  rw [Fin.sum_univ_succ]
  simp only [Fin.zero_succAbove, Fin.cons_succ, Fin.cons_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have he : (fun l => (Fin.cons (α := fun _ : Fin (r + 2) => Fin n) j I) (k.succ.succAbove l)) =
      Fin.cons (α := fun _ : Fin (r + 1) => Fin n) j (k.removeNth I) :=
    Fin.cons_comp_succ_succAbove j I k
  rw [he]

lemma tensorOneFormCross_slot
    (w : EuclideanSpace ℝ (TensorOneFormIndex n (r + 1)))
    (hw : tensorOneFormAuxiliarySymmetric w) (k : Fin (r + 1)) :
    (∑ I : OrderedTensorIndex n (r + 1), ∑ j,
      w (I, j) * w (Fin.cons j (k.removeNth I), I k)) = tensorOneFormCross w := by
  calc
    _ = ∑ p : Fin n × OrderedTensorIndex n r, ∑ j,
      w (Fin.insertNth (α := fun _ => Fin n) k p.1 p.2, j) *
        w (Fin.cons j (k.removeNth (Fin.insertNth (α := fun _ => Fin n) k p.1 p.2)),
          (Fin.insertNth (α := fun _ => Fin n) k p.1 p.2) k) := by
      symm
      exact Fintype.sum_equiv (Fin.insertNthEquiv (fun _ : Fin (r + 1) => Fin n) k)
        _ _ (fun _ => rfl)
    _ = ∑ p : Fin n × OrderedTensorIndex n r, ∑ j,
        w (Fin.cons p.1 p.2, j) * w (Fin.cons j p.2, p.1) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro j _
      rw [hw _ _ (KLSBelow25.ofFn_insertNth_perm_cons k p.1 p.2) j]
      simp
    _ = _ := by unfold tensorOneFormCross; rw [Fintype.sum_prod_type, Finset.sum_comm]

lemma tensorOneForm_norm_sq_eq_slices
    (w : EuclideanSpace ℝ (TensorOneFormIndex n (r + 1))) :
    ‖w‖ ^ 2 = ∑ I : OrderedTensorIndex n r, ∑ i, ∑ j, (w (Fin.cons i I, j)) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs, Fintype.sum_prod_type]
  symm
  rw [Finset.sum_comm]
  calc
    _ = ∑ p : Fin n × OrderedTensorIndex n r, ∑ j, (w (Fin.cons p.1 p.2, j)) ^ 2 :=
      (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (r + 1) => Fin n))
      _ _ (fun _ => rfl)

lemma tensorOneForm_inner_symmetrization
    (w : EuclideanSpace ℝ (TensorOneFormIndex n (r + 1)))
    (hw : tensorOneFormAuxiliarySymmetric w) :
    inner ℝ w (tensorOneFormSymmetrization w) =
      (1 / (r + 2 : ℕ)) * (‖w‖ ^ 2 + (r + 1 : ℕ) * tensorOneFormCross w) := by
  have hn : (∑ I : OrderedTensorIndex n (r + 1), ∑ j, (w (I, j)) ^ 2) = ‖w‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs, sq_abs, Fintype.sum_prod_type]
  have hx (I : OrderedTensorIndex n (r + 1)) (j : Fin n) :
      w (I, j) * tensorSymmetrizationValue w (Fin.cons j I) =
        (1 / (r + 2 : ℕ)) * ((w (I, j)) ^ 2 +
          ∑ k : Fin (r + 1), w (I, j) * w (Fin.cons j (k.removeNth I), I k)) := by
    rw [tensorSymmetrizationValue_cons, ← Finset.mul_sum]
    ring
  have hc : (∑ I : OrderedTensorIndex n (r + 1), ∑ j, ∑ k : Fin (r + 1),
      w (I, j) * w (Fin.cons j (k.removeNth I), I k)) =
      (r + 1 : ℕ) * tensorOneFormCross w := by
    calc
      _ = ∑ I : OrderedTensorIndex n (r + 1), ∑ k : Fin (r + 1), ∑ j,
          w (I, j) * w (Fin.cons j (k.removeNth I), I k) :=
        Finset.sum_congr rfl (fun I _ => Finset.sum_comm)
      _ = ∑ k : Fin (r + 1), ∑ I : OrderedTensorIndex n (r + 1), ∑ j,
          w (I, j) * w (Fin.cons j (k.removeNth I), I k) := Finset.sum_comm
      _ = _ := by simp_rw [tensorOneFormCross_slot w hw]; simp
  have he : (∑ I : OrderedTensorIndex n (r + 1), ∑ j,
      w (I, j) * tensorSymmetrizationValue w (Fin.cons j I)) =
      (1 / (r + 2 : ℕ)) * (‖w‖ ^ 2 + (r + 1 : ℕ) * tensorOneFormCross w) := by
    simp_rw [hx, ← Finset.mul_sum, Finset.sum_add_distrib]
    rw [hn]
    have hc' : (∑ I : OrderedTensorIndex n (r + 1), ∑ j, w (I, j) *
        ∑ k : Fin (r + 1), w (Fin.cons j (k.removeNth I), I k)) =
        (r + 1 : ℕ) * tensorOneFormCross w := by
      simpa only [Finset.mul_sum] using hc
    rw [hc']
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    tensorOneFormSymmetrization, PiLp.toLp_apply, Fintype.sum_prod_type, mul_comm] using he

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorOneForm_inner_symmetrization
