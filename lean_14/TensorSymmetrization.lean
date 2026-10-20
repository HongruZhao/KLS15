import TensorAuxiliaryContractionEstimate
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Literal full symmetrization of an auxiliary-symmetric one-form.
The proof constructs a permutation of the actual finite tuple positions
from list permutation, and then reindexes the omitted-slot average. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ}

lemma tuple_perm_exists_equiv {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (a b : Fin m → α) (hp : List.Perm (List.ofFn a) (List.ofFn b)) :
    ∃ e : Equiv.Perm (Fin m), ∀ i, b (e i) = a i := by
  have hc (j : α) : Fintype.card {i : Fin m // a i = j} =
      Fintype.card {i : Fin m // b i = j} := by
    have h := (hp.map (fun x => if x = j then (1 : ℕ) else 0)).sum_eq
    simpa only [← List.ofFn_comp', List.sum_ofFn, Fintype.card_subtype,
      Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_const_zero,
      Function.comp_apply] using h
  let ef (j : α) : {i : Fin m // a i = j} ≃ {i : Fin m // b i = j} :=
    Fintype.equivOfCardEq (hc j)
  exact ⟨Equiv.ofFiberEquiv ef, Equiv.ofFiberEquiv_map ef⟩

def tensorOneFormAuxiliarySymmetric
    (w : EuclideanSpace ℝ (TensorOneFormIndex n r)) : Prop :=
  ∀ I J, List.Perm (List.ofFn I) (List.ofFn J) → ∀ i, w (I, i) = w (J, i)

def tensorSymmetrizationValue
    (w : EuclideanSpace ℝ (TensorOneFormIndex n r))
    (a : OrderedTensorIndex n (r + 1)) : ℝ :=
  (1 / (r + 1 : ℕ)) * ∑ k : Fin (r + 1), w ((fun j => a (k.succAbove j)), a k)

lemma tensorSymmetrizationValue_perm
    (w : EuclideanSpace ℝ (TensorOneFormIndex n r))
    (hw : tensorOneFormAuxiliarySymmetric w)
    (a b : OrderedTensorIndex n (r + 1))
    (hp : List.Perm (List.ofFn a) (List.ofFn b)) :
    tensorSymmetrizationValue w a = tensorSymmetrizationValue w b := by
  obtain ⟨e, he⟩ := tuple_perm_exists_equiv a b hp
  unfold tensorSymmetrizationValue
  congr 1
  apply Fintype.sum_equiv e
  intro k
  have hp' : List.Perm (List.ofFn (fun j => a (k.succAbove j)))
      (List.ofFn (fun j => b ((e k).succAbove j))) := by
    have hg : (List.ofFn a)[k.val]? = (List.ofFn b)[(e k).val]? := by
      simp only [List.getElem?_ofFn, dif_pos k.isLt, dif_pos (e k).isLt]
      exact congrArg some (he k).symm
    have h := hp.eraseIdx_of_getElem?_eq hg
    simpa only [KLS.list_ofFn_eraseIdx] using h
  rw [he k]
  exact hw _ _ hp' (a k)

def tensorOneFormSymmetrization
    (w : EuclideanSpace ℝ (TensorOneFormIndex n r)) :
    EuclideanSpace ℝ (TensorOneFormIndex n r) :=
  WithLp.toLp 2 (fun a => tensorSymmetrizationValue w (Fin.cons a.2 a.1))

lemma tensorOneFormSymmetrization_mem
    (w : EuclideanSpace ℝ (TensorOneFormIndex n r))
    (hw : tensorOneFormAuxiliarySymmetric w) :
    tensorOneFormSymmetrization w ∈ tensorOneFormSymmetricFiber n r := by
  simp only [tensorOneFormSymmetricFiber, Submodule.mem_iInf, LinearMap.mem_ker,
    tensorOneFormDifference, ContinuousLinearMap.coe_coe, _root_.sub_apply,
    PiLp.proj_apply, sub_eq_zero]
  intro a b hp
  exact tensorSymmetrizationValue_perm w hw _ _ hp

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tuple_perm_exists_equiv
#print axioms KLS.DeterministicBridgeIntegration.tensorOneFormSymmetrization_mem
