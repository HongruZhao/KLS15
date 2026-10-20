import WeightedCurlFreeRangeIdentification
import FiniteGradientPrimitive
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-! Genuine compatible symmetric tensor fields of every finite rank.
Coordinates are ordered tuples and the norm sums their actual L² squares.
Compatibility is the full ordinary distributional curl condition on each
vector slice. No closed-domain or primitive-existence condition is assumed. -/
noncomputable section
open MeasureTheory Set Matrix
open scoped ContDiff BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration

abbrev OrderedTensorIndex (n r : ℕ) := Fin r → Fin n
abbrev OrderedTensorField {n : ℕ} (φ : Space n → ℝ) (r : ℕ) :=
  CenteredL2.Family (potentialMeasure φ) (OrderedTensorIndex n r)

variable {n r : ℕ} {φ : Space n → ℝ}

def orderedTensorSlice (r : ℕ) (I : OrderedTensorIndex n r) :
    OrderedTensorField φ (r + 1) →L[ℝ]
      CenteredL2.Family (potentialMeasure φ) (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin n => Lp ℝ 2 (potentialMeasure φ))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i =>
        PiLp.proj 2 (fun _ : OrderedTensorIndex n (r + 1) =>
          Lp ℝ 2 (potentialMeasure φ)) (Fin.cons i I))

@[simp] lemma orderedTensorSlice_apply (F : OrderedTensorField φ (r + 1))
    (I : OrderedTensorIndex n r) (i : Fin n) :
    orderedTensorSlice r I F i = F (Fin.cons i I) := rfl

def orderedTensorSlices (r : ℕ) : OrderedTensorField φ (r + 1) →L[ℝ]
    TensorField (φ := φ) (OrderedTensorIndex n r) :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : OrderedTensorIndex n r => VectorField (φ := φ))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun I => orderedTensorSlice r I)

@[simp] lemma orderedTensorSlices_apply (F : OrderedTensorField φ (r + 1))
    (I : OrderedTensorIndex n r) : orderedTensorSlices r F I = orderedTensorSlice r I F := rfl

lemma orderedTensorSlices_norm_sq (F : OrderedTensorField φ (r + 1)) :
    ‖orderedTensorSlices r F‖ ^ 2 = ‖F‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, orderedTensorSlices_apply, orderedTensorSlice_apply]
  rw [Finset.sum_comm]
  calc
    _ = ∑ p : Fin n × OrderedTensorIndex n r, ‖F (Fin.cons p.1 p.2)‖ ^ 2 :=
      (Fintype.sum_prod_type (fun p : Fin n × OrderedTensorIndex n r =>
        ‖F (Fin.cons p.1 p.2)‖ ^ 2)).symm
    _ = _ := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (r + 1) => Fin n))
      _ _ (fun _ => rfl)

lemma orderedTensorSlices_norm (F : OrderedTensorField φ (r + 1)) :
    ‖orderedTensorSlices r F‖ = ‖F‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (orderedTensorSlices_norm_sq F)

/-- Symmetry means invariance under every permutation of ordered indices.
The equivalent list-permutation formulation avoids privileging any slot. -/
def orderedTensorCoordinateDifference (φ : Space n → ℝ) (r : ℕ)
    (I J : OrderedTensorIndex n r) : OrderedTensorField φ r →L[ℝ]
      Lp ℝ 2 (potentialMeasure φ) :=
  (PiLp.proj 2 (fun _ : OrderedTensorIndex n r => Lp ℝ 2 (potentialMeasure φ)) I :
    OrderedTensorField φ r →L[ℝ] Lp ℝ 2 (potentialMeasure φ)) -
    PiLp.proj 2 (fun _ : OrderedTensorIndex n r => Lp ℝ 2 (potentialMeasure φ)) J

def orderedTensorSymmetricSubspace (φ : Space n → ℝ) (r : ℕ) :
    Submodule ℝ (OrderedTensorField φ r) :=
  ⨅ I, ⨅ J, ⨅ (_ : List.Perm (List.ofFn I) (List.ofFn J)),
    LinearMap.ker (orderedTensorCoordinateDifference φ r I J).toLinearMap

lemma mem_orderedTensorSymmetricSubspace_iff (F : OrderedTensorField φ r) :
    F ∈ orderedTensorSymmetricSubspace φ r ↔
      ∀ I J, List.Perm (List.ofFn I) (List.ofFn J) → F I = F J := by
  simp only [orderedTensorSymmetricSubspace, Submodule.mem_iInf, LinearMap.mem_ker,
    orderedTensorCoordinateDifference, _root_.sub_apply,
    ContinuousLinearMap.coe_coe, PiLp.proj_apply, sub_eq_zero]

lemma orderedTensorSymmetricSubspace_isClosed (φ : Space n → ℝ) (r : ℕ) :
    IsClosed (orderedTensorSymmetricSubspace φ r : Set (OrderedTensorField φ r)) := by
  simp only [orderedTensorSymmetricSubspace, Submodule.coe_iInf]
  exact isClosed_iInter fun I => isClosed_iInter fun J => isClosed_iInter fun _ =>
    (orderedTensorCoordinateDifference φ r I J).isClosed_ker

def orderedTensorCurlSubspace (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    Submodule ℝ (OrderedTensorField φ r) :=
  match r with
  | 0 => ⊤
  | s + 1 => ⨅ I : OrderedTensorIndex n s,
      (weightedCurlFreeSubspace hφ).comap (orderedTensorSlice s I).toLinearMap

lemma mem_orderedTensorCurlSubspace_succ_iff (hφ : ContDiff ℝ 1 φ)
    (F : OrderedTensorField φ (r + 1)) :
    F ∈ orderedTensorCurlSubspace hφ (r + 1) ↔
      ∀ I, orderedTensorSlice r I F ∈ weightedCurlFreeSubspace hφ := by
  simp only [orderedTensorCurlSubspace, Submodule.mem_iInf, Submodule.mem_comap,
    ContinuousLinearMap.coe_coe]

lemma orderedTensorCurlSubspace_isClosed (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    IsClosed (orderedTensorCurlSubspace hφ r : Set (OrderedTensorField φ r)) := by
  cases r with
  | zero => exact isClosed_univ
  | succ r =>
    simp only [orderedTensorCurlSubspace, Submodule.coe_iInf]
    exact isClosed_iInter fun I =>
      (weightedCurlFreeSubspace_isClosed hφ).preimage (orderedTensorSlice r I).continuous

/-- The paper's actual Cᵣ, with ordered-index Hilbert norm. -/
def compatibleSymmetricTensorSubspace (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    Submodule ℝ (OrderedTensorField φ r) :=
  orderedTensorSymmetricSubspace φ r ⊓ orderedTensorCurlSubspace hφ r

lemma compatibleSymmetricTensorSubspace_isClosed (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    IsClosed (compatibleSymmetricTensorSubspace hφ r : Set (OrderedTensorField φ r)) :=
  (orderedTensorSymmetricSubspace_isClosed φ r).inter (orderedTensorCurlSubspace_isClosed hφ r)

lemma tensor_symmetry_cons (F : OrderedTensorField φ (r + 1))
    (hF : F ∈ orderedTensorSymmetricSubspace φ (r + 1))
    {I J : OrderedTensorIndex n r} (hIJ : List.Perm (List.ofFn I) (List.ofFn J))
    (i : Fin n) : F (Fin.cons i I) = F (Fin.cons i J) := by
  apply (mem_orderedTensorSymmetricSubspace_iff F).mp hF
  simpa only [List.ofFn_cons] using hIJ.cons i

lemma tensor_symmetry_swap (F : OrderedTensorField φ (r + 2))
    (hF : F ∈ orderedTensorSymmetricSubspace φ (r + 2))
    (I : OrderedTensorIndex n r) (i j : Fin n) :
    F (Fin.cons i (Fin.cons j I)) = F (Fin.cons j (Fin.cons i I)) := by
  apply (mem_orderedTensorSymmetricSubspace_iff F).mp hF
  simpa only [List.ofFn_cons] using List.Perm.swap j i (List.ofFn I)

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.orderedTensorSlices_norm
#print axioms KLS.DeterministicBridgeIntegration.compatibleSymmetricTensorSubspace_isClosed
#print axioms KLS.DeterministicBridgeIntegration.tensor_symmetry_swap
