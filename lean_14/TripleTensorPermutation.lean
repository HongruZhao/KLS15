import TripleTensorNaturality
import PairTensorPermutation

noncomputable section
open scoped BigOperators
namespace KLSBelow25.TripleTensor
open TripleProjection PairTensor
variable {r : ℕ} {ι : Type*} [Fintype ι]

def mapTriple {N : ℕ} (π : Equiv.Perm (Fin N)) (e : Triple N) : Triple N :=
  ⟨e.val.map π.toEmbedding,by simp [e.property]⟩

@[simp] theorem mapTriple_val {N : ℕ} (π : Equiv.Perm (Fin N)) (e : Triple N) :
    (mapTriple π e).val = e.val.map π.toEmbedding := rfl

@[simp] theorem mem_mapTriple {N : ℕ} (π : Equiv.Perm (Fin N)) (e : Triple N) (i : Fin N) :
    π i ∈ (mapTriple π e).val ↔ i ∈ e.val := by
  simp [mapTriple]

def triplePerm {N : ℕ} (π : Equiv.Perm (Fin N)) : Equiv.Perm (Triple N) where
  toFun := mapTriple π
  invFun := mapTriple π.symm
  left_inv e := by
    apply Subtype.ext
    simp [mapTriple, Finset.map_map]
  right_inv e := by
    apply Subtype.ext
    simp [mapTriple, Finset.map_map]

theorem kernel_comp (κ : ι → ι → ι → ι → ℝ)
    (hκ : ∀ m,Symmetric (fun a : Fin 3→ι => κ (a 0) (a 1) (a 2) m)) (H : Tensor (ι := ι) (r+1))
    (hH : Symmetric H) (π : Equiv.Perm (Fin (r+3)))
    (e : Triple (r+3)) (a : Fin (r+3) → ι) :
    kernel κ H e (a ∘ π) = kernel κ H (mapTriple π e) a := by
  unfold kernel
  rw [kernelInFrame_comp]
  apply kernelInFrame_eq κ hκ H hH (mapTriple π e)
  · intro i
    exact (mem_mapTriple π e _).mpr (tripleFrame_inl_mem e i)
  · intro i
    exact fun h => tripleFrame_inr_not_mem e i ((mem_mapTriple π e _).mp h)
  · exact tripleFrame_inl_mem _
  · exact tripleFrame_inr_not_mem _

theorem creation_symmetric (κ : ι → ι → ι → ι → ℝ)
    (hκ : ∀ m,Symmetric (fun a : Fin 3→ι => κ (a 0) (a 1) (a 2) m)) (H : Tensor (ι := ι) (r+1))
    (hH : Symmetric H) : Symmetric (creation κ H) := by
  intro π a
  simp_rw [creation,kernel_comp κ hκ H hH]
  exact Equiv.sum_comp (triplePerm π) (fun e => kernel κ H e a)

theorem kernel_pairing_map (κ : ι → ι → ι → ι → ℝ)
    (hκ : ∀ m,Symmetric (fun a : Fin 3→ι => κ (a 0) (a 1) (a 2) m)) (H : Tensor (ι := ι) (r+1))
    (hH : Symmetric H) (π : Equiv.Perm (Fin (r+3))) (e f : Triple (r+3)) :
    pairing (kernel κ H (mapTriple π e)) (kernel κ H (mapTriple π f)) =
      pairing (kernel κ H e) (kernel κ H f) := by
  have he : kernel κ H (mapTriple π e) = fun a => kernel κ H e (a ∘ π) :=
    funext (fun a => (kernel_comp κ hκ H hH π e a).symm)
  have hf : kernel κ H (mapTriple π f) = fun a => kernel κ H f (a ∘ π) :=
    funext (fun a => (kernel_comp κ hκ H hH π f a).symm)
  rw [he,hf]
  exact pairing_comp _ _ π

theorem kernel_pairing_eq_of_intersection_card (κ : ι → ι → ι → ι → ℝ)
    (hκ : ∀ m,Symmetric (fun a : Fin 3→ι => κ (a 0) (a 1) (a 2) m)) (H : Tensor (ι := ι) (r+1))
    (hH : Symmetric H) (e f e' f' : Triple (r+3))
    (hc : (e.val ∩ f.val).card = (e'.val ∩ f'.val).card) :
    pairing (kernel κ H e) (kernel κ H f) =
      pairing (kernel κ H e') (kernel κ H f') := by
  obtain ⟨π,he,hf⟩ := PairProjection.exists_finset_pair_permutation e.val f.val e'.val f'.val
    (by rw [e.property,e'.property]) (by rw [f.property,f'.property]) hc
  have he' : mapTriple π e=e' := Subtype.ext he
  have hf' : mapTriple π f=f' := Subtype.ext hf
  rw [←he',←hf']
  exact (kernel_pairing_map κ hκ H hH π e f).symm

end KLSBelow25.TripleTensor
#print axioms KLSBelow25.TripleTensor.kernel_pairing_eq_of_intersection_card
