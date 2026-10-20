import PairTensorNaturality
import PairProjectionOrbit

noncomputable section
open scoped BigOperators
namespace KLSBelow25.PairTensor
open PairProjection
variable {r : ℕ} {ι : Type*} [Fintype ι]

def mapPair {N : ℕ} (π : Equiv.Perm (Fin N)) (e : Pair N) : Pair N :=
  ⟨e.val.map π.toEmbedding,by simp [e.property]⟩

@[simp] theorem mapPair_val {N : ℕ} (π : Equiv.Perm (Fin N)) (e : Pair N) :
    (mapPair π e).val = e.val.map π.toEmbedding := rfl

@[simp] theorem mem_mapPair {N : ℕ} (π : Equiv.Perm (Fin N)) (e : Pair N) (i : Fin N) :
    π i ∈ (mapPair π e).val ↔ i ∈ e.val := by
  simp [mapPair]

def pairPerm {N : ℕ} (π : Equiv.Perm (Fin N)) : Equiv.Perm (Pair N) where
  toFun := mapPair π
  invFun := mapPair π.symm
  left_inv e := by
    apply Subtype.ext
    simp [mapPair, Finset.map_map]
  right_inv e := by
    apply Subtype.ext
    simp [mapPair, Finset.map_map]

theorem kernel_comp (κ : ι → ι → ι → ℝ)
    (hκ : ∀ i j m,κ i j m=κ j i m) (H : Tensor (ι := ι) (r+1))
    (hH : Symmetric H) (π : Equiv.Perm (Fin (r+2)))
    (e : Pair (r+2)) (a : Fin (r+2) → ι) :
    kernel κ H e (a ∘ π) = kernel κ H (mapPair π e) a := by
  unfold kernel
  rw [kernelInFrame_comp]
  apply kernelInFrame_eq κ hκ H hH (mapPair π e)
  · intro i
    exact (mem_mapPair π e _).mpr (pairFrame_inl_mem e i)
  · intro i
    exact fun h => pairFrame_inr_not_mem e i ((mem_mapPair π e _).mp h)
  · exact pairFrame_inl_mem _
  · exact pairFrame_inr_not_mem _

theorem creation_symmetric (κ : ι → ι → ι → ℝ)
    (hκ : ∀ i j m,κ i j m=κ j i m) (H : Tensor (ι := ι) (r+1))
    (hH : Symmetric H) : Symmetric (creation κ H) := by
  intro π a
  simp_rw [creation,kernel_comp κ hκ H hH]
  exact Equiv.sum_comp (pairPerm π) (fun e => kernel κ H e a)

def wordPerm {d : ℕ} (π : Equiv.Perm (Fin d)) : Equiv.Perm (Fin d → ι) where
  toFun a := a ∘ π
  invFun a := a ∘ π.symm
  left_inv a := by funext i; simp [Function.comp_def]
  right_inv a := by funext i; simp [Function.comp_def]

theorem pairing_comp {d : ℕ} (S T : Tensor (ι := ι) d) (π : Equiv.Perm (Fin d)) :
    pairing (fun a => S (a ∘ π)) (fun a => T (a ∘ π)) = pairing S T := by
  exact Equiv.sum_comp (wordPerm π) (fun a => S a*T a)

theorem kernel_pairing_map (κ : ι → ι → ι → ℝ)
    (hκ : ∀ i j m,κ i j m=κ j i m) (H : Tensor (ι := ι) (r+1))
    (hH : Symmetric H) (π : Equiv.Perm (Fin (r+2))) (e f : Pair (r+2)) :
    pairing (kernel κ H (mapPair π e)) (kernel κ H (mapPair π f)) =
      pairing (kernel κ H e) (kernel κ H f) := by
  have he : kernel κ H (mapPair π e) = fun a => kernel κ H e (a ∘ π) :=
    funext (fun a => (kernel_comp κ hκ H hH π e a).symm)
  have hf : kernel κ H (mapPair π f) = fun a => kernel κ H f (a ∘ π) :=
    funext (fun a => (kernel_comp κ hκ H hH π f a).symm)
  rw [he,hf]
  exact pairing_comp _ _ π

theorem kernel_pairing_eq_of_intersection_card (κ : ι → ι → ι → ℝ)
    (hκ : ∀ i j m,κ i j m=κ j i m) (H : Tensor (ι := ι) (r+1))
    (hH : Symmetric H) (e f e' f' : Pair (r+2))
    (hc : (e.val ∩ f.val).card = (e'.val ∩ f'.val).card) :
    pairing (kernel κ H e) (kernel κ H f) =
      pairing (kernel κ H e') (kernel κ H f') := by
  obtain ⟨π,he,hf⟩ := exists_pair_permutation e f e' f' hc
  have he' : mapPair π e=e' := Subtype.ext he
  have hf' : mapPair π f=f' := Subtype.ext hf
  rw [←he',←hf']
  exact (kernel_pairing_map κ hκ H hH π e f).symm

end KLSBelow25.PairTensor
#print axioms KLSBelow25.PairTensor.kernel_pairing_eq_of_intersection_card
