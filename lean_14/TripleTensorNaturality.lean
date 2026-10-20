import TripleTensorKernel

noncomputable section
open scoped BigOperators
namespace KLSBelow25.TripleTensor
open TripleProjection PairTensor
variable {r : ℕ} {ι : Type*} [Fintype ι]

def frameTripleEquiv (e : Triple (r+3)) (F : Fin 3 ⊕ Fin r ≃ Fin (r+3))
    (hF : ∀ i,F (Sum.inl i)∈e.val) : Fin 3 ≃ e.val :=
  Equiv.ofBijective (fun i => ⟨F (Sum.inl i),hF i⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro i j hij
      exact Sum.inl.inj (F.injective (congrArg Subtype.val hij)),by simp [e.property]⟩)

def frameTailEquiv (e : Triple (r+3)) (F : Fin 3 ⊕ Fin r ≃ Fin (r+3))
    (hF : ∀ i,F (Sum.inr i)∉e.val) : Fin r ≃ (e.valᶜ : Finset (Fin (r+3))) :=
  Equiv.ofBijective (fun i => ⟨F (Sum.inr i),by simpa using hF i⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro i j hij
      exact Sum.inr.inj (F.injective (congrArg Subtype.val hij)),by simp [e.property]⟩)

@[simp] theorem frameTripleEquiv_apply (e : Triple (r+3))
    (F : Fin 3 ⊕ Fin r ≃ Fin (r+3)) (hF : ∀ i,F (Sum.inl i)∈e.val) (i : Fin 3) :
    (frameTripleEquiv e F hF i : Fin (r+3))=F (Sum.inl i) := rfl

@[simp] theorem frameTailEquiv_apply (e : Triple (r+3))
    (F : Fin 3 ⊕ Fin r ≃ Fin (r+3)) (hF : ∀ i,F (Sum.inr i)∉e.val) (i : Fin r) :
    (frameTailEquiv e F hF i : Fin (r+3))=F (Sum.inr i) := rfl

theorem kernelInFrame_eq_of_reindex (κ : ι→ι→ι→ι→ℝ)
    (hκ : ∀ m,Symmetric (fun a : Fin 3→ι => κ (a 0) (a 1) (a 2) m))
    (H : Tensor (ι:=ι) (r+1)) (hH : Symmetric H)
    (F G : Fin 3 ⊕ Fin r ≃ Fin (r+3))
    (σ : Equiv.Perm (Fin 3)) (τ : Equiv.Perm (Fin r))
    (hp : ∀ i,F (Sum.inl i)=G (Sum.inl (σ i)))
    (ht : ∀ i,F (Sum.inr i)=G (Sum.inr (τ i))) (a : Fin (r+3)→ι) :
    kernelInFrame κ H F a=kernelInFrame κ H G a := by
  unfold kernelInFrame
  apply Finset.sum_congr rfl
  intro m _
  simp_rw [hp,ht]
  have hk := hκ m σ (fun i => a (G (Sum.inl i)))
  simp only [Function.comp_def] at hk
  rw [hk]
  congr 1
  exact symmetric_cons_tail H hH τ m (fun j => a (G (Sum.inr j)))

theorem kernelInFrame_eq (κ : ι→ι→ι→ι→ℝ)
    (hκ : ∀ m,Symmetric (fun a : Fin 3→ι => κ (a 0) (a 1) (a 2) m))
    (H : Tensor (ι:=ι) (r+1)) (hH : Symmetric H)
    (e : Triple (r+3)) (F G : Fin 3 ⊕ Fin r ≃ Fin (r+3))
    (hFp : ∀ i,F (Sum.inl i)∈e.val) (hFt : ∀ i,F (Sum.inr i)∉e.val)
    (hGp : ∀ i,G (Sum.inl i)∈e.val) (hGt : ∀ i,G (Sum.inr i)∉e.val)
    (a : Fin (r+3)→ι) : kernelInFrame κ H F a=kernelInFrame κ H G a := by
  let σ := (frameTripleEquiv e F hFp).trans (frameTripleEquiv e G hGp).symm
  let τ := (frameTailEquiv e F hFt).trans (frameTailEquiv e G hGt).symm
  apply kernelInFrame_eq_of_reindex κ hκ H hH F G σ τ
  · intro i
    have h := (frameTripleEquiv e G hGp).apply_symm_apply (frameTripleEquiv e F hFp i)
    exact (congrArg Subtype.val h).symm
  · intro i
    have h := (frameTailEquiv e G hGt).apply_symm_apply (frameTailEquiv e F hFt i)
    exact (congrArg Subtype.val h).symm

end KLSBelow25.TripleTensor
#print axioms KLSBelow25.TripleTensor.kernelInFrame_eq
