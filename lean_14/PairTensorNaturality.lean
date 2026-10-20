import PairTensorKernel

noncomputable section
open scoped BigOperators
namespace KLSBelow25.PairTensor
open PairProjection
variable {r : ℕ} {ι : Type*} [Fintype ι]

/-- An arbitrary pair frame enumerates its pair and its complement. -/
def framePairEquiv (e : Pair (r+2)) (F : Fin 2 ⊕ Fin r ≃ Fin (r+2))
    (hF : ∀ i, F (Sum.inl i) ∈ e.val) : Fin 2 ≃ e.val :=
  Equiv.ofBijective (fun i => ⟨F (Sum.inl i),hF i⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro i j hij
      exact Sum.inl.inj (F.injective (congrArg Subtype.val hij)), by
      simp [e.property]⟩)

def frameTailEquiv (e : Pair (r+2)) (F : Fin 2 ⊕ Fin r ≃ Fin (r+2))
    (hF : ∀ i, F (Sum.inr i) ∉ e.val) : Fin r ≃ (e.valᶜ : Finset (Fin (r+2))) :=
  Equiv.ofBijective (fun i => ⟨F (Sum.inr i),by simpa using hF i⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro i j hij
      exact Sum.inr.inj (F.injective (congrArg Subtype.val hij)), by
      simp [e.property]⟩)

@[simp] theorem framePairEquiv_apply (e : Pair (r+2))
    (F : Fin 2 ⊕ Fin r ≃ Fin (r+2)) (hF : ∀ i, F (Sum.inl i) ∈ e.val) (i : Fin 2) :
    (framePairEquiv e F hF i : Fin (r+2)) = F (Sum.inl i) := rfl

@[simp] theorem frameTailEquiv_apply (e : Pair (r+2))
    (F : Fin 2 ⊕ Fin r ≃ Fin (r+2)) (hF : ∀ i, F (Sum.inr i) ∉ e.val) (i : Fin r) :
    (frameTailEquiv e F hF i : Fin (r+2)) = F (Sum.inr i) := rfl

/-- Permuting only the tail slots is an actual tensor permutation. -/
def fixHeadPerm (τ : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (r+1)) :=
  (finSuccEquiv r).trans ((Equiv.optionCongr τ).trans (finSuccEquiv r).symm)

@[simp] theorem fixHeadPerm_zero (τ : Equiv.Perm (Fin r)) : fixHeadPerm τ 0 = 0 := by
  simp [fixHeadPerm]
@[simp] theorem fixHeadPerm_succ (τ : Equiv.Perm (Fin r)) (j : Fin r) :
    fixHeadPerm τ j.succ = (τ j).succ := by simp [fixHeadPerm]

omit [Fintype ι] in
theorem symmetric_cons_tail (H : Tensor (ι := ι) (r+1)) (hH : Symmetric H)
    (τ : Equiv.Perm (Fin r)) (m : ι) (a : Fin r → ι) :
    H (Fin.cons m (a ∘ τ)) = H (Fin.cons m a) := by
  have h := hH (fixHeadPerm τ) (Fin.cons m a)
  apply Eq.trans ?_ h
  congr 1
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [Function.comp_def]

omit [Fintype ι] in
theorem symmetric_fin_two_pair (κ : ι → ι → ι → ℝ)
    (hκ : ∀ i j m, κ i j m = κ j i m) (σ : Equiv.Perm (Fin 2))
    (a : Fin 2 → ι) (m : ι) : κ (a (σ 0)) (a (σ 1)) m = κ (a 0) (a 1) m := by
  have hn : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have h0 : σ 0 = 0 ∨ σ 0 = 1 := by omega
  have h1 : σ 1 = 0 ∨ σ 1 = 1 := by omega
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact (hn (h0.trans h1.symm)).elim
  · simp [h0,h1]
  · simp [h0,h1,hκ]
  · exact (hn (h0.trans h1.symm)).elim

theorem kernelInFrame_eq_of_reindex (κ : ι → ι → ι → ℝ)
    (hκ : ∀ i j m, κ i j m = κ j i m)
    (H : Tensor (ι := ι) (r+1)) (hH : Symmetric H)
    (F G : Fin 2 ⊕ Fin r ≃ Fin (r+2))
    (σ : Equiv.Perm (Fin 2)) (τ : Equiv.Perm (Fin r))
    (hp : ∀ i, F (Sum.inl i) = G (Sum.inl (σ i)))
    (ht : ∀ i, F (Sum.inr i) = G (Sum.inr (τ i))) (a : Fin (r+2) → ι) :
    kernelInFrame κ H F a = kernelInFrame κ H G a := by
  unfold kernelInFrame
  apply Finset.sum_congr rfl
  intro m _
  simp_rw [hp, ht]
  rw [symmetric_fin_two_pair κ hκ σ (fun i => a (G (Sum.inl i))) m]
  congr 1
  exact symmetric_cons_tail H hH τ m (fun j => a (G (Sum.inr j)))

theorem kernelInFrame_eq (κ : ι → ι → ι → ℝ)
    (hκ : ∀ i j m, κ i j m = κ j i m)
    (H : Tensor (ι := ι) (r+1)) (hH : Symmetric H)
    (e : Pair (r+2)) (F G : Fin 2 ⊕ Fin r ≃ Fin (r+2))
    (hFp : ∀ i, F (Sum.inl i) ∈ e.val) (hFt : ∀ i, F (Sum.inr i) ∉ e.val)
    (hGp : ∀ i, G (Sum.inl i) ∈ e.val) (hGt : ∀ i, G (Sum.inr i) ∉ e.val)
    (a : Fin (r+2) → ι) : kernelInFrame κ H F a = kernelInFrame κ H G a := by
  let σ := (framePairEquiv e F hFp).trans (framePairEquiv e G hGp).symm
  let τ := (frameTailEquiv e F hFt).trans (frameTailEquiv e G hGt).symm
  apply kernelInFrame_eq_of_reindex κ hκ H hH F G σ τ
  · intro i
    have h := (framePairEquiv e G hGp).apply_symm_apply (framePairEquiv e F hFp i)
    exact (congrArg Subtype.val h).symm
  · intro i
    have h := (frameTailEquiv e G hGt).apply_symm_apply (frameTailEquiv e F hFt i)
    exact (congrArg Subtype.val h).symm

end KLSBelow25.PairTensor
#print axioms KLSBelow25.PairTensor.kernelInFrame_eq
