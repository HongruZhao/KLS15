import PairTensorAdjoint

/-! A pair incident to the leading coordinate is exactly a one-slot
contraction on the remaining ordered tensor coordinates. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.PairTensor
open PairProjection
variable {r : ℕ} {ι : Type*} [Fintype ι]
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def incidentPair (s : Fin (r+1)) : Pair (r+2) :=
  ⟨{0,s.succ},Finset.card_pair (Fin.succ_ne_zero s).symm⟩

def moveHeadPerm (s : Fin (r+1)) : Equiv.Perm (Fin (r+1)) :=
  (finSuccEquiv r).trans (finSuccEquiv' s).symm
@[simp] theorem moveHeadPerm_zero (s : Fin (r+1)) : moveHeadPerm s 0=s := by
  simp [moveHeadPerm]
@[simp] theorem moveHeadPerm_succ (s : Fin (r+1)) (j : Fin r) :
    moveHeadPerm s j.succ=s.succAbove j := by simp [moveHeadPerm]

def incidentFrame (s : Fin (r+1)) : Fin 2 ⊕ Fin r ≃ Fin (r+2) :=
  (consFrame r).trans (fixHeadPerm (moveHeadPerm s))
@[simp] theorem incidentFrame_inl_zero (s : Fin (r+1)) : incidentFrame s (Sum.inl 0)=0 := by
  simp [incidentFrame]
@[simp] theorem incidentFrame_inl_one (s : Fin (r+1)) : incidentFrame s (Sum.inl 1)=s.succ := by
  change fixHeadPerm (moveHeadPerm s) (Fin.succ 0)=s.succ
  rw [fixHeadPerm_succ,moveHeadPerm_zero]
@[simp] theorem incidentFrame_inr (s : Fin (r+1)) (j : Fin r) :
    incidentFrame s (Sum.inr j)=(s.succAbove j).succ := by
  simp [incidentFrame]

omit [Fintype ι] in
theorem symmetric_update (H : Tensor (ι := ι) (r+1)) (hH : Symmetric H)
    (s : Fin (r+1)) (a : Fin (r+1)→ι) (m : ι) :
    H (Fin.cons m (fun j => a (s.succAbove j)))=H (Function.update a s m) := by
  have hh := hH (moveHeadPerm s) (Function.update a s m)
  apply Eq.trans ?_ hh
  congr 1
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp
  · simp [s.succAbove_ne k]

theorem kernel_incidentPair_cons (κ : ι→ι→ι→ℝ)
    (hκ : ∀ i j m,κ i j m=κ j i m)
    (H : Tensor (ι := ι) (r+1)) (hH : Symmetric H)
    (s : Fin (r+1)) (i : ι) (a : Fin (r+1)→ι) :
    kernel κ H (incidentPair s) (Fin.cons i a)=
      ∑ m,κ i (a s) m*H (Function.update a s m) := by
  have he := kernelInFrame_eq κ hκ H hH (incidentPair s)
    (pairFrame (incidentPair s)) (incidentFrame s)
    (pairFrame_inl_mem _) (pairFrame_inr_not_mem _)
    (by intro j;fin_cases j <;> simp [incidentPair])
    (by intro j;simp [incidentPair,s.succAbove_ne j]) (Fin.cons i a)
  rw [kernel,he]
  simp only [kernelInFrame,incidentFrame_inl_zero,incidentFrame_inl_one,incidentFrame_inr,
    Fin.cons_zero,Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro m _
  rw [symmetric_update H hH s a m]

end KLSBelow25.PairTensor
#print axioms KLSBelow25.PairTensor.kernel_incidentPair_cons
