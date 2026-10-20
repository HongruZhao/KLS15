import TripleProjectionDefinitions
import PairTensorNaturality

/-! Literal unordered-triple fourth-cumulant insertion into ordered tensors.
The input has degree two less than the output. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.TripleTensor
open TripleProjection PairTensor
variable {r : ℕ} {ι : Type*} [Fintype ι]

theorem complement_card (e : Triple (r+3)) : e.valᶜ.card=r := by
  rw [Finset.card_compl,Fintype.card_fin,e.property]
  omega

def tripleFrame (e : Triple (r+3)) : Fin 3 ⊕ Fin r ≃ Fin (r+3) :=
  ((e.val.orderIsoOfFin e.property).toEquiv.sumCongr
    ((e.valᶜ.orderIsoOfFin (complement_card e)).toEquiv.trans
      (Equiv.subtypeEquivRight (fun _ => Finset.mem_compl)))).trans
        (Equiv.sumCompl (fun i => i∈e.val))

@[simp] theorem tripleFrame_inl (e : Triple (r+3)) (i : Fin 3) :
    tripleFrame e (Sum.inl i)=e.val.orderEmbOfFin e.property i := rfl

@[simp] theorem tripleFrame_inr (e : Triple (r+3)) (i : Fin r) :
    tripleFrame e (Sum.inr i)=e.valᶜ.orderEmbOfFin (complement_card e) i := rfl

@[simp] theorem tripleFrame_inl_mem (e : Triple (r+3)) (i : Fin 3) :
    tripleFrame e (Sum.inl i)∈e.val := by
  simp only [tripleFrame_inl,Finset.orderEmbOfFin_mem]

@[simp] theorem tripleFrame_inr_not_mem (e : Triple (r+3)) (i : Fin r) :
    tripleFrame e (Sum.inr i)∉e.val := by
  simpa only [tripleFrame_inr,Finset.mem_compl] using
    Finset.orderEmbOfFin_mem e.valᶜ (complement_card e) i

def kernelInFrame (κ : ι→ι→ι→ι→ℝ) (H : Tensor (ι:=ι) (r+1))
    (F : Fin 3 ⊕ Fin r ≃ Fin (r+3)) (a : Fin (r+3)→ι) : ℝ :=
  ∑ m,κ (a (F (Sum.inl 0))) (a (F (Sum.inl 1))) (a (F (Sum.inl 2))) m*
    H (Fin.cons m (fun j => a (F (Sum.inr j))))

def kernel (κ : ι→ι→ι→ι→ℝ) (H : Tensor (ι:=ι) (r+1))
    (e : Triple (r+3)) : Tensor (ι:=ι) (r+3) :=
  kernelInFrame κ H (tripleFrame e)

def creation (κ : ι→ι→ι→ι→ℝ) (H : Tensor (ι:=ι) (r+1)) :
    Tensor (ι:=ι) (r+3) := fun a => ∑ e,kernel κ H e a

def annihilation (κ : ι→ι→ι→ι→ℝ) (T : Tensor (ι:=ι) (r+3)) :
    Tensor (ι:=ι) (r+1) := fun a =>
  ∑ i,∑ j,∑ k,κ i j k (a 0)*T (Fin.cons i (Fin.cons j (Fin.cons k (Fin.tail a))))

@[simp] theorem kernelInFrame_comp (κ : ι→ι→ι→ι→ℝ)
    (H : Tensor (ι:=ι) (r+1)) (F : Fin 3 ⊕ Fin r ≃ Fin (r+3))
    (π : Equiv.Perm (Fin (r+3))) (a : Fin (r+3)→ι) :
    kernelInFrame κ H F (a∘π)=kernelInFrame κ H (F.trans π) a := rfl

end KLSBelow25.TripleTensor
#print axioms KLSBelow25.TripleTensor.tripleFrame_inr_not_mem
