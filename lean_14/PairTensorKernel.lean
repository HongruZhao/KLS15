import PairProjectionDefinitions
import AppellTensorTwoSlot

/-! Literal unordered-pair cubic insertion into ordered coordinate tensors.
The pair frame consists of its two sorted entries followed by its sorted
complement. The norm is the ordered Hilbert--Schmidt norm. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.PairTensor
open PairProjection

variable {r : ℕ} {ι : Type*} [Fintype ι]

abbrev Tensor (d : ℕ) := (Fin d → ι) → ℝ

def square {d : ℕ} (T : Tensor (ι := ι) d) : ℝ := ∑ a, T a ^ 2

def pairing {d : ℕ} (S T : Tensor (ι := ι) d) : ℝ := ∑ a, S a * T a

def Symmetric {d : ℕ} (T : Tensor (ι := ι) d) : Prop :=
  ∀ (π : Equiv.Perm (Fin d)) a, T (a ∘ π) = T a

theorem complement_card (e : Pair (r+2)) : e.valᶜ.card = r := by
  rw [Finset.card_compl, Fintype.card_fin, e.property]
  omega

def pairFrame (e : Pair (r+2)) : Fin 2 ⊕ Fin r ≃ Fin (r+2) :=
  ((e.val.orderIsoOfFin e.property).toEquiv.sumCongr
    ((e.valᶜ.orderIsoOfFin (complement_card e)).toEquiv.trans
      (Equiv.subtypeEquivRight (fun _ => Finset.mem_compl)))).trans
        (Equiv.sumCompl (fun i => i ∈ e.val))

@[simp] theorem pairFrame_inl (e : Pair (r+2)) (i : Fin 2) :
    pairFrame e (Sum.inl i) = e.val.orderEmbOfFin e.property i := rfl

@[simp] theorem pairFrame_inr (e : Pair (r+2)) (i : Fin r) :
    pairFrame e (Sum.inr i) = e.valᶜ.orderEmbOfFin (complement_card e) i := rfl

@[simp] theorem pairFrame_inl_mem (e : Pair (r+2)) (i : Fin 2) :
    pairFrame e (Sum.inl i) ∈ e.val := by
  simp only [pairFrame_inl, Finset.orderEmbOfFin_mem]

@[simp] theorem pairFrame_inr_not_mem (e : Pair (r+2)) (i : Fin r) :
    pairFrame e (Sum.inr i) ∉ e.val := by
  simpa only [pairFrame_inr, Finset.mem_compl] using
    Finset.orderEmbOfFin_mem e.valᶜ (complement_card e) i

def kernelInFrame (κ : ι → ι → ι → ℝ) (H : Tensor (ι := ι) (r+1))
    (F : Fin 2 ⊕ Fin r ≃ Fin (r+2)) (a : Fin (r+2) → ι) : ℝ :=
  ∑ m, κ (a (F (Sum.inl 0))) (a (F (Sum.inl 1))) m *
    H (Fin.cons m (fun j => a (F (Sum.inr j))))

def kernel (κ : ι → ι → ι → ℝ) (H : Tensor (ι := ι) (r+1))
    (e : Pair (r+2)) : Tensor (ι := ι) (r+2) :=
  kernelInFrame κ H (pairFrame e)

def creation (κ : ι → ι → ι → ℝ) (H : Tensor (ι := ι) (r+1)) :
    Tensor (ι := ι) (r+2) := fun a => ∑ e, kernel κ H e a

def annihilation (κ : ι → ι → ι → ℝ) (T : Tensor (ι := ι) (r+2)) :
    Tensor (ι := ι) (r+1) := fun a =>
  ∑ i, ∑ j, κ i j (a 0) * T (Fin.cons i (Fin.cons j (Fin.tail a)))

@[simp] theorem kernelInFrame_comp (κ : ι → ι → ι → ℝ)
    (H : Tensor (ι := ι) (r+1)) (F : Fin 2 ⊕ Fin r ≃ Fin (r+2))
    (π : Equiv.Perm (Fin (r+2))) (a : Fin (r+2) → ι) :
    kernelInFrame κ H F (a ∘ π) = kernelInFrame κ H (F.trans π) a := rfl

@[simp] theorem square_nonneg {d : ℕ} (T : Tensor (ι := ι) d) : 0 ≤ square T := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end KLSBelow25.PairTensor
#print axioms KLSBelow25.PairTensor.pairFrame_inr_not_mem
