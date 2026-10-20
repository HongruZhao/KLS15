import KLS.DirectionalWordAlgebra
import Mathlib.Data.List.Perm.Basic

/-! Exact multiplicity in differentiation of a symmetric ordered-index
tensor contraction. Every erased slot contributes the same term. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem ofFn_insertNth_perm_cons {α : Type*} {d : ℕ}
    (k : Fin (d+1)) (j : α) (b : Fin d → α) :
    List.Perm (List.ofFn (Fin.insertNth (α := fun _ => α) k j b)) (List.ofFn (Fin.cons j b)) := by
  have hp := List.getElem_cons_eraseIdx_perm
    (l := List.ofFn (Fin.insertNth (α := fun _ => α) k j b)) (n := k.val) (by simpa using k.isLt)
  rw [KLS.list_ofFn_eraseIdx] at hp
  have he : (fun l => (Fin.insertNth (α := fun _ => α) k j b) (k.succAbove l))=b := by
    funext l
    simp
  rw [he] at hp
  simpa only [List.getElem_ofFn,Fin.insertNth_apply_same,List.ofFn_cons] using hp.symm

theorem symmetric_tuple_erased_contraction {α : Type*} [Fintype α] [DecidableEq α]
    {d : ℕ} (t : (Fin (d+1) → α) → ℝ)
    (hs : ∀ a b, List.Perm (List.ofFn a) (List.ofFn b) → t a=t b)
    (p : (Fin d → α) → ℝ) (j : α) :
    (∑ a : Fin (d+1) → α, t a *
      ∑ k : Fin (d+1), (if a k=j then (1 : ℝ) else 0)*p (fun l => a (k.succAbove l))) =
      (d+1 : ℕ)*∑ b : Fin d → α, t (Fin.cons j b)*p b := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hk (k : Fin (d+1)) :
      (∑ a : Fin (d+1) → α, t a*((if a k=j then (1 : ℝ) else 0)*p (fun l => a (k.succAbove l)))) =
        ∑ b : Fin d → α, t (Fin.cons j b)*p b := by
    calc
      _ = ∑ q : α × (Fin d → α), t (Fin.insertNth (α := fun _ => α) k q.1 q.2)*
          ((if (Fin.insertNth (α := fun _ => α) k q.1 q.2) k=j then (1 : ℝ) else 0)*
            p (fun l => (Fin.insertNth (α := fun _ => α) k q.1 q.2) (k.succAbove l))) := by
        symm
        exact Fintype.sum_equiv (Fin.insertNthEquiv (fun _ : Fin (d+1) => α) k) _ _ (fun _ => rfl)
      _ = ∑ b : Fin d → α, t (Fin.insertNth (α := fun _ => α) k j b)*p b := by
        rw [Fintype.sum_prod_type]
        simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hs _ _ (ofFn_insertNth_perm_cons k j b)]
  simp_rw [hk]
  simp only [Finset.sum_const,Fintype.card_fin,Finset.card_univ,nsmul_eq_mul]
  exact Finset.mul_sum _ _ _

end KLSBelow25
#print axioms KLSBelow25.ofFn_insertNth_perm_cons
#print axioms KLSBelow25.symmetric_tuple_erased_contraction
