import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Real.Basic

/-! Extend a fixed-rank symmetric ordered tensor to list coefficients,
preserving its literal values at that rank. -/
noncomputable section
namespace KLSBelow25
set_option maxHeartbeats 500000

def tupleFromLength {α : Type*} {s : ℕ} (l : List α) (h : l.length=s) : Fin s → α :=
  fun i => l.get (Fin.cast h.symm i)

theorem ofFn_tupleFromLength {α : Type*} {s : ℕ} (l : List α) (h : l.length=s) :
    List.ofFn (tupleFromLength l h)=l := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,h]
  · intro i hi hi'
    simp only [List.getElem_ofFn,tupleFromLength,List.get_eq_getElem,Fin.coe_cast]

def symmetricListExtension {α : Type*} (s : ℕ) (T : (Fin s → α) → ℝ) (l : List α) : ℝ :=
  if h : l.length=s then T (tupleFromLength l h) else 0

theorem symmetricListExtension_ofFn {α : Type*} (s : ℕ) (T : (Fin s → α) → ℝ)
    (I : Fin s → α) : symmetricListExtension s T (List.ofFn I)=T I := by
  have hl : (List.ofFn I).length=s := List.length_ofFn
  rw [symmetricListExtension,dif_pos hl]
  congr 1
  funext i
  simp [tupleFromLength]

theorem symmetricListExtension_perm {α : Type*} (s : ℕ) (T : (Fin s → α) → ℝ)
    (hT : ∀ I J, List.Perm (List.ofFn I) (List.ofFn J) → T I=T J)
    (a b : List α) (h : List.Perm a b) :
    symmetricListExtension s T a=symmetricListExtension s T b := by
  by_cases ha : a.length=s
  · have hb : b.length=s := h.length_eq.symm.trans ha
    simp only [symmetricListExtension,dif_pos ha,dif_pos hb]
    apply hT
    rw [ofFn_tupleFromLength,ofFn_tupleFromLength]
    exact h
  · have hb : b.length≠s := fun he => ha (h.length_eq.trans he)
    simp only [symmetricListExtension,dif_neg ha,dif_neg hb]

end KLSBelow25
#print axioms KLSBelow25.symmetricListExtension_ofFn
#print axioms KLSBelow25.symmetricListExtension_perm
