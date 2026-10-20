import Mathlib

/-! Literal unordered triples and their Hilbert Gram data. No measure,
creation estimate, or desired recurrence is assumed in these definitions. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace KLSBelow25.TripleProjection

def Triple (N : ℕ) := {e : Finset (Fin N) // e.card = 3}

instance (N : ℕ) : Fintype (Triple N) :=
  inferInstanceAs (Fintype {e : Finset (Fin N) // e.card = 3})
instance (N : ℕ) : DecidableEq (Triple N) :=
  inferInstanceAs (DecidableEq {e : Finset (Fin N) // e.card = 3})

def triples (N : ℕ) : Finset (Finset (Fin N)) := Finset.univ.powersetCard 3

theorem mem_triples {N : ℕ} (e : Finset (Fin N)) :
    e ∈ triples N ↔ e.card = 3 := by simp [triples]

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def sumTriples (U : Triple N → H) : H := ∑ e, U e

def Gram (U : Triple N → H) (Q₃ Q₂ Q₁ Q₀ : ℝ) : Prop :=
  ∀ e f, inner ℝ (U e) (U f) =
    if (e.val ∩ f.val).card = 3 then Q₃ else
    if (e.val ∩ f.val).card = 2 then Q₂ else
    if (e.val ∩ f.val).card = 1 then Q₁ else Q₀

end KLSBelow25.TripleProjection
