import Mathlib

/-! Unordered pairs of coordinate positions and their literal finite
Hilbert-space sums. No measure or coefficient estimate is assumed here. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace KLSBelow25.PairProjection

def Pair (N : ℕ) := {e : Finset (Fin N) // e.card = 2}

instance (N : ℕ) : Fintype (Pair N) := inferInstanceAs (Fintype {e : Finset (Fin N) // e.card = 2})
instance (N : ℕ) : DecidableEq (Pair N) := inferInstanceAs (DecidableEq {e : Finset (Fin N) // e.card = 2})

theorem Pair.repr {N : ℕ} (e : Pair N) :
    ∃ i j : Fin N, i ≠ j ∧ e.val = {i,j} := by
  exact Finset.card_eq_two.mp e.property

def pairs (N : ℕ) : Finset (Finset (Fin N)) := Finset.univ.powersetCard 2

theorem mem_pairs {N : ℕ} (e : Finset (Fin N)) : e ∈ pairs N ↔ e.card = 2 := by
  simp [pairs]

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def sumPairs (U : Pair N → H) : H := ∑ e, U e

def star (U : Pair N → H) (i : Fin N) : H :=
  ∑ e with i ∈ e.val, U e

def projection (U : Pair N → H) : H := (2/(N : ℝ)) • sumPairs U

def Gram (U : Pair N → H) (Q R S : ℝ) : Prop :=
  ∀ e f, inner ℝ (U e) (U f) =
    if e = f then Q else if (e.val ∩ f.val).Nonempty then R else S

end KLSBelow25.PairProjection

#print axioms KLSBelow25.PairProjection.Pair.repr
