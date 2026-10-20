import ActualPairTensorSlotBounds
import PairTensorHilbert

/-! The vertex star of unordered-pair insertions is the actual sum of
coordinate-slot contractions, with no multiplicity or rank factor. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.PairTensor
open PairProjection
variable {r : ℕ} {ι : Type*} [Fintype ι]
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem incidentPair_injective : Function.Injective (incidentPair (r:=r)) := by
  intro s t h
  have hs : s.succ∈(incidentPair t).val := by
    rw [←h]
    simp [incidentPair]
  simpa only [incidentPair,Finset.mem_insert,Finset.mem_singleton,
    Fin.succ_ne_zero,false_or,Fin.succ_inj] using hs

theorem incidentPair_surjective (e : Pair (r+2)) (he : 0∈e.val) :
    ∃ s : Fin (r+1),incidentPair s=e := by
  obtain ⟨i,j,hij,heq⟩ := Pair.repr e
  have h0 : 0=i∨0=j := by simpa [heq] using he
  rcases h0 with hi | hj
  · subst i
    have hj : j≠0 := hij.symm
    let s : Fin (r+1) := ⟨j.val-1,by
      have hjlt := j.isLt
      have hjv : j.val≠0 := by simpa using Fin.val_ne_iff.mpr hj
      omega⟩
    have hs : s.succ=j := by
      apply Fin.ext
      dsimp [s]
      have hjv : j.val≠0 := by simpa using Fin.val_ne_iff.mpr hj
      omega
    refine ⟨s,Subtype.ext ?_⟩
    simpa only [incidentPair,hs] using heq.symm
  · subst j
    have hi : i≠0 := hij
    let s : Fin (r+1) := ⟨i.val-1,by
      have hilt := i.isLt
      have hiv : i.val≠0 := by simpa using Fin.val_ne_iff.mpr hi
      omega⟩
    have hs : s.succ=i := by
      apply Fin.ext
      dsimp [s]
      have hiv : i.val≠0 := by simpa using Fin.val_ne_iff.mpr hi
      omega
    refine ⟨s,Subtype.ext ?_⟩
    simpa only [incidentPair,hs,Finset.pair_comm] using heq.symm

theorem sum_incidentPairs {M : Type*} [AddCommMonoid M] (F : Pair (r+2)→M) :
    (∑ e with (0 : Fin (r+2))∈e.val,F e)=∑ s : Fin (r+1),F (incidentPair s) := by
  symm
  apply Finset.sum_bij (fun s _ => incidentPair s)
  · intro s _
    simp [incidentPair]
  · intro s _ t _ h
    exact incidentPair_injective h
  · intro e he
    obtain ⟨s,hs⟩ := incidentPair_surjective e (Finset.mem_filter.mp he).2
    exact ⟨s,Finset.mem_univ _,hs⟩
  · intro s _
    rfl

theorem star_kernel_cons (κ : ι→ι→ι→ℝ)
    (hκ : ∀ i j m,κ i j m=κ j i m)
    (T : Tensor (ι := ι) (r+1)) (hT : Symmetric T)
    (i : ι) (a : Fin (r+1)→ι) :
    PairProjection.star (fun e => toHilbert (kernel κ T e)) 0 (Fin.cons i a)=
      ∑ s : Fin (r+1),∑ m,κ i (a s) m*T (Function.update a s m) := by
  rw [PairProjection.star,sum_incidentPairs]
  simp only [WithLp.ofLp_sum,Finset.sum_apply,toHilbert_apply,kernel_incidentPair_cons κ hκ T hT]

end KLSBelow25.PairTensor
#print axioms KLSBelow25.PairTensor.sum_incidentPairs
#print axioms KLSBelow25.PairTensor.star_kernel_cons
