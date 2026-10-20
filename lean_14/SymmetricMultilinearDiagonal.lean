import KLS.LocalMixedFrechet
import Mathlib

/-! A symmetric continuous multilinear map over the reals is determined
by its diagonal.  The proof differentiates its diagonal polynomial and
uses the exact finite embedding formula for a multilinear derivative. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff
namespace KLS.DeterministicBridgeIntegration
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {d : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3

 def MultilinearPermutationInvariant
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) ℝ) : Prop :=
  ∀ (m : Fin d → E) (σ : Equiv.Perm (Fin d)), T (m ∘ σ) = T m

 theorem symmetric_diagonal_iteratedFDeriv
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) ℝ)
    (hT : MultilinearPermutationInvariant T) (m : Fin d → E) :
    iteratedFDeriv ℝ d (fun v : E => T (fun _ => v)) 0 m =
      (Fintype.card (Fin d ↪ Fin d) : ℝ)*T m := by
  classical
  letI : DecidableEq (Fin d) := Classical.decEq _
  let L : E →L[ℝ] (Fin d → E) := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ E)
  have hs : ContDiffAt ℝ d T (L 0) := T.contDiff.contDiffAt
  have he := KLS.iteratedFDeriv_comp_clm_of_contDiffAt L 0 hs
  change iteratedFDeriv ℝ d (T ∘ L) 0 m = _
  rw [he]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [T.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.iteratedFDeriv,sum_apply]
  have hterm (e : Fin d ↪ Fin d) :
      T.iteratedFDerivComponent e.toEquivRange
        (Pi.compRightL ℝ (fun _ : Fin d => E) Subtype.val (L 0)) (fun j => L (m j)) = T m := by
    have hsur : Function.Surjective e := Finite.surjective_of_injective e.injective
    let σ : Equiv.Perm (Fin d) := Equiv.ofBijective e ⟨e.injective,hsur⟩
    rw [ContinuousMultilinearMap.iteratedFDerivComponent_apply]
    change (T fun j => if h : j ∈ Set.range e then
      L (m (e.toEquivRange.symm ⟨j,h⟩)) j else (L 0) j) = T m
    have harg :
        (fun j => if h : j ∈ Set.range e then
          L (m (e.toEquivRange.symm ⟨j,h⟩)) j else
          (L 0) j) = m ∘ σ.symm := by
      funext j
      have hj : j ∈ Set.range e := hsur j
      rw [dif_pos hj]
      change m (e.toEquivRange.symm ⟨j,hj⟩) = m (σ.symm j)
      congr 1
      apply e.injective
      have heq := congrArg Subtype.val (e.toEquivRange.apply_symm_apply ⟨j,hj⟩)
      exact heq.trans (σ.apply_symm_apply j).symm
    rw [harg]
    exact hT m σ.symm
  calc
    _ = ∑ _e : Fin d ↪ Fin d, T m := by
      apply Finset.sum_congr rfl
      intro e he
      exact hterm e
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

 theorem symmetric_multilinear_eq_of_diagonal
    (T U : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) ℝ)
    (hT : MultilinearPermutationInvariant T) (hU : MultilinearPermutationInvariant U)
    (hdiag : ∀ v : E, T (fun _ => v) = U (fun _ => v)) : T = U := by
  have he : (fun v : E => T (fun _ => v)) = (fun v : E => U (fun _ => v)) := funext hdiag
  have hn : (Fintype.card (Fin d ↪ Fin d) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨Function.Embedding.refl (Fin d)⟩).ne'
  ext m
  have hd := congrArg (fun f : E → ℝ => iteratedFDeriv ℝ d f 0 m) he
  rw [symmetric_diagonal_iteratedFDeriv T hT m,
    symmetric_diagonal_iteratedFDeriv U hU m] at hd
  exact mul_left_cancel₀ hn hd

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.symmetric_multilinear_eq_of_diagonal
