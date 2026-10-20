import PairTensorKernel
import ActualAppellSymmetry

/-! The existing actual Appell swap symmetry implies invariance under every
permutation, exactly as needed by the unordered-pair tensor realization. -/
noncomputable section
namespace KLSBelow25.PairTensor

theorem symmetric_of_swaps {ι : Type*} {d : ℕ} (T : (Fin d→ι)→ℝ)
    (hT : ∀ (s t : Fin d) a,T (a∘Equiv.swap s t)=T a) :
    ∀ (π : Equiv.Perm (Fin d)) a,T (a∘π)=T a := by
  intro π
  induction π using Equiv.Perm.swap_induction_on with
  | one => intro a;rfl
  | swap_mul π s t _ ih =>
      intro a
      change T ((a∘Equiv.swap s t)∘π)=T a
      rw [ih,hT]

end KLSBelow25.PairTensor
namespace KLS.DeterministicBridgeIntegration
open MeasureTheory KLS

theorem actualAppellCoefficient_pair_symmetric {n d : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    KLSBelow25.PairTensor.Symmetric (actualAppellCoefficient μ f d) :=
  KLSBelow25.PairTensor.symmetric_of_swaps _ (actualAppellCoefficient_symmetric hLC hf)

end KLS.DeterministicBridgeIntegration
#print axioms KLSBelow25.PairTensor.symmetric_of_swaps
#print axioms KLS.DeterministicBridgeIntegration.actualAppellCoefficient_pair_symmetric
