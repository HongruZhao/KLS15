import LocalizedTensorTempered
import PolyharmonicSobolevLifting

/-! Actual local Fourier-Sobolev membership of every lower weak jet in the
constructed primitive tower, after an arbitrary smooth compact multiplier. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric TemperedDistribution
open scoped ContDiff Topology BigOperators SchwartzMap LineDeriv
namespace KLS.DeterministicBridgeIntegration
open KLS KLSBelow25
variable {n s : ℕ} {φ : Space n → ℝ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem compactTensorWordTempered_memSobolev (hφ : ContDiff ℝ 1 φ)
    (U : (k : ℕ) → OrderedTensorField φ k)
    (hgraph : ∀ k, k < s → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
      finitePrimitiveValue (OrderedTensorIndex n k) V = U k ∧
        ∀ I i, weightedH1Derivative φ i (V I) = U (k + 1) (Fin.cons i I))
    (q : ℕ) (L : List (Fin n)) (hL : L.length+q ≤ s)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    MemSobolev (q : ℝ) 2
      (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U L)) := by
  induction q generalizing L χ with
  | zero =>
    simpa only [Nat.cast_zero] using
      compactWeightedTempered_memSobolev_zero hφ.continuous hχ.continuous hc (tensorWordLp U L)
  | succ q ih =>
    have hlo := ih L (by omega) hχ hc
    have hdi (i : Fin n) : MemSobolev (q : ℝ) 2
        (∂_{EuclideanSpace.basisFun (Fin n) ℝ i}
          (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U L))) := by
      rw [EuclideanSpace.basisFun_apply,
        compactTensorWordTempered_lineDeriv hφ U hgraph L (by omega) i (hχ.of_le (by simp)) hc]
      have hχd : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative χ i) :=
        contDiff_coordinateDerivative hχ (m := (⊤ : ℕ∞)) (by simp) i
      exact (ih (i::L) (by simp only [List.length_cons]; omega) hχ hc).add
        (ih L (by omega) hχd (hasCompactSupport_coordinateDerivative hc i))
    simpa only [Nat.cast_add,Nat.cast_one] using
      tempered_sobolev_first_derivatives_lift (EuclideanSpace.basisFun (Fin n) ℝ) hlo hdi

 theorem compactTensorPrimitive_memSobolev (hφ : ContDiff ℝ 1 φ)
    (U : (k : ℕ) → OrderedTensorField φ k)
    (hgraph : ∀ k, k < s → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
      finitePrimitiveValue (OrderedTensorIndex n k) V = U k ∧
        ∀ I i, weightedH1Derivative φ i (V I) = U (k + 1) (Fin.cons i I))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    MemSobolev (s : ℝ) 2
      (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U [])) :=
  compactTensorWordTempered_memSobolev hφ U hgraph s [] (by simp) hχ hc

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.compactTensorWordTempered_memSobolev
#print axioms KLS.DeterministicBridgeIntegration.compactTensorPrimitive_memSobolev
