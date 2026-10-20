import ActualSymmetricQuadraticNoise

/-! The three cubic lower contractions have correlated coordinates.
Keeping their Gram matrix improves the triangle bound 24 to sqrt(384),
and, more usefully, keeps the factor sqrt(E₂) in the cubic drift. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace KLSBelow25.CubicRemainderImprovement
open KLSBelow25.CubicSymmetricNoise

variable {ι : Type*} [Fintype ι]

def remainder (U : Array3 ι) : Array3 ι :=
  fun i j k => U i j k + U i k j + U j k i

theorem remainder_square (U : Array3 ι)
    (hU : ∀ i j k, U i j k = U j i k) :
    square (remainder U) = 3 * square U + 6 * cross U := by
  have hh := symPart_square U hU
  have he : square (symPart U) = (4/9 : ℝ)*square (remainder U) := by
    unfold square symPart remainder
    rw [← tripleSum_smul]
    congr 1
    funext i j k
    ring
  rw [he] at hh
  linarith

theorem remainder_square_le {E : ℝ} (U : Array3 ι)
    (hU : ∀ i j k, U i j k = U j i k)
    (hQ : square U ≤ 8*E) (hR : cross U ≤ 4*E) :
    square (remainder U) ≤ 48*E := by
  rw [remainder_square U hU]
  linarith

end KLSBelow25.CubicRemainderImprovement

namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25.CubicRemainderImprovement

theorem actualCubicRemainder_square_le {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    KLSBelow25.CubicSymmetricNoise.square (remainder (actualCubicSlotArray μ f)) ≤
      48*actualAppellEnergy μ f 2 := by
  exact remainder_square_le _ (actualCubicSlotArray_first_symmetry μ f)
    (actualCubicSlotArray_square_le_eight hμ f)
    (actualCubicSlotArray_cross_le_four hμ hf)

end KLS.DeterministicBridgeIntegration

#print axioms KLSBelow25.CubicRemainderImprovement.remainder_square
#print axioms KLS.DeterministicBridgeIntegration.actualCubicRemainder_square_le
