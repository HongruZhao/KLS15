import ActualTripleAppellRemainder
import ActualPairAppellYoung

/-! Exact normalization of a genuine size-three insertion square bound.
The square bound is an explicit intermediate input, not a public KLS
endpoint premise. Actual tensor geometry must discharge it. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25.PairTensor KLSBelow25.CoupledEnergy
variable {n r : ℕ}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem actualAppellTripleContractionSum_weighted_young_of_affine_square
    {μ : Measure (Space n)} (f : Space n → ℝ) {K v A R : ℝ}
    (hK : 0 < K) (hv : 0 < v)
    (hbound : square (actualAppellTripleContractionSum μ f (r+4)) ≤
      A*actualCanonicalContractionSquare μ f 3 (r+1)+R*actualAppellEnergy μ f (r+2)) :
    2*factorialWeight K (r+4)*
      pairing (actualAppellCoefficient μ f (r+4)) (actualAppellTripleContractionSum μ f (r+4)) ≤
      v*factorialWeight K (r+4)*actualAppellEnergy μ f (r+4)+
      (A/(K^2*((r : ℝ)+4)^2*((r : ℝ)+3)^2*v))*factorialWeight K (r+2)*
        actualCanonicalContractionSquare μ f 3 (r+1)+
      (R/(K^2*((r : ℝ)+4)^2*((r : ℝ)+3)^2*v))*factorialWeight K (r+2)*
        actualAppellEnergy μ f (r+2) := by
  have hw := factorialWeight_nonneg hK (r+4)
  have hy := mul_le_mul_of_nonneg_left
    (pairing_young hv (actualAppellCoefficient μ f (r+4))
      (actualAppellTripleContractionSum μ f (r+4))) hw
  have hb := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hbound hv.le) hw
  have hs1 := factorialWeight_step hK (r+2)
  have hs2 := factorialWeight_step hK (r+3)
  norm_num only [Nat.add_assoc,Nat.reduceAdd] at hs1 hs2
  have he :
      (A/(K^2*((r : ℝ)+4)^2*((r : ℝ)+3)^2*v))*factorialWeight K (r+2)*
        actualCanonicalContractionSquare μ f 3 (r+1)+
      (R/(K^2*((r : ℝ)+4)^2*((r : ℝ)+3)^2*v))*factorialWeight K (r+2)*
        actualAppellEnergy μ f (r+2) =
      factorialWeight K (r+4)*
        ((A*actualCanonicalContractionSquare μ f 3 (r+1)+
          R*actualAppellEnergy μ f (r+2))/v) := by
    rw [hs1,hs2]
    push_cast
    field_simp
  rw [add_assoc,he]
  change factorialWeight K (r+4)*
      (2*pairing (actualAppellCoefficient μ f (r+4))
        (actualAppellTripleContractionSum μ f (r+4))) ≤
    factorialWeight K (r+4)*
      (v*actualAppellEnergy μ f (r+4)+square (actualAppellTripleContractionSum μ f (r+4))/v) at hy
  nlinarith [hy,hb]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualAppellTripleContractionSum_weighted_young_of_affine_square
