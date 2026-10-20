import ActualPairTensorCreationAffineQ
import ActualPairAppellYoung
import ActualJointCumulantContraction

/-! Literal canonical a2 square retained in the actual proper pair drift. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
open KLSBelow25.PairTensor KLSBelow25.PairProjection KLSBelow25.CoupledEnergy
variable {n r : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_pair_kernel_square_eq_canonical {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (e : Pair (r+3)) :
    square (kernel (actualThirdCubicArray μ) (actualAppellCoefficient μ f (r+2)) e)=
      actualCanonicalContractionSquare μ f 2 (r+1) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  change (∑ γ, (kernel (actualThirdCubicArray μ) (actualAppellCoefficient μ f (r+2)) e γ)^2)=_
  simp_rw [←actualSubsetAppellContraction_pair_kernel hμ hf e]
  have hh := actualSubsetAppellContraction_square_eq_canonical hμ.logConcave hf e.val
  simpa only [e.property,complement_card e] using hh

theorem actualAppellPairContractionSum_square_le_affineQ {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    square (actualAppellPairContractionSum μ f (r+3)) ≤
      (((r : ℝ)+3)*((r : ℝ)+2)/2)*actualCanonicalContractionSquare μ f 2 (r+1)+
      ((r : ℝ)+3)*((r : ℝ)+2)*
        (((r : ℝ)+2)^2+5*((r : ℝ)+2)/3-10/3)*actualAppellEnergy μ f (r+2) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  rw [actualAppellPairContractionSum_eq_creation hμ hf]
  have hb := actual_pair_creation_square_le_affineQ hμ r
    (actualAppellCoefficient μ f (r+2)) (actualAppellCoefficient_pair_symmetric hμ.logConcave hf)
  rw [actual_pair_kernel_square_eq_canonical hμ hf] at hb
  exact hb

theorem actualAppellPairContractionSum_weighted_young_affineQ {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    {K v : ℝ} (hK : 0<K) (hv : 0<v) :
    2*factorialWeight K (r+3)*
        pairing (actualAppellCoefficient μ f (r+3)) (actualAppellPairContractionSum μ f (r+3)) ≤
      v*factorialWeight K (r+3)*actualAppellEnergy μ f (r+3)+
      (((r : ℝ)+2)/(2*K*((r : ℝ)+3)*v))*factorialWeight K (r+2)*
        actualCanonicalContractionSquare μ f 2 (r+1)+
      (((r : ℝ)+2)*(((r : ℝ)+2)^2+5*((r : ℝ)+2)/3-10/3)/
        (K*((r : ℝ)+3)*v))*factorialWeight K (r+2)*actualAppellEnergy μ f (r+2) := by
  have hw := factorialWeight_nonneg hK (r+3)
  have hy := mul_le_mul_of_nonneg_left
    (pairing_young hv (actualAppellCoefficient μ f (r+3))
      (actualAppellPairContractionSum μ f (r+3))) hw
  have hb := div_le_div_of_nonneg_right
    (actualAppellPairContractionSum_square_le_affineQ (r:=r) hμ hf) hv.le
  have hb' := mul_le_mul_of_nonneg_left hb hw
  have hs := factorialWeight_step hK (r+2)
  have he :
      v*factorialWeight K (r+3)*actualAppellEnergy μ f (r+3)+
      (((r : ℝ)+2)/(2*K*((r : ℝ)+3)*v))*factorialWeight K (r+2)*
        actualCanonicalContractionSquare μ f 2 (r+1)+
      (((r : ℝ)+2)*(((r : ℝ)+2)^2+5*((r : ℝ)+2)/3-10/3)/
        (K*((r : ℝ)+3)*v))*factorialWeight K (r+2)*actualAppellEnergy μ f (r+2) =
      factorialWeight K (r+3)*
        (v*actualAppellEnergy μ f (r+3)+
          ((((r : ℝ)+3)*((r : ℝ)+2)/2)*actualCanonicalContractionSquare μ f 2 (r+1)+
            ((r : ℝ)+3)*((r : ℝ)+2)*
              (((r : ℝ)+2)^2+5*((r : ℝ)+2)/3-10/3)*actualAppellEnergy μ f (r+2))/v) := by
    rw [hs]
    push_cast
    field_simp
    ring
  rw [he]
  change factorialWeight K (r+3)*
      (2*pairing (actualAppellCoefficient μ f (r+3)) (actualAppellPairContractionSum μ f (r+3))) ≤
      factorialWeight K (r+3)*
        (v*actualAppellEnergy μ f (r+3)+square (actualAppellPairContractionSum μ f (r+3))/v) at hy
  nlinarith [hy,hb']

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_pair_kernel_square_eq_canonical
#print axioms KLS.DeterministicBridgeIntegration.actualAppellPairContractionSum_square_le_affineQ
#print axioms KLS.DeterministicBridgeIntegration.actualAppellPairContractionSum_weighted_young_affineQ
