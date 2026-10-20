import ActualPairAppellContraction

/-! The literal size-two part of the actual Appell lower drift is the
symmetric cubic creation map. The retained neighboring energy is explicit. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
open KLSBelow25.PairTensor KLSBelow25.PairProjection
variable {n r : ℕ}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def actualAppellPairContractionSum (μ : Measure (Space n)) (f : Space n→ℝ)
    (d : ℕ) : Tensor (ι := Fin n) d :=
  ∑ S : Finset (Fin d), if S.card=2 then actualSubsetAppellContraction μ f d S else 0

theorem actualAppellPairContractionSum_eq_creation {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    actualAppellPairContractionSum μ f (r+2) =
      creation (actualThirdCubicArray μ) (actualAppellCoefficient μ f (r+1)) := by
  funext γ
  have he : (Finset.univ : Finset (Finset (Fin (r+2)))).filter (fun S => S.card=2) = pairs (r+2) := by
    ext S
    simp [mem_pairs]
  unfold actualAppellPairContractionSum
  simp only [Finset.sum_apply]
  change (∑ S : Finset (Fin (r+2)), (if S.card=2 then
      actualSubsetAppellContraction μ f (r+2) S else 0) γ)=_
  simp only [ite_apply,Pi.zero_apply]
  rw [←Finset.sum_filter,he,←sum_pair_values]
  simp_rw [actualSubsetAppellContraction_pair_kernel hμ hf]
  rfl

theorem actualAppellPairContractionSum_square_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    square (actualAppellPairContractionSum μ f (r+3)) ≤
      ((r : ℝ)+3)^2*((r : ℝ)+2)*((r : ℝ)+3-1/3)*actualAppellEnergy μ f (r+2) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  rw [actualAppellPairContractionSum_eq_creation hμ hf]
  exact actual_pair_creation_square_le hμ r _
    (actualAppellCoefficient_pair_symmetric hμ.logConcave hf)

theorem actualAppellPairContractionSum_pairing_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    pairing (actualAppellCoefficient μ f (r+3)) (actualAppellPairContractionSum μ f (r+3)) ≤
      Real.sqrt (actualAppellEnergy μ f (r+3))*
        Real.sqrt (((r : ℝ)+3)^2*((r : ℝ)+2)*((r : ℝ)+3-1/3)*
          actualAppellEnergy μ f (r+2)) := by
  have hc := pairing_sq_le (actualAppellCoefficient μ f (r+3))
    (actualAppellPairContractionSum μ f (r+3))
  have hb := mul_le_mul_of_nonneg_left (actualAppellPairContractionSum_square_le (r:=r) hμ hf)
    (actualAppellEnergy_nonneg μ f (r+3))
  have hE := actualAppellEnergy_nonneg μ f (r+3)
  have hR : 0≤((r : ℝ)+3)^2*((r : ℝ)+2)*((r : ℝ)+3-1/3)*
      actualAppellEnergy μ f (r+2) := by
    have hr : 0≤(r : ℝ) := Nat.cast_nonneg _
    have hf' : 0≤(r : ℝ)+3-1/3 := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) hf')
      (actualAppellEnergy_nonneg μ f (r+2))
  have hsE := Real.sq_sqrt hE
  have hsR := Real.sq_sqrt hR
  have hn := mul_nonneg (Real.sqrt_nonneg (actualAppellEnergy μ f (r+3)))
    (Real.sqrt_nonneg (((r : ℝ)+3)^2*((r : ℝ)+2)*((r : ℝ)+3-1/3)*actualAppellEnergy μ f (r+2)))
  change (pairing (actualAppellCoefficient μ f (r+3)) (actualAppellPairContractionSum μ f (r+3)))^2 ≤
    actualAppellEnergy μ f (r+3)*square (actualAppellPairContractionSum μ f (r+3)) at hc
  nlinarith [hc.trans hb,sq_nonneg
    (pairing (actualAppellCoefficient μ f (r+3)) (actualAppellPairContractionSum μ f (r+3))+
      Real.sqrt (actualAppellEnergy μ f (r+3))*
        Real.sqrt (((r : ℝ)+3)^2*((r : ℝ)+2)*((r : ℝ)+3-1/3)*actualAppellEnergy μ f (r+2)))]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualAppellPairContractionSum_eq_creation
#print axioms KLS.DeterministicBridgeIntegration.actualAppellPairContractionSum_square_le
#print axioms KLS.DeterministicBridgeIntegration.actualAppellPairContractionSum_pairing_le
