import ActualPairAppellRemainder
import CoupledEnergyShift

/-! Exact factorial-normalized Young estimate for the genuine size-two
Appell lower drift. The upper and lower neighboring energies remain visible. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace KLSBelow25.PairTensor
variable {ι : Type*} [Fintype ι] {d : ℕ}

theorem pairing_young {v : ℝ} (hv : 0 < v) (A B : Tensor (ι := ι) d) :
    2 * pairing A B ≤ v * square A + square B / v := by
  have hpoint (a : Fin d → ι) :
      2 * A a * B a ≤ v * (A a)^2 + (B a)^2 / v := by
    apply (mul_le_mul_iff_right₀ hv).mp
    have he : v * (v * (A a)^2 + (B a)^2 / v) =
        v^2 * (A a)^2 + (B a)^2 := by
      field_simp
    rw [he]
    nlinarith [sq_nonneg (v * A a - B a)]
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin d → ι))) => hpoint a)
  simpa only [pairing,square,Finset.mul_sum,Finset.sum_div,Finset.sum_add_distrib,mul_assoc] using hs

end KLSBelow25.PairTensor
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25.PairTensor KLSBelow25.CoupledEnergy
variable {n r : ℕ}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem actualAppellPairContractionSum_weighted_young {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    {K v : ℝ} (hK : 0 < K) (hv : 0 < v) :
    2 * factorialWeight K (r+3) *
        pairing (actualAppellCoefficient μ f (r+3))
          (actualAppellPairContractionSum μ f (r+3)) ≤
      v * factorialWeight K (r+3) * actualAppellEnergy μ f (r+3) +
        (((r : ℝ)+2)*((r : ℝ)+8/3)/(K*v)) *
          factorialWeight K (r+2) * actualAppellEnergy μ f (r+2) := by
  have hw := factorialWeight_nonneg hK (r+3)
  have hy := mul_le_mul_of_nonneg_left
    (pairing_young hv (actualAppellCoefficient μ f (r+3))
      (actualAppellPairContractionSum μ f (r+3))) hw
  have hb := div_le_div_of_nonneg_right
    (actualAppellPairContractionSum_square_le (r:=r) hμ hf) (le_of_lt hv)
  have hb' := mul_le_mul_of_nonneg_left hb hw
  have hs := factorialWeight_step hK (r+2)
  have he : (((r : ℝ)+2)*((r : ℝ)+8/3)/(K*v)) *
        factorialWeight K (r+2) * actualAppellEnergy μ f (r+2) =
      factorialWeight K (r+3) *
        ((((r : ℝ)+3)^2*((r : ℝ)+2)*((r : ℝ)+3-1/3)*
          actualAppellEnergy μ f (r+2))/v) := by
    rw [hs]
    push_cast
    field_simp
    ring
  rw [he]
  change factorialWeight K (r+3) *
      (2 * pairing (actualAppellCoefficient μ f (r+3))
        (actualAppellPairContractionSum μ f (r+3))) ≤
    factorialWeight K (r+3) *
      (v * actualAppellEnergy μ f (r+3) +
        square (actualAppellPairContractionSum μ f (r+3)) / v) at hy
  nlinarith [hy,hb']

end KLS.DeterministicBridgeIntegration
#print axioms KLSBelow25.PairTensor.pairing_young
#print axioms KLS.DeterministicBridgeIntegration.actualAppellPairContractionSum_weighted_young
