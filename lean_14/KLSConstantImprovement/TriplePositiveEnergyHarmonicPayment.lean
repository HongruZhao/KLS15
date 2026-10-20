import KLSConstantImprovement.TriplePositiveEnergyWeightedDrift

/-! The actual harmonic triple Young estimate with literal positive
energy multipliers. Its selected canonical square cancels exactly. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLSConstantImprovement.TriplePositiveEnergyHarmonicPayment
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.PositiveEnergyWeightedDrift
variable {n : ℕ}
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

def tripleGain (young zeta : ℕ → ℝ) (b : ℕ) : ℝ :=
  young b-young b/harmonicRatioDenom (tripleHarmonicRatio (b : ℝ)) (zeta b)

def harmonicFirstCost (young t theta lambda zeta : ℕ → ℝ) (d : ℕ) : ℝ :=
  firstCost young t theta lambda d-
    if 4 ≤ d then tripleGain young zeta (d-2)*(t d/(t 3*t (d-2))) else 0

theorem actual_harmonic_triple_payment
    {mu : Measure (Space n)} (hmu : admissibleMeasure mu) {f : Space n → ℝ} (hf : MemLp f 2 mu)
    {K : ℝ} (hK : 0<K) (young t zeta : ℕ → ℝ)
    (hy : ∀ d,2 ≤ d → 0<young d) (ht : ∀ d,2 ≤ d → 0<t d)
    (hz : ∀ b,2 ≤ b → 0 ≤ zeta b) (d : ℕ) (hd : 4 ≤ d) :
    2*tripleHarmonicThetaProfile zeta d*weight K t d*
      (actualAppellCoefficient mu f d ⬝ᵥ actualAppellTripleContractionSum mu f d) ≤ 
      (tripleHarmonicThetaProfile zeta d*tripleHarmonicEtaProfile zeta d*young (d-2)*
        (t d/(t 3*t (d-2))))*weight K t d*actualAppellEnergy mu f d+
      (tripleHarmonicLambdaProfile zeta (d-2)*K/young (d-2))*(normalizedQ mu f K t 3 (d-2))^2+
      t 3*tripleHarmonicNeighborCharge K young zeta (d-2)*weight K t (d-2)*actualAppellEnergy mu f (d-2) := by
  have hb:2 ≤ d-2:=by omega
  have htd:0<t d:=ht d (by omega)
  have ht3:0<t 3:=ht 3 (by omega)
  have htb:0<t (d-2):=ht (d-2) hb
  have hyb:0<young (d-2):=hy (d-2) hb
  let effective:=fun b=>young b*(t d/(t 3*t b))
  have he:∀ b,2 ≤ b → 0<effective b := by
    intro b hb'
    dsimp only [effective]
    exact mul_pos (hy b hb') (div_pos htd (mul_pos ht3 (ht b hb')))
  have hh:=mul_le_mul_of_nonneg_left
    (actual_harmonic_triple_young_matching_charge hmu hf hK effective zeta he hz d hd) htd.le
  have hfirst:t d*(tripleHarmonicThetaProfile zeta d*tripleHarmonicEtaProfile zeta d*effective (d-2)*
      (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy mu f d)=
      (tripleHarmonicThetaProfile zeta d*tripleHarmonicEtaProfile zeta d*young (d-2)*
        (t d/(t 3*t (d-2))))*weight K t d*actualAppellEnergy mu f d := by
    unfold weight CoupledEnergy.factorialWeight
    dsimp only [effective]
    ring
  have hcharge:t d*actualTwoRowsTripleCharge mu f K effective (tripleHarmonicLambdaProfile zeta) d=
      (tripleHarmonicLambdaProfile zeta (d-2)*K/young (d-2))*(normalizedQ mu f K t 3 (d-2))^2 := by
    unfold actualTwoRowsTripleCharge
    rw [ite_eq_left hd]
    unfold normalizedQ
    rw [mul_pow,mul_pow,Real.sq_sqrt ht3.le,Real.sq_sqrt htb.le]
    dsimp only [effective]
    field_simp [ne_of_gt htd,ne_of_gt ht3,ne_of_gt htb,ne_of_gt hyb]
  have hout:t d*(tripleHarmonicNeighborCharge K effective zeta (d-2)*
      (K^(d-2)*((d-2).factorial : ℝ)^2)⁻¹*actualAppellEnergy mu f (d-2))=
      t 3*tripleHarmonicNeighborCharge K young zeta (d-2)*weight K t (d-2)*actualAppellEnergy mu f (d-2) := by
    unfold tripleHarmonicNeighborCharge weight CoupledEnergy.factorialWeight
    dsimp only [effective]
    field_simp [ne_of_gt htd,ne_of_gt ht3,ne_of_gt htb,ne_of_gt hyb]
  rw [mul_add,mul_add,hfirst,hcharge,hout] at hh
  convert hh using 1
  unfold weight CoupledEnergy.factorialWeight
  ring

end KLSConstantImprovement.TriplePositiveEnergyHarmonicPayment
#print axioms KLSConstantImprovement.TriplePositiveEnergyHarmonicPayment.actual_harmonic_triple_payment
