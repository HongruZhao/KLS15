import KLSConstantImprovement.TriplePositiveEnergyWeightedCharges
import KLSConstantImprovement.TriplePositiveEnergyHarmonicPayment
import ActualTwoRowsHarmonicCenteredDrift

/-! Actual reserved pair and harmonic triple drift under one shared budget. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLSConstantImprovement.TriplePositiveEnergyWeightedBudgetDrift
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.PositiveEnergyWeightedDrift
open KLSConstantImprovement.TriplePositiveEnergyWeightedDrift
open KLSConstantImprovement.TriplePositiveEnergyWeightedCharges
open KLSConstantImprovement.TriplePositiveEnergyHarmonicPayment
variable {n : ℕ}
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

def extra (young t zeta : ℕ → ℝ) (d : ℕ) : ℝ :=
  if 4 ≤ d then tripleHarmonicThetaProfile zeta d*tripleHarmonicEtaProfile zeta d*young (d-2)*
    (t d/(t 3*t (d-2))) else 0

def rawFirstCost (young t theta lambda zeta : ℕ → ℝ) (d : ℕ) : ℝ :=
  selectedFirstCost young t (twoRowsProfile theta (tripleHarmonicThetaProfile zeta))
    (twoRowsLambda lambda (tripleHarmonicLambdaProfile zeta)) d+extra young t zeta d

def cost (K C : ℝ) (young t theta lambda zeta : ℕ → ℝ) (d : ℕ) : ℝ :=
  (K*C/young d)*(d : ℝ)^2+(if 3 ≤ d then rawFirstCost young t theta lambda zeta d else 0)+
    t 3*tripleHarmonicNeighborCharge K young zeta d

theorem actual_full_reserved_proper_drift_le
    {mu : Measure (Space n)} (hmu : admissibleMeasure mu) {f : Space n → ℝ} (hf : MemLp f 2 mu)
    {K C : ℝ} (hK : 0<K) (young t theta lambda zeta : ℕ → ℝ)
    (hy : ∀ d,2 ≤ d → 0<young d) (ht : ∀ d,2 ≤ d → 0<t d)
    (hth : ∀ d,3 ≤ d → theta d ≤ 1) (hl : ∀ d,2 ≤ d → lambda d ≤ 1)
    (hboundary : ∀ d,2 ≤ d → lambda d=1 → theta (d+1)=1)
    (hz : ∀ b,2 ≤ b → 0 ≤ zeta b) (hcap : ∀ (b : ℕ),2 ≤ b → tripleHarmonicRatio (b : ℝ)*zeta b<1)
    (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n → ℝ,MemLp g 2 mu → 
      (∑ d ∈ Finset.Icc 2 (N-1),weight K t d*actualAppellEnergy mu g d) ≤ C*(∫ x,(g x)^2 ∂mu)) :
    2*(∑ d ∈ Finset.Icc 3 N,weight K t d*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellProperRemainder mu f d))+
      (∑ b ∈ Finset.Icc 2 N,kappa K young t lambda b*weight K t b*actualCanonicalContractionSquare mu f 2 (b-1)) ≤ 
      (∑ d ∈ Finset.Icc 3 N,rawFirstCost young t theta lambda zeta d*weight K t d*actualAppellEnergy mu f d)+
      (∑ b ∈ Finset.Icc 2 N,(K*C/young b)*(b : ℝ)^2*weight K t b*actualAppellEnergy mu f b)+
      (∑ b ∈ Finset.Icc 2 N,t 3*tripleHarmonicNeighborCharge K young zeta b*weight K t b*actualAppellEnergy mu f b)+
      2*(∑ d ∈ Finset.Icc 3 N,theta d*weight K t d*
        (actualAppellCoefficient mu f d ⬝ᵥ actualAppellPairContractionSum mu f d)) := by
  have htrip:∀ d,3 ≤ d → tripleHarmonicThetaProfile zeta d ≤ 1 := by
    intro d hd
    exact (tripleHarmonicThetaProfile_lt_one zeta hz hcap d).le
  have hltrip:∀ d,2 ≤ d → tripleHarmonicLambdaProfile zeta d<1:=tripleHarmonicLambdaProfile_lt_one zeta hcap
  have hproper:=actual_two_rows_retained_le hmu hf hK young t theta (tripleHarmonicThetaProfile zeta)
    lambda (tripleHarmonicLambdaProfile zeta) hy ht hth htrip hl hltrip hboundary N hN hprevious
  have hper (d : ℕ) (hd:d∈Finset.Icc 3 N) :
      2*(tripleHarmonicThetaProfile zeta d*weight K t d*
        (actualAppellCoefficient mu f d ⬝ᵥ actualAppellProperTripleContractionSum mu f d)) ≤ 
      extra young t zeta d*weight K t d*actualAppellEnergy mu f d+
      tripleCharge mu f K young t (tripleHarmonicLambdaProfile zeta) d+
      (if 4 ≤ d then t 3*tripleHarmonicNeighborCharge K young zeta (d-2)*weight K t (d-2)*
        actualAppellEnergy mu f (d-2) else 0) := by
    by_cases hd4:4 ≤ d
    · have hp:=actual_harmonic_triple_payment hmu hf hK young t zeta hy ht hz d hd4
      simp only [actualAppellProperTripleContractionSum,extra,tripleCharge,ite_eq_left hd4]
      convert hp using 1 <;> ring
    · simp [actualAppellProperTripleContractionSum,extra,tripleCharge,tripleHarmonicThetaProfile,hd4]
  have hyoung:=Finset.sum_le_sum hper
  rw [←Finset.mul_sum] at hyoung
  simp only [Finset.sum_add_distrib] at hproper hyoung
  have hout:=sum_two_previous_degrees_le N (fun b=>t 3*tripleHarmonicNeighborCharge K young zeta b*
    weight K t b*actualAppellEnergy mu f b) (by
      intro b hb
      have hb2:2 ≤ b:=(Finset.mem_Icc.mp hb).1
      have hn:=tripleHarmonicNeighborCharge_nonneg hK young zeta b hb2 (hy b hb2) (hz b hb2)
      exact mul_nonneg (mul_nonneg (mul_nonneg (ht 3 (by omega)).le hn)
        (weight_positive hK t b (ht b hb2)).le) (actualAppellEnergy_nonneg _ _ _))
  have he:(∑ d ∈ Finset.Icc 3 N,rawFirstCost young t theta lambda zeta d*weight K t d*actualAppellEnergy mu f d)=
      (∑ d ∈ Finset.Icc 3 N,selectedFirstCost young t
        (twoRowsProfile theta (tripleHarmonicThetaProfile zeta)) (twoRowsLambda lambda (tripleHarmonicLambdaProfile zeta)) d*
        weight K t d*actualAppellEnergy mu f d)+
      ∑ d ∈ Finset.Icc 3 N,extra young t zeta d*weight K t d*actualAppellEnergy mu f d := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    unfold rawFirstCost
    ring
  rw [he]
  linarith

end KLSConstantImprovement.TriplePositiveEnergyWeightedBudgetDrift
#print axioms KLSConstantImprovement.TriplePositiveEnergyWeightedBudgetDrift.actual_full_reserved_proper_drift_le
