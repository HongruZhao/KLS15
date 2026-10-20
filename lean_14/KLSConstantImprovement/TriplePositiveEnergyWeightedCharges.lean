import KLSConstantImprovement.TriplePositiveEnergyWeightedDrift
import ActualTwoRowsAppellCharges

/-! Exact selected size-two/size-three charges with positive energy weights.
Only the unused size-two last-column cell is additionally retained. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLSConstantImprovement.TriplePositiveEnergyWeightedCharges
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.PositiveEnergyWeightedDrift
open KLSConstantImprovement.SignedReservedCanonicalDrift
open KLSConstantImprovement.TriplePositiveEnergyWeightedDrift
variable {n : ℕ}
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

def tripleCharge (mu : Measure (Space n)) (f : Space n → ℝ) (K : ℝ)
    (young t lambda3 : ℕ → ℝ) (d : ℕ) : ℝ :=
  if 4 ≤ d then (lambda3 (d-2)*K/young (d-2))*(normalizedQ mu f K t 3 (d-2))^2 else 0

theorem two_rows_charge_sum_eq (K : ℝ) (young lambda2 lambda3 : ℕ → ℝ)
    (Q : ℕ → ℕ → ℝ) (N : ℕ) (hN : 3 ≤ N) :
    (∑ p ∈ coupledDriftPairs N,(twoRowsLambda lambda2 lambda3 p.2 (p.1-p.2+1)*K/young (p.1-p.2+1))*
      (Q p.2 (p.1-p.2+1))^2)+(lambda2 N*K/young N)*(Q 2 N)^2=
      (∑ b ∈ Finset.Icc 2 N,(lambda2 b*K/young b)*(Q 2 b)^2)+
      ∑ d ∈ Finset.Icc 3 N,if 4 ≤ d then (lambda3 (d-2)*K/young (d-2))*(Q 3 (d-2))^2 else 0 := by
  classical
  have hp:(∑ p ∈ coupledDriftPairs N,(twoRowsLambda lambda2 lambda3 p.2 (p.1-p.2+1)*K/young (p.1-p.2+1))*
      (Q p.2 (p.1-p.2+1))^2)=
      (∑ p ∈ coupledDriftPairs N,((if p.2=2 then lambda2 (p.1-p.2+1) else 0)*K/young (p.1-p.2+1))*
        (Q p.2 (p.1-p.2+1))^2)+
      ∑ p ∈ coupledDriftPairs N,if p.2=3 then
        (lambda3 (p.1-p.2+1)*K/young (p.1-p.2+1))*(Q p.2 (p.1-p.2+1))^2 else 0 := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp'
    by_cases h2:p.2=2
    · have h3:p.2≠3:=by omega
      simp [twoRowsLambda,h2,h3]
    · by_cases h3:p.2=3
      · simp [twoRowsLambda,h2,h3]
      · simp [twoRowsLambda,h2,h3]
  have htr:(∑ p ∈ coupledDriftPairs N,if p.2=3 then
      (lambda3 (p.1-p.2+1)*K/young (p.1-p.2+1))*(Q p.2 (p.1-p.2+1))^2 else 0)=
      ∑ d ∈ Finset.Icc 3 N,if 4 ≤ d then (lambda3 (d-2)*K/young (d-2))*(Q 3 (d-2))^2 else 0 := by
    rw [coupledDriftPairs,Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro d hd
    have hs:d-3+1=d-2:=by have:=(Finset.mem_Icc.mp hd).1;omega
    simp only [Finset.sum_ite_eq',Finset.mem_Icc,hs]
    have he:3 ≤ d-1↔4 ≤ d:=by omega
    simp [he]
  rw [hp,htr]
  have hpair:=canonical_charge_sum_reindex K young lambda2 Q N hN
  linear_combination hpair

theorem pair_charge_eq
    (mu : Measure (Space n)) (f : Space n → ℝ) {K : ℝ} (hK : 0<K)
    (young t lambda : ℕ → ℝ) (ht : ∀ d,2 ≤ d → 0<t d) (b : ℕ) (hb : 2 ≤ b) :
    (lambda b*K/young b)*(normalizedQ mu f K t 2 b)^2=
      PositiveEnergyWeightedDrift.kappa K young t lambda b*weight K t b*
        actualCanonicalContractionSquare mu f 2 (b-1) := by
  rw [normalizedQ_sq mu f hK t 2 b (ht 2 (by omega)).le (ht b hb).le,coupledAppellScale_sq hK]
  unfold PositiveEnergyWeightedDrift.kappa weight CoupledEnergy.factorialWeight
  norm_num only [Nat.factorial,Nat.cast_ofNat]
  field_simp

theorem actual_two_rows_retained_le
    {mu : Measure (Space n)} (hmu : admissibleMeasure mu) {f : Space n → ℝ} (hf : MemLp f 2 mu)
    {K C : ℝ} (hK : 0<K) (young t theta2 theta3 lambda2 lambda3 : ℕ → ℝ)
    (hy : ∀ d,2 ≤ d → 0<young d) (ht : ∀ d,2 ≤ d → 0<t d)
    (hth2 : ∀ d,3 ≤ d → theta2 d ≤ 1) (hth3 : ∀ d,3 ≤ d → theta3 d ≤ 1)
    (hl2 : ∀ d,2 ≤ d → lambda2 d ≤ 1) (hl3 : ∀ d,2 ≤ d → lambda3 d<1)
    (hboundary : ∀ d,2 ≤ d → lambda2 d=1 → theta2 (d+1)=1) (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n → ℝ,MemLp g 2 mu → 
      (∑ d ∈ Finset.Icc 2 (N-1),weight K t d*actualAppellEnergy mu g d) ≤ C*(∫ x,(g x)^2 ∂mu)) :
    2*(∑ d ∈ Finset.Icc 3 N,weight K t d*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellProperRemainder mu f d))+
      (∑ b ∈ Finset.Icc 2 N,PositiveEnergyWeightedDrift.kappa K young t lambda2 b*weight K t b*
        actualCanonicalContractionSquare mu f 2 (b-1))+
      (∑ d ∈ Finset.Icc 3 N,tripleCharge mu f K young t lambda3 d) ≤ 
      (∑ d ∈ Finset.Icc 3 N,selectedFirstCost young t (twoRowsProfile theta2 theta3) (twoRowsLambda lambda2 lambda3) d*
        weight K t d*actualAppellEnergy mu f d)+
      (∑ b ∈ Finset.Icc 2 N,(K*C/young b)*(b : ℝ)^2*weight K t b*actualAppellEnergy mu f b)+
      2*(∑ d ∈ Finset.Icc 3 N,(theta2 d*weight K t d*
        (actualAppellCoefficient mu f d ⬝ᵥ actualAppellPairContractionSum mu f d)+
        theta3 d*weight K t d*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellProperTripleContractionSum mu f d))) := by
  have hcap:∀ a b,2 ≤ a → 2 ≤ b → twoRowsLambda lambda2 lambda3 a b ≤ 1 := by
    intro a b ha hb
    unfold twoRowsLambda
    split_ifs
    · exact hl2 b hb
    · exact (hl3 b hb).le
    · norm_num
  have hbd:∀ d a,3 ≤ d → a∈Finset.Icc 2 (d-1) → 
      twoRowsLambda lambda2 lambda3 a (d-a+1)=1 → twoRowsProfile theta2 theta3 d a=0 := by
    intro d a hd ha he
    have hb2:2 ≤ d-a+1:=by have:=(Finset.mem_Icc.mp ha).2;omega
    by_cases h2:a=2
    · subst a
      have hs:d-2+1=d-1:=by omega
      have hs':d-1+1=d:=by omega
      simp only [twoRowsLambda,ite_true,hs] at he
      have hh:=hboundary (d-1) (by omega) he
      rw [hs'] at hh
      simp [twoRowsProfile,hh]
    · by_cases h3:a=3
      · subst a
        simp only [twoRowsLambda,show (3:ℕ)≠2 by omega,ite_false,ite_true] at he
        have hh:=hl3 (d-3+1) hb2
        rw [he] at hh
        linarith
      · simp [twoRowsLambda,h2,h3] at he
  have hh:=actual_selected_remainder_with_last_refund_le hmu hf hK young t
    (twoRowsProfile theta2 theta3) (twoRowsLambda lambda2 lambda3) hy ht
    (fun d a hd=>twoRowsProfile_nonneg theta2 theta3 hth2 hth3 d a hd) hcap hbd N hN hprevious
  have hchg:(∑ p ∈ coupledDriftPairs N,(twoRowsLambda lambda2 lambda3 p.2 (p.1-p.2+1)*K/young (p.1-p.2+1))*
      (normalizedQ mu f K t p.2 (p.1-p.2+1))^2)+
      (twoRowsLambda lambda2 lambda3 2 N*K/young N)*(normalizedQ mu f K t 2 N)^2=
      (∑ b ∈ Finset.Icc 2 N,PositiveEnergyWeightedDrift.kappa K young t lambda2 b*weight K t b*
        actualCanonicalContractionSquare mu f 2 (b-1))+
      ∑ d ∈ Finset.Icc 3 N,tripleCharge mu f K young t lambda3 d := by
    have htop:twoRowsLambda lambda2 lambda3 2 N=lambda2 N:=by simp [twoRowsLambda]
    rw [htop,two_rows_charge_sum_eq K young lambda2 lambda3 (normalizedQ mu f K t) N hN]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    exact pair_charge_eq mu f hK young t lambda2 ht b (Finset.mem_Icc.mp hb).1
  rw [add_assoc,hchg] at hh
  have he:(∑ d ∈ Finset.Icc 3 N,weight K t d*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellProperRemainder mu f d))=
      (∑ d ∈ Finset.Icc 3 N,weight K t d*(actualAppellCoefficient mu f d ⬝ᵥ
        actualProfileProperRemainder mu f (twoRowsProfile theta2 theta3) d))+
      (∑ d ∈ Finset.Icc 3 N,(theta2 d*weight K t d*
        (actualAppellCoefficient mu f d ⬝ᵥ actualAppellPairContractionSum mu f d)+
        theta3 d*weight K t d*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellProperTripleContractionSum mu f d))) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [actualAppellProperRemainder_two_rows_split mu f theta2 theta3 d (Finset.mem_Icc.mp hd).1]
    rw [dotProduct_add,dotProduct_add,dotProduct_smul,dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  rw [he]
  linarith

end KLSConstantImprovement.TriplePositiveEnergyWeightedCharges
#print axioms KLSConstantImprovement.TriplePositiveEnergyWeightedCharges.actual_two_rows_retained_le
