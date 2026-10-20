import ActualCubicJointCoefficients
import CoupledJointNoiseSeed239Numerics

/-! The genuine pair-projection residual bound is available at every degree.
This assembly retains it at all d >= 4, instead of cutting it off at 24.
All prior universal budget, signed cubic cancellation, and canonical-charge
hypotheses are unchanged. This is not by itself an improved endpoint. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLSConstantImprovement.AllRankResidualWeightedGenerator
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

def allRankResidualGeneratorLoss (beta : ℕ → ℝ) (d : ℕ) : ℝ :=
  if 4 ≤ d then generalResidualGeneratorLoss (beta d) d
  else appellGeneralResidualGeneratorLoss beta d

def allRankJointCubicGeneratorLoss (K s : ℝ) (beta : ℕ → ℝ) (d : ℕ) : ℝ :=
  if d=2 then 64*(1+1/(6*K))^2/(3*(1-beta 2))-18-8/(K*s)
  else allRankResidualGeneratorLoss beta d

def allRankJointCubicTailCoefficient (K : ℝ) (beta cost : ℕ → ℝ) (d : ℕ) : ℝ :=
  K*beta (d-1)*(d : ℝ)^2-allRankResidualGeneratorLoss beta d-1-cost d

theorem actual_all_rank_residual_degree_generator_lower
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (beta : ℕ → ℝ) (d : ℕ) (hd : 2 ≤ d)
    (hbeta0 : 0 ≤ beta d) (hbeta1 : beta d < 1)
    (hbeta2 : (1 : ℝ)/3 ≤ beta 2) (hbeta3 : (1 : ℝ)/2 ≤ beta 3)
    (hbetalow : ∀ j, 4 ≤ j → beta j ≤ ((j : ℝ)-1)/((j : ℝ)+1)) :
    beta d*actualAppellEnergy μ f (d+1)-
      allRankResidualGeneratorLoss beta d*actualAppellEnergy μ f d-
      2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d) ≤
      actualAppellEnergyHeatGenerator μ f d := by
  by_cases hnew : 4 ≤ d
  · simpa only [allRankResidualGeneratorLoss,ite_eq_left hnew] using
      actualCovarianceAppellEnergy_generator_lower_general_residual hμ hf d
        (by omega : 3 ≤ d) hbeta0 (hbetalow d hnew)
  · simpa only [allRankResidualGeneratorLoss,ite_eq_right hnew] using
      actual_general_residual_degree_generator_lower hμ hf beta d hd hbeta0 hbeta1
        hbeta2 hbeta3 (fun j hj _ => hbetalow j hj)

/-- The inherited profile meets the pair-projection threshold at every degree. -/
theorem seed239_alpha_le_three_fifths (d : ℕ) (hd : 4 ≤ d) :
    CoupledEnergy.NumericsJointNoiseSeed239.alpha d ≤ (3 : ℝ)/5 := by
  by_cases hs : d ≤ 34
  · interval_cases d <;> norm_num [CoupledEnergy.NumericsJointNoiseSeed239.alpha]
  · rw [CoupledEnergy.NumericsJointNoiseSeed239.alpha_eq_tail d (by omega)]
    norm_num

theorem seed239_alpha_le_all_low_threshold (d : ℕ) (hd : 4 ≤ d) :
    CoupledEnergy.NumericsJointNoiseSeed239.alpha d ≤ ((d : ℝ)-1)/((d : ℝ)+1) := by
  have hr : (4 : ℝ) ≤ d := by exact_mod_cast hd
  apply (seed239_alpha_le_three_fifths d hd).trans
  apply (le_div_iff₀ (by linarith : 0 < (d : ℝ)+1)).mpr
  nlinarith

/-- Exact universal loss saved in each degree beyond the old cutoff. -/
theorem all_rank_residual_loss_saved (beta : ℕ → ℝ) (d : ℕ) (hd : 25 ≤ d)
    (hbeta : beta d < 1) :
    allRankResidualGeneratorLoss beta d = appellGeneralResidualGeneratorLoss beta d-
      4*beta d*(d : ℝ)*((d : ℝ)+1)/(3*((d : ℝ)-1)*(1-beta d)) := by
  have h4 : 4 ≤ d := by omega
  have h24 : ¬ (4 ≤ d ∧ d ≤ 24) := by omega
  have h2 : d ≠ 2 := by omega
  have h3 : d ≠ 3 := by omega
  have hr : (25 : ℝ) ≤ d := by exact_mod_cast hd
  have hdm : (d : ℝ)-1 ≠ 0 := by linarith
  have hb : 1-beta d ≠ 0 := by linarith
  simp only [allRankResidualGeneratorLoss,ite_eq_left h4,
    appellGeneralResidualGeneratorLoss,ite_eq_right h24,
    appellSymmetricCubicGeneratorLoss,h3,ite_false,
    appellSymmetricQuadraticGeneratorLoss,h2,
    generalResidualGeneratorLoss,generalResidualA,appellGeneratorLoss]
  field_simp
  ring

 theorem actual_all_rank_centered_joint_cubic_generator_sum_lower
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {K : ℝ} (hK : 0 < K)
    (s : ℝ) (cost : ℕ → ℝ) (N : ℕ) (hN : 3 ≤ N) (beta : ℕ → ℝ)
    (hbeta0 : ∀ d ∈ Finset.Icc 2 N, 0 ≤ beta d)
    (hbeta1 : ∀ d ∈ Finset.Icc 2 N, beta d < 1)
    (hbeta2 : (1 : ℝ)/3 ≤ beta 2) (hbeta3 : (1 : ℝ)/2 ≤ beta 3)
    (hbetalow : ∀ d, 4 ≤ d → beta d ≤ ((d : ℝ)-1)/((d : ℝ)+1))
    (hQcoeff : 2+1/(K*s)-4*(1+1/(6*K))^2/(3*(1-beta 2)) ≤ 0)
    (hRcoeff : 1-8*(1+1/(6*K))^2/(3*(1-beta 2)) ≤ 0)
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator μ f K N+
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤ 0)
    (hproper : 2*(∑ d ∈ Finset.Icc 4 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d))+
      (K/s)*(coupledAppellQ μ f K 2 2)^2 ≤
      ∑ d ∈ Finset.Icc 2 N, cost d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) :
    (∑ d ∈ Finset.Icc 2 N, beta d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d+1)) ≤
      ∑ d ∈ Finset.Icc 2 N, (allRankJointCubicGeneratorLoss K s beta d+1+cost d)*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
  classical
  let w : ℕ → ℝ := fun d => (K^d*(d.factorial : ℝ)^2)⁻¹
  let R := ∑ d ∈ Finset.Icc 2 N, w d*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)
  let D := ∑ d ∈ Finset.Icc 2 N, cost d*w d*actualAppellEnergy μ f d
  let S := ∑ d ∈ Finset.Icc 2 N, beta d*w d*actualAppellEnergy μ f (d+1)
  let L := ∑ d ∈ Finset.Icc 2 N, allRankJointCubicGeneratorLoss K s beta d*w d*actualAppellEnergy μ f d
  let cubic := 2*w 3*(actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)
  let credit := (K/s)*(coupledAppellQ μ f K 2 2)^2
  have h2mem : 2 ∈ Finset.Icc 2 N := by simp only [Finset.mem_Icc]; omega
  have hcell (d : ℕ) (hd : d ∈ Finset.Icc 2 N) :
      w d*(beta d*actualAppellEnergy μ f (d+1)-
        allRankJointCubicGeneratorLoss K s beta d*actualAppellEnergy μ f d-
        2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d))+
        (if d=2 then cubic-credit else 0) ≤ w d*actualAppellEnergyHeatGenerator μ f d := by
    by_cases hd2 : d=2
    · subst d
      have hh := actual_weighted_generator_two_joint_proper_three_lower (θ:=1) (lmb:=1)
        hμ (Lp.memLp f) hK (hbeta1 2 h2mem) (by simpa using hQcoeff) (by simpa using hRcoeff)
      simp only [allRankJointCubicGeneratorLoss,ite_true,Nat.reduceAdd,one_mul,mul_one] at hh ⊢
      change _ ≤ KLSBelow25.CoupledEnergy.factorialWeight K 2*actualAppellEnergyHeatGenerator μ f 2
      dsimp only [w,cubic,credit]
      simp only [KLSBelow25.CoupledEnergy.factorialWeight] at hh ⊢
      linarith
    · have hh := mul_le_mul_of_nonneg_left
        (actual_all_rank_residual_degree_generator_lower hμ (Lp.memLp f) beta d
          (Finset.mem_Icc.mp hd).1 (hbeta0 d hd) (hbeta1 d hd) hbeta2 hbeta3 hbetalow)
        (show 0 ≤ w d by dsimp only [w]; positivity)
      simpa only [allRankJointCubicGeneratorLoss,hd2,ite_false,add_zero] using hh
  have hsum := Finset.sum_le_sum hcell
  have he : S-L-2*R+cubic-credit = ∑ d ∈ Finset.Icc 2 N,
      (w d*(beta d*actualAppellEnergy μ f (d+1)-
        allRankJointCubicGeneratorLoss K s beta d*actualAppellEnergy μ f d-
        2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d))+
        (if d=2 then cubic-credit else 0)) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',h2mem,ite_true]
    dsimp only [S,L,R]
    rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
    rw [add_sub_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hlower : S-L-2*R+cubic-credit ≤ actualWeightedAppellHeatGenerator μ f K N := by
    rw [he]
    exact hsum
  have hdrift := actual_centered_drift_excluding_cubic_of_proper_cost hμ f hunit hK s cost N hN hstat hproper
  change 2*R-cubic+credit-actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤
    actualWeightedAppellEnergy μ f K N+D at hdrift
  have hr : (∑ d ∈ Finset.Icc 2 N, (allRankJointCubicGeneratorLoss K s beta d+1+cost d)*
      (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) = L+actualWeightedAppellEnergy μ f K N+D := by
    dsimp only [L,D,w]
    unfold actualWeightedAppellEnergy
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hr]
  change S ≤ _
  linarith


 theorem actual_all_rank_centered_joint_cubic_generator_coefficients_nonpos
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {K : ℝ} (hK : 0 < K)
    (s : ℝ) (cost beta : ℕ → ℝ)
    (hbeta0 : ∀ d, 2 ≤ d → 0 ≤ beta d)
    (hbeta1 : ∀ d, 2 ≤ d → beta d < 1)
    (hbeta2 : (1 : ℝ)/3 ≤ beta 2) (hbeta3 : (1 : ℝ)/2 ≤ beta 3)
    (hbetalow : ∀ d, 4 ≤ d → beta d ≤ ((d : ℝ)-1)/((d : ℝ)+1))
    (hQcoeff : 2+1/(K*s)-4*(1+1/(6*K))^2/(3*(1-beta 2)) ≤ 0)
    (hRcoeff : 1-8*(1+1/(6*K))^2/(3*(1-beta 2)) ≤ 0)
    (N : ℕ) (hN : 3 ≤ N)
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator μ f K N+
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤ 0)
    (hproper : 2*(∑ d ∈ Finset.Icc 4 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d))+
      (K/s)*(coupledAppellQ μ f K 2 2)^2 ≤
      ∑ d ∈ Finset.Icc 2 N, cost d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) :
    (∑ d ∈ Finset.Icc 3 N, allRankJointCubicTailCoefficient K beta cost d*
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d))-
      jointCubicHeadCoefficient K s beta cost*
        ((K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2) ≤ 0 := by
  classical
  have hlower := actual_all_rank_centered_joint_cubic_generator_sum_lower hμ f hunit hK s cost N hN beta
    (fun d hd => hbeta0 d (Finset.mem_Icc.mp hd).1)
    (fun d hd => hbeta1 d (Finset.mem_Icc.mp hd).1) hbeta2 hbeta3 hbetalow hQcoeff hRcoeff
    hstat hheat hproper
  have hshift := CoupledEnergy.variable_factorial_weight_energy_shift
    (fun d => actualAppellEnergy μ f d) beta hK hbeta0
    (fun d => actualAppellEnergy_nonneg _ _ _) N (by omega)
  simp only [CoupledEnergy.factorialWeight] at hshift
  have hsum := hshift.trans hlower
  have hset : Finset.Icc 2 N=insert 2 (Finset.Icc 3 N) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hnot : 2 ∉ Finset.Icc 3 N := by simp
  have he : (∑ d ∈ Finset.Icc 3 N, allRankJointCubicTailCoefficient K beta cost d*
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d))-
      jointCubicHeadCoefficient K s beta cost*
        ((K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2) =
      (∑ d ∈ Finset.Icc 3 N, K*beta (d-1)*(d : ℝ)^2*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)-
      ∑ d ∈ Finset.Icc 2 N, (allRankJointCubicGeneratorLoss K s beta d+1+cost d)*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
    rw [hset,Finset.sum_insert hnot]
    have htail : (∑ d ∈ Finset.Icc 3 N, allRankJointCubicTailCoefficient K beta cost d*
        ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)) =
        (∑ d ∈ Finset.Icc 3 N, K*beta (d-1)*(d : ℝ)^2*
          (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)-
        ∑ d ∈ Finset.Icc 3 N, (allRankJointCubicGeneratorLoss K s beta d+1+cost d)*
          (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      have hd2 : d ≠ 2 := by have := (Finset.mem_Icc.mp hd).1; omega
      simp only [allRankJointCubicTailCoefficient,allRankJointCubicGeneratorLoss,hd2,ite_false]
      ring
    rw [htail]
    simp only [allRankJointCubicGeneratorLoss,ite_true,jointCubicHeadCoefficient]
    ring
  rw [he]
  exact sub_nonpos.mpr hsum

 theorem actual_all_rank_joint_cubic_harmonic_generator_coefficients_nonpos
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {K C : ℝ}
    (s zeta2 zeta3 : ℕ → ℝ) (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (hzeta2 : ∀ b, 2 ≤ b → 0 ≤ zeta2 b)
    (hcap2 : ∀ b, 2 ≤ b → 2*zeta2 b < (b : ℝ)*((b : ℝ)+1))
    (hzeta3 : ∀ b, 2 ≤ b → 0 ≤ zeta3 b)
    (hcap3 : ∀ (b : ℕ), 2 ≤ b → tripleHarmonicRatio (b : ℝ)*zeta3 b < 1)
    (beta : ℕ → ℝ) (hbeta0 : ∀ d, 2 ≤ d → 0 ≤ beta d)
    (hbeta1 : ∀ d, 2 ≤ d → beta d < 1)
    (hbeta2 : (1 : ℝ)/3 ≤ beta 2) (hbeta3 : (1 : ℝ)/2 ≤ beta 3)
    (hbetalow : ∀ d, 4 ≤ d → beta d ≤ ((d : ℝ)-1)/((d : ℝ)+1))
    (hQcoeff : 2+1/(K*s 2)-4*(1+1/(6*K))^2/(3*(1-beta 2)) ≤ 0)
    (hRcoeff : 1-8*(1+1/(6*K))^2/(3*(1-beta 2)) ≤ 0)
    (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x,(g x)^2 ∂μ))
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator μ f K N+
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤ 0) :
    (∑ d ∈ Finset.Icc 3 N, allRankJointCubicTailCoefficient K beta
      (cubicExcludedHarmonicCost K C s zeta2 zeta3) d*
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d))-
      jointCubicHeadCoefficient K (s 2) beta (cubicExcludedHarmonicCost K C s zeta2 zeta3)*
        ((K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2) ≤ 0 :=
  actual_all_rank_centered_joint_cubic_generator_coefficients_nonpos hμ f hunit hK (s 2)
    (cubicExcludedHarmonicCost K C s zeta2 zeta3) beta hbeta0 hbeta1 hbeta2 hbeta3 hbetalow
    hQcoeff hRcoeff N hN hstat hheat
    (actual_weighted_proper_drift_harmonic_excluding_cubic_le hμ (Lp.memLp f)
      s zeta2 zeta3 hK hs hzeta2 hcap2 hzeta3 hcap3 N hN hprevious)

end KLSConstantImprovement.AllRankResidualWeightedGenerator
#print axioms KLSConstantImprovement.AllRankResidualWeightedGenerator.actual_all_rank_residual_degree_generator_lower
#print axioms KLSConstantImprovement.AllRankResidualWeightedGenerator.seed239_alpha_le_all_low_threshold
#print axioms KLSConstantImprovement.AllRankResidualWeightedGenerator.all_rank_residual_loss_saved
#print axioms KLSConstantImprovement.AllRankResidualWeightedGenerator.actual_all_rank_joint_cubic_harmonic_generator_coefficients_nonpos
