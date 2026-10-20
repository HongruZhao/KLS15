import ActualCubicJointGenerator
import ActualCubicExcludedHarmonicDrift

/-! Centered generator with the signed cubic proper drift completed in
the rank-two covariance noise. Its retained canonical square cancels
exactly; the previous joint budget for every higher row is unchanged. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def jointCubicGeneratorLoss (K s : ℝ) (beta : ℕ → ℝ) (d : ℕ) : ℝ :=
  if d=2 then 64*(1+1/(6*K))^2/(3*(1-beta 2))-18-8/(K*s)
  else appellGeneralResidualGeneratorLoss beta d

def jointCubicHeadCoefficient (K s : ℝ) (beta cost : ℕ → ℝ) : ℝ :=
  64*(1+1/(6*K))^2/(3*(1-beta 2))-17-8/(K*s)+cost 2

def jointCubicTailCoefficient (K : ℝ) (beta cost : ℕ → ℝ) (d : ℕ) : ℝ :=
  K*beta (d-1)*(d : ℝ)^2-appellGeneralResidualGeneratorLoss beta d-1-cost d

 theorem actual_centered_drift_excluding_cubic_of_proper_cost
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {K : ℝ} (hK : 0 < K)
    (s : ℝ) (cost : ℕ → ℝ) (N : ℕ) (hN : 3 ≤ N)
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hproper : 2*(∑ d ∈ Finset.Icc 4 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d))+
      (K/s)*(coupledAppellQ μ f K 2 2)^2 ≤
      ∑ d ∈ Finset.Icc 2 N, cost d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) :
    2*(∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d))-
      2*(K^3*(Nat.factorial 3 : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)+
      (K/s)*(coupledAppellQ μ f K 2 2)^2-
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤
    actualWeightedAppellEnergy μ f K N+
      ∑ d ∈ Finset.Icc 2 N, cost d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
  classical
  have hi : Finset.Icc 3 N=insert 3 (Finset.Icc 4 N) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hn : 3 ∉ Finset.Icc 4 N := by simp
  have hproper' :
      2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d))-
        2*(K^3*(Nat.factorial 3 : ℝ)^2)⁻¹*
          (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)+
        (K/s)*(coupledAppellQ μ f K 2 2)^2 ≤
      ∑ d ∈ Finset.Icc 2 N, cost d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
    rw [hi,Finset.sum_insert hn]
    linarith [hproper]
  rw [actual_weighted_proper_drift_sum_eq f K N] at hproper'
  have ht := actual_weighted_terminal_eq hμ f K N hstat
  have hb : actualAppellEnergy μ f 1 ≤ 1 := by
    rw [actualAppellEnergy_eq_norm_sq]
    simpa only [hunit,one_pow] using fullClassAppellTensor_one_norm_sq_le hμ.logConcave hμ.isotropic f
  have hM := actualWeightedAppellEnergy_nonneg μ f hK N
  have hMb := mul_le_of_le_one_right hM hb
  have he : (∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)) =
      (∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellCoefficient μ
          (fun x => inner ℝ x (affineProjectionVector hμ.isotropic f)) d))+
      ∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f
      (Finset.mem_Icc.mp hd).1,dotProduct_add]
    ring
  rw [he]
  linarith

 theorem actual_centered_joint_cubic_generator_sum_lower
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {K : ℝ} (hK : 0 < K)
    (s : ℝ) (cost : ℕ → ℝ) (N : ℕ) (hN : 3 ≤ N) (beta : ℕ → ℝ)
    (hbeta0 : ∀ d ∈ Finset.Icc 2 N, 0 ≤ beta d)
    (hbeta1 : ∀ d ∈ Finset.Icc 2 N, beta d < 1)
    (hbeta2 : (1 : ℝ)/3 ≤ beta 2) (hbeta3 : (1 : ℝ)/2 ≤ beta 3)
    (hbetalow : ∀ d, 4 ≤ d → d ≤ 24 → beta d ≤ ((d : ℝ)-1)/((d : ℝ)+1))
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
      ∑ d ∈ Finset.Icc 2 N, (jointCubicGeneratorLoss K s beta d+1+cost d)*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
  classical
  let w : ℕ → ℝ := fun d => (K^d*(d.factorial : ℝ)^2)⁻¹
  let R := ∑ d ∈ Finset.Icc 2 N, w d*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)
  let D := ∑ d ∈ Finset.Icc 2 N, cost d*w d*actualAppellEnergy μ f d
  let S := ∑ d ∈ Finset.Icc 2 N, beta d*w d*actualAppellEnergy μ f (d+1)
  let L := ∑ d ∈ Finset.Icc 2 N, jointCubicGeneratorLoss K s beta d*w d*actualAppellEnergy μ f d
  let cubic := 2*w 3*(actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)
  let credit := (K/s)*(coupledAppellQ μ f K 2 2)^2
  have h2mem : 2 ∈ Finset.Icc 2 N := by simp only [Finset.mem_Icc]; omega
  have hcell (d : ℕ) (hd : d ∈ Finset.Icc 2 N) :
      w d*(beta d*actualAppellEnergy μ f (d+1)-
        jointCubicGeneratorLoss K s beta d*actualAppellEnergy μ f d-
        2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d))+
        (if d=2 then cubic-credit else 0) ≤ w d*actualAppellEnergyHeatGenerator μ f d := by
    by_cases hd2 : d=2
    · subst d
      have hh := actual_weighted_generator_two_joint_proper_three_lower (θ:=1) (lmb:=1)
        hμ (Lp.memLp f) hK (hbeta1 2 h2mem) (by simpa using hQcoeff) (by simpa using hRcoeff)
      simp only [jointCubicGeneratorLoss,ite_true,Nat.reduceAdd,one_mul,mul_one] at hh ⊢
      change _ ≤ KLSBelow25.CoupledEnergy.factorialWeight K 2*actualAppellEnergyHeatGenerator μ f 2
      dsimp only [w,cubic,credit]
      simp only [KLSBelow25.CoupledEnergy.factorialWeight] at hh ⊢
      linarith
    · have hh := mul_le_mul_of_nonneg_left
        (actual_general_residual_degree_generator_lower hμ (Lp.memLp f) beta d
          (Finset.mem_Icc.mp hd).1 (hbeta0 d hd) (hbeta1 d hd) hbeta2 hbeta3 hbetalow)
        (show 0 ≤ w d by dsimp only [w]; positivity)
      simpa only [jointCubicGeneratorLoss,hd2,ite_false,add_zero] using hh
  have hsum := Finset.sum_le_sum hcell
  have he : S-L-2*R+cubic-credit = ∑ d ∈ Finset.Icc 2 N,
      (w d*(beta d*actualAppellEnergy μ f (d+1)-
        jointCubicGeneratorLoss K s beta d*actualAppellEnergy μ f d-
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
  have hr : (∑ d ∈ Finset.Icc 2 N, (jointCubicGeneratorLoss K s beta d+1+cost d)*
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

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_centered_drift_excluding_cubic_of_proper_cost
#print axioms KLS.DeterministicBridgeNext.actual_centered_joint_cubic_generator_sum_lower
