import ActualThetaGeneralResidualGenerator

/-! The unchanged genuine centered generator with an explicitly proved
proper-drift cost. This is an assembly lemma, not a new numerical endpoint. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def centeredDriftTailCoefficient (K : ℝ) (beta cost : ℕ → ℝ) (d : ℕ) : ℝ :=
  K*beta (d-1)*(d : ℝ)^2-appellGeneralResidualGeneratorLoss beta d-1-cost d

def centeredDriftHeadCoefficient (beta cost : ℕ → ℝ) : ℝ :=
  64/(3*(1-beta 2))-17+cost 2

theorem actual_weighted_centered_full_drift_of_proper_cost
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {K : ℝ} (hK : 0 < K)
    (cost : ℕ → ℝ) (N : ℕ)
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N =
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hproper : 2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) ≤
      ∑ d ∈ Finset.Icc 2 N, cost d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) :
    2*(∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)) -
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤
      actualWeightedAppellEnergy μ f K N+
      ∑ d ∈ Finset.Icc 2 N, cost d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
  have ht := actual_weighted_terminal_eq hμ f K N hstat
  have hb : actualAppellEnergy μ f 1 ≤ 1 := by
    rw [actualAppellEnergy_eq_norm_sq]
    simpa only [hunit,one_pow] using fullClassAppellTensor_one_norm_sq_le hμ.logConcave hμ.isotropic f
  have hM := actualWeightedAppellEnergy_nonneg μ f hK N
  have hMb := mul_le_of_le_one_right hM hb
  rw [actual_weighted_proper_drift_sum_eq f K N] at hproper
  have he : (∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)) =
      (∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellCoefficient μ
          (fun x => inner ℝ x (affineProjectionVector hμ.isotropic f)) d)) +
      ∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f
      (Finset.mem_Icc.mp hd).1,dotProduct_add]
    ring
  rw [he]
  linarith

theorem actual_centered_generator_sum_lower_of_proper_cost
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {K : ℝ} (hK : 0 < K)
    (cost : ℕ → ℝ) (N : ℕ) (beta : ℕ → ℝ)
    (hbeta0 : ∀ d ∈ Finset.Icc 2 N, 0 ≤ beta d)
    (hbeta1 : ∀ d ∈ Finset.Icc 2 N, beta d < 1)
    (hbeta2 : (1 : ℝ)/3 ≤ beta 2) (hbeta3 : (1 : ℝ)/2 ≤ beta 3)
    (hbetalow : ∀ d, 4 ≤ d → d ≤ 24 → beta d ≤ ((d : ℝ)-1)/((d : ℝ)+1))
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N =
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator μ f K N+
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤ 0)
    (hproper : 2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) ≤
      ∑ d ∈ Finset.Icc 2 N, cost d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) :
    (∑ d ∈ Finset.Icc 2 N, beta d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d+1)) ≤
      ∑ d ∈ Finset.Icc 2 N, (appellGeneralResidualGeneratorLoss beta d+1+cost d)*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
  classical
  let w : ℕ → ℝ := fun d => (K^d*(d.factorial : ℝ)^2)⁻¹
  let R := ∑ d ∈ Finset.Icc 2 N, w d*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)
  let D := ∑ d ∈ Finset.Icc 2 N, cost d*w d*actualAppellEnergy μ f d
  let S := ∑ d ∈ Finset.Icc 2 N, beta d*w d*actualAppellEnergy μ f (d+1)
  let L := ∑ d ∈ Finset.Icc 2 N, appellGeneralResidualGeneratorLoss beta d*w d*actualAppellEnergy μ f d
  have hlower : S-L-2*R ≤ actualWeightedAppellHeatGenerator μ f K N := by
    have hh := Finset.sum_le_sum (s := Finset.Icc 2 N) (fun d hd => mul_le_mul_of_nonneg_left
      (actual_general_residual_degree_generator_lower hμ (Lp.memLp f) beta d
        (Finset.mem_Icc.mp hd).1 (hbeta0 d hd) (hbeta1 d hd) hbeta2 hbeta3 hbetalow)
      (show 0 ≤ w d by dsimp only [w]; positivity))
    change (∑ d ∈ Finset.Icc 2 N, w d*(beta d*actualAppellEnergy μ f (d+1)-
      appellGeneralResidualGeneratorLoss beta d*actualAppellEnergy μ f d-
      2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d))) ≤
        actualWeightedAppellHeatGenerator μ f K N at hh
    have he : S-L-2*R = ∑ d ∈ Finset.Icc 2 N, w d*(beta d*actualAppellEnergy μ f (d+1)-
        appellGeneralResidualGeneratorLoss beta d*actualAppellEnergy μ f d-
        2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)) := by
      dsimp only [S,L,R]
      rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    rwa [he]
  have hdrift := actual_weighted_centered_full_drift_of_proper_cost hμ f hunit hK cost N hstat hproper
  change 2*R-actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤
    actualWeightedAppellEnergy μ f K N+D at hdrift
  have he : (∑ d ∈ Finset.Icc 2 N, (appellGeneralResidualGeneratorLoss beta d+1+cost d)*
      (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) = L+actualWeightedAppellEnergy μ f K N+D := by
    dsimp only [L,D,w]
    unfold actualWeightedAppellEnergy
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [he]
  change S ≤ _
  linarith

theorem actual_centered_generator_coefficients_nonpos_of_proper_cost
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖ = 1) {K : ℝ} (hK : 0 < K)
    (cost : ℕ → ℝ)
    (beta : ℕ → ℝ) (hbeta0 : ∀ d, 2 ≤ d → 0 ≤ beta d)
    (hbeta1 : ∀ d, 2 ≤ d → beta d < 1)
    (hbeta2 : (1 : ℝ)/3 ≤ beta 2) (hbeta3 : (1 : ℝ)/2 ≤ beta 3)
    (hbetalow : ∀ d, 4 ≤ d → d ≤ 24 → beta d ≤ ((d : ℝ)-1)/((d : ℝ)+1))
    (N : ℕ) (hN : 2 ≤ N)
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N =
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator μ f K N +
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤ 0)
    (hproper : 2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) ≤
      ∑ d ∈ Finset.Icc 2 N, cost d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) :
    (∑ d ∈ Finset.Icc 3 N, centeredDriftTailCoefficient K beta cost d *
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)) -
      centeredDriftHeadCoefficient beta cost *
        ((K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2) ≤ 0 := by
  classical
  have hlower := actual_centered_generator_sum_lower_of_proper_cost hμ f hunit hK cost N beta
    (fun d hd => hbeta0 d (Finset.mem_Icc.mp hd).1)
    (fun d hd => hbeta1 d (Finset.mem_Icc.mp hd).1) hbeta2 hbeta3 hbetalow hstat hheat hproper
  have hshift := CoupledEnergy.variable_factorial_weight_energy_shift
    (fun d => actualAppellEnergy μ f d) beta hK hbeta0
    (fun d => actualAppellEnergy_nonneg _ _ _) N hN
  simp only [CoupledEnergy.factorialWeight] at hshift
  have hsum := hshift.trans hlower
  have hset : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hnot : 2 ∉ Finset.Icc 3 N := by simp
  have he : (∑ d ∈ Finset.Icc 3 N, centeredDriftTailCoefficient K beta cost d *
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)) -
      centeredDriftHeadCoefficient beta cost *
        ((K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2) =
      (∑ d ∈ Finset.Icc 3 N, K*beta (d-1)*(d : ℝ)^2 *
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) -
      ∑ d ∈ Finset.Icc 2 N,
        (appellGeneralResidualGeneratorLoss beta d+1+cost d) *
          (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
    rw [hset,Finset.sum_insert hnot]
    have htail : (∑ d ∈ Finset.Icc 3 N, centeredDriftTailCoefficient K beta cost d *
        ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)) =
        (∑ d ∈ Finset.Icc 3 N, K*beta (d-1)*(d : ℝ)^2 *
          (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) -
        ∑ d ∈ Finset.Icc 3 N,
          (appellGeneralResidualGeneratorLoss beta d+1+cost d) *
            (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      unfold centeredDriftTailCoefficient
      ring
    rw [htail]
    have hl2 : appellGeneralResidualGeneratorLoss beta 2 = 64/(3*(1-beta 2))-18 := by
      simp [appellGeneralResidualGeneratorLoss,appellSymmetricCubicGeneratorLoss,
        appellSymmetricQuadraticGeneratorLoss]
    rw [hl2]
    unfold centeredDriftHeadCoefficient
    norm_num only [Nat.cast_ofNat]
    ring
  rw [he]
  exact sub_nonpos.mpr hsum

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_centered_generator_sum_lower_of_proper_cost

#print axioms KLS.DeterministicBridgeNext.actual_centered_generator_coefficients_nonpos_of_proper_cost
