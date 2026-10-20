import ActualGeneralResidualGeneratorCoefficients
import ActualThetaCenteredAppellDrift

/-! Genuine centered weighted generator with the size-two neighbor
refinement.  Every covariance-noise estimate is the actual already-proved
one; the shared preceding joint Appell budget remains unchanged. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def thetaGeneralResidualTailCoefficient (K C : ℝ) (beta s theta eta : ℕ → ℝ)
    (d : ℕ) : ℝ :=
  K*beta (d-1)*(d : ℝ)^2-appellGeneralResidualGeneratorLoss beta d-
    (K*C/s d)*(d : ℝ)^2-1-thetaFirstCost s theta eta d-thetaNeighborCharge K s theta eta d

def thetaSymmetricQuadraticHeadCoefficient (K C : ℝ) (beta s theta eta : ℕ → ℝ) : ℝ :=
  symmetricQuadraticHeadCoefficient K C beta s + thetaNeighborCharge K s theta eta 2

theorem actual_general_residual_degree_generator_lower
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (beta : ℕ → ℝ) (d : ℕ) (hd : 2 ≤ d)
    (hbeta0 : 0 ≤ beta d) (hbeta1 : beta d < 1)
    (hbeta2 : (1 : ℝ)/3 ≤ beta 2) (hbeta3 : (1 : ℝ)/2 ≤ beta 3)
    (hbetalow : ∀ j, 4 ≤ j → j ≤ 24 → beta j ≤ ((j : ℝ)-1)/((j : ℝ)+1)) :
    beta d*actualAppellEnergy μ f (d+1)-
      appellGeneralResidualGeneratorLoss beta d*actualAppellEnergy μ f d-
      2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d) ≤
      actualAppellEnergyHeatGenerator μ f d := by
  by_cases hdnew : 4 ≤ d ∧ d ≤ 24
  · simpa only [appellGeneralResidualGeneratorLoss,ite_eq_left hdnew] using
      actualCovarianceAppellEnergy_generator_lower_general_residual hμ hf d
        (by omega : 3 ≤ d) hbeta0 (hbetalow d hdnew.1 hdnew.2)
  · by_cases hd3 : d = 3
    · subst d
      simpa [appellGeneralResidualGeneratorLoss,hdnew,appellSymmetricCubicGeneratorLoss] using
        actualCovarianceAppellEnergy_generator_lower_three_symmetric hμ hf hbeta3 hbeta1
    · by_cases hd2 : d = 2
      · subst d
        simpa [appellGeneralResidualGeneratorLoss,hdnew,appellSymmetricCubicGeneratorLoss,
          appellSymmetricQuadraticGeneratorLoss] using
          actualCovarianceAppellEnergy_generator_lower_two_symmetric hμ hf hbeta2 hbeta1
      · simpa only [appellGeneralResidualGeneratorLoss,ite_eq_right hdnew,
          appellSymmetricCubicGeneratorLoss,ite_eq_right hd3,
          appellSymmetricQuadraticGeneratorLoss,ite_eq_right hd2,
          appellGeneratorLoss,actualAppellEnergyHeatGenerator] using
          actualCovarianceAppellEnergy_generator_lower hμ hf d hbeta0 hbeta1

theorem actual_theta_general_residual_generator_sum_lower
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖ = 1) {K C : ℝ} (hK : 0 < K)
    (s theta eta : ℕ → ℝ) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (htheta0 : ∀ d, 3 ≤ d → 0 ≤ theta d)
    (htheta1 : ∀ d, 3 ≤ d → theta d ≤ 1)
    (heta : ∀ d, 3 ≤ d → 0 < eta d)
    (N : ℕ) (beta : ℕ → ℝ)
    (hbeta0 : ∀ d ∈ Finset.Icc 2 N, 0 ≤ beta d)
    (hbeta1 : ∀ d ∈ Finset.Icc 2 N, beta d < 1)
    (hbeta2 : (1 : ℝ)/3 ≤ beta 2) (hbeta3 : (1 : ℝ)/2 ≤ beta 3)
    (hbetalow : ∀ d, 4 ≤ d → d ≤ 24 → beta d ≤ ((d : ℝ)-1)/((d : ℝ)+1))
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ))
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N =
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator μ f K N +
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤ 0) :
    (∑ d ∈ Finset.Icc 2 N, beta d*(K^d*(d.factorial : ℝ)^2)⁻¹ *
      actualAppellEnergy μ f (d+1)) ≤
      ∑ d ∈ Finset.Icc 2 N,
        (appellGeneralResidualGeneratorLoss beta d+(K*C/s d)*(d : ℝ)^2+
          1+thetaFirstCost s theta eta d+thetaNeighborCharge K s theta eta d) *
          (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
  classical
  let w : ℕ → ℝ := fun d => (K^d*(d.factorial : ℝ)^2)⁻¹
  let R := ∑ d ∈ Finset.Icc 2 N, w d *
    (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)
  let T := ∑ d ∈ Finset.Icc 2 N, thetaFirstCost s theta eta d*w d*actualAppellEnergy μ f d
  let D := ∑ d ∈ Finset.Icc 2 N,
    ((K*C/s d)*(d : ℝ)^2+thetaNeighborCharge K s theta eta d)*w d*actualAppellEnergy μ f d
  let S := ∑ d ∈ Finset.Icc 2 N, beta d*w d*actualAppellEnergy μ f (d+1)
  let L := ∑ d ∈ Finset.Icc 2 N,
    appellGeneralResidualGeneratorLoss beta d*w d*actualAppellEnergy μ f d
  have hw (d : ℕ) : 0 ≤ w d := by
    exact inv_nonneg.mpr (mul_nonneg (pow_nonneg hK.le _) (sq_nonneg _))
  have hlower : S-L-2*R ≤ actualWeightedAppellHeatGenerator μ f K N := by
    have hh := Finset.sum_le_sum (s := Finset.Icc 2 N) (fun d hd =>
      mul_le_mul_of_nonneg_left
        (actual_general_residual_degree_generator_lower hμ (Lp.memLp f) beta d
          (Finset.mem_Icc.mp hd).1 (hbeta0 d hd) (hbeta1 d hd) hbeta2 hbeta3 hbetalow) (hw d))
    change (∑ d ∈ Finset.Icc 2 N, w d*(beta d*actualAppellEnergy μ f (d+1)-
      appellGeneralResidualGeneratorLoss beta d*actualAppellEnergy μ f d-
      2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d))) ≤
        actualWeightedAppellHeatGenerator μ f K N at hh
    have he : S-L-2*R =
        ∑ d ∈ Finset.Icc 2 N, w d*(beta d*actualAppellEnergy μ f (d+1)-
          appellGeneralResidualGeneratorLoss beta d*actualAppellEnergy μ f d-
          2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)) := by
      dsimp only [S,L,R]
      rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    rwa [he]
  have hdrift := actual_weighted_centered_full_drift_theta_young_le hμ f hunit
    s theta eta hK hs htheta0 htheta1 heta N hprevious hstat
  have htri : (∑ d ∈ Finset.Icc 3 N, thetaFirstCost s theta eta d *
      (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) = T := by
    apply Finset.sum_subset (by intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega)
    intro d hd hn
    have hd2 : d = 2 := by simp only [Finset.mem_Icc] at hd hn; omega
    subst d
    rw [thetaFirstCost_two,zero_mul,zero_mul]
  rw [htri] at hdrift
  change 2*R-actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤
    actualWeightedAppellEnergy μ f K N+T+D at hdrift
  have he : (∑ d ∈ Finset.Icc 2 N,
      (appellGeneralResidualGeneratorLoss beta d+(K*C/s d)*(d : ℝ)^2+
        1+thetaFirstCost s theta eta d+thetaNeighborCharge K s theta eta d) *
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) =
      L+D+actualWeightedAppellEnergy μ f K N+T := by
    dsimp only [L,D,T]
    unfold actualWeightedAppellEnergy
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp only [w]
    ring
  rw [he]
  change S ≤ _
  linarith

theorem actual_theta_general_residual_coefficients_nonpos
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖ = 1) {K C : ℝ} (hK : 0 < K)
    (s theta eta : ℕ → ℝ) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (htheta0 : ∀ d, 3 ≤ d → 0 ≤ theta d)
    (htheta1 : ∀ d, 3 ≤ d → theta d ≤ 1)
    (heta : ∀ d, 3 ≤ d → 0 < eta d)
    (beta : ℕ → ℝ) (hbeta0 : ∀ d, 2 ≤ d → 0 ≤ beta d)
    (hbeta1 : ∀ d, 2 ≤ d → beta d < 1)
    (hbeta2 : (1 : ℝ)/3 ≤ beta 2) (hbeta3 : (1 : ℝ)/2 ≤ beta 3)
    (hbetalow : ∀ d, 4 ≤ d → d ≤ 24 → beta d ≤ ((d : ℝ)-1)/((d : ℝ)+1))
    (N : ℕ) (hN : 2 ≤ N)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ))
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N =
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator μ f K N +
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤ 0) :
    (∑ d ∈ Finset.Icc 3 N, thetaGeneralResidualTailCoefficient K C beta s theta eta d *
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)) -
      thetaSymmetricQuadraticHeadCoefficient K C beta s theta eta *
        ((K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2) ≤ 0 := by
  classical
  have hlower := actual_theta_general_residual_generator_sum_lower hμ f hunit hK
    s theta eta hs htheta0 htheta1 heta N beta
    (fun d hd => hbeta0 d (Finset.mem_Icc.mp hd).1)
    (fun d hd => hbeta1 d (Finset.mem_Icc.mp hd).1) hbeta2 hbeta3 hbetalow hprevious hstat hheat
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
  have he : (∑ d ∈ Finset.Icc 3 N, thetaGeneralResidualTailCoefficient K C beta s theta eta d *
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)) -
      thetaSymmetricQuadraticHeadCoefficient K C beta s theta eta *
        ((K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2) =
      (∑ d ∈ Finset.Icc 3 N, K*beta (d-1)*(d : ℝ)^2 *
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) -
      ∑ d ∈ Finset.Icc 2 N,
        (appellGeneralResidualGeneratorLoss beta d+(K*C/s d)*(d : ℝ)^2+
          1+thetaFirstCost s theta eta d+thetaNeighborCharge K s theta eta d) *
          (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
    rw [hset,Finset.sum_insert hnot]
    have htail : (∑ d ∈ Finset.Icc 3 N, thetaGeneralResidualTailCoefficient K C beta s theta eta d *
        ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)) =
        (∑ d ∈ Finset.Icc 3 N, K*beta (d-1)*(d : ℝ)^2 *
          (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) -
        ∑ d ∈ Finset.Icc 3 N,
          (appellGeneralResidualGeneratorLoss beta d+(K*C/s d)*(d : ℝ)^2+
            1+thetaFirstCost s theta eta d+thetaNeighborCharge K s theta eta d) *
            (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      unfold thetaGeneralResidualTailCoefficient
      ring
    rw [htail,thetaFirstCost_two]
    have hl2 : appellGeneralResidualGeneratorLoss beta 2 = 64/(3*(1-beta 2))-18 := by
      simp [appellGeneralResidualGeneratorLoss,appellSymmetricCubicGeneratorLoss,
        appellSymmetricQuadraticGeneratorLoss]
    rw [hl2]
    unfold thetaSymmetricQuadraticHeadCoefficient symmetricQuadraticHeadCoefficient
    norm_num only [Nat.cast_ofNat]
    ring
  rw [he]
  exact sub_nonpos.mpr hsum

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_theta_general_residual_generator_sum_lower
#print axioms KLS.DeterministicBridgeNext.actual_theta_general_residual_coefficients_nonpos
