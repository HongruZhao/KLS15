import ActualSymmetricQuadraticWeightedGenerator
import ActualSymmetricCubicNoise

/-! Genuine weighted generator with the symmetric rank-two and rank-three
covariance-noise improvements. Higher degrees retain the previously proved generator, and the
proper drift and centered maximum are unchanged. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def appellSymmetricCubicGeneratorLoss (beta : ℕ → ℝ) (d : ℕ) : ℝ :=
  if d=3 then 44/(1-beta 3)-33 else appellSymmetricQuadraticGeneratorLoss beta d

theorem actual_symmetric_cubic_degree_young_generator_sum_lower
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {K C : ℝ} (hK : 0<K) (hC : 0≤C)
    (s : ℕ→ℝ) (hs : ∀ b,2≤b→0<s b)
    (N : ℕ) (beta : ℕ → ℝ)
    (hbeta0 : ∀ d∈Finset.Icc 2 N, 0≤beta d)
    (hbeta1 : ∀ d∈Finset.Icc 2 N, beta d<1)
    (hbeta2 : (1 : ℝ)/3≤beta 2)
    (hbeta3 : (1 : ℝ)/2≤beta 3)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x,(g x)^2 ∂μ))
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator μ f K N+
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1≤0) :
    (∑ d∈Finset.Icc 2 N,beta d*(K^d*(d.factorial : ℝ)^2)⁻¹*
      actualAppellEnergy μ f (d+1)) ≤
    (∑ d∈Finset.Icc 2 N,
      (appellSymmetricCubicGeneratorLoss beta d+(K*C/s d)*(d : ℝ)^2+
        1+properYoungPrefix s d)*
      (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) := by
  classical
  let w : ℕ → ℝ := fun d => (K^d*(d.factorial : ℝ)^2)⁻¹
  let R := ∑ d∈Finset.Icc 2 N,w d*
    (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)
  let T := ∑ d∈Finset.Icc 2 N,properYoungPrefix s d*w d*actualAppellEnergy μ f d
  let D := ∑ d∈Finset.Icc 2 N,(K*C/s d)*(d : ℝ)^2*w d*actualAppellEnergy μ f d
  let S := ∑ d∈Finset.Icc 2 N,beta d*w d*actualAppellEnergy μ f (d+1)
  let L := ∑ d∈Finset.Icc 2 N,
    appellSymmetricCubicGeneratorLoss beta d*w d*actualAppellEnergy μ f d
  have hw (d : ℕ) : 0≤w d := by
    exact inv_nonneg.mpr (mul_nonneg (pow_nonneg hK.le _) (sq_nonneg _))
  have hlower : S-L-2*R≤actualWeightedAppellHeatGenerator μ f K N := by
    have hdegree (d : ℕ) (hd : d∈Finset.Icc 2 N) :
        beta d*actualAppellEnergy μ f (d+1)-
          appellSymmetricCubicGeneratorLoss beta d*actualAppellEnergy μ f d-
          2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d) ≤
        actualAppellEnergyHeatGenerator μ f d := by
      by_cases hd3 : d=3
      · subst d
        simpa [appellSymmetricCubicGeneratorLoss] using
          actualCovarianceAppellEnergy_generator_lower_three_symmetric
            hμ (Lp.memLp f) hbeta3 (hbeta1 3 hd)
      · by_cases hd2 : d=2
        · subst d
          simpa [appellSymmetricCubicGeneratorLoss,appellSymmetricQuadraticGeneratorLoss] using
            actualCovarianceAppellEnergy_generator_lower_two_symmetric
              hμ (Lp.memLp f) hbeta2 (hbeta1 2 hd)
        · simpa only [appellSymmetricCubicGeneratorLoss,ite_eq_right hd3,
            appellSymmetricQuadraticGeneratorLoss,ite_eq_right hd2,
            appellGeneratorLoss,actualAppellEnergyHeatGenerator] using
            actualCovarianceAppellEnergy_generator_lower hμ (Lp.memLp f) d
              (hbeta0 d hd) (hbeta1 d hd)
    have hh := Finset.sum_le_sum (s:=Finset.Icc 2 N) (fun d hd =>
      mul_le_mul_of_nonneg_left (hdegree d hd) (hw d))
    change (∑ d∈Finset.Icc 2 N,w d*(beta d*actualAppellEnergy μ f (d+1)-
      appellSymmetricCubicGeneratorLoss beta d*actualAppellEnergy μ f d-
      2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)))≤
        actualWeightedAppellHeatGenerator μ f K N at hh
    have he : S-L-2*R =
        ∑ d∈Finset.Icc 2 N,w d*(beta d*actualAppellEnergy μ f (d+1)-
          appellSymmetricCubicGeneratorLoss beta d*actualAppellEnergy μ f d-
          2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)) := by
      dsimp only [S,L,R]
      rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    rwa [he]
  have hdrift := actual_weighted_centered_full_drift_degree_young_le hμ f hunit hK hC s hs N hprevious hstat
  have htri : (∑ d∈Finset.Icc 3 N,properYoungPrefix s d*
      (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)=T := by
    apply Finset.sum_subset (by intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega)
    intro d hd hn
    have hd2 : d=2 := by simp only [Finset.mem_Icc] at hd hn; omega
    subst d
    norm_num [properYoungPrefix]
  rw [htri] at hdrift
  change 2*R-actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1≤
    actualWeightedAppellEnergy μ f K N+T+D at hdrift
  have he : (∑ d∈Finset.Icc 2 N,
      (appellSymmetricCubicGeneratorLoss beta d+(K*C/s d)*(d : ℝ)^2+
        1+properYoungPrefix s d)*
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
  change S≤_
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_symmetric_cubic_degree_young_generator_sum_lower
