import ActualGeneralResidualWeightedGenerator
import ActualSymmetricQuadraticGeneratorCoefficients

/-! Exact finite-degree coefficient inequality for the genuine centered
weighted maximum, with the symmetric rank-two, rank-three, and rank-four noise estimates. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def generalResidualTailCoefficient (K C : ℝ) (beta s : ℕ → ℝ) (d : ℕ) : ℝ :=
  K*beta (d-1)*(d : ℝ)^2-appellGeneralResidualGeneratorLoss beta d-
    (K*C/s d)*(d : ℝ)^2-1-properYoungPrefix s d

theorem actual_general_residual_generator_coefficients_nonpos
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {K C : ℝ} (hK : 0<K) (hC : 0≤C)
    (s : ℕ → ℝ) (hs : ∀ d,2≤d→0<s d)
    (beta : ℕ → ℝ) (hbeta0 : ∀ d,2≤d→0≤beta d)
    (hbeta1 : ∀ d,2≤d→beta d<1) (hbeta2 : (1 : ℝ)/3≤beta 2)
    (hbeta3 : (1 : ℝ)/2≤beta 3)
    (hbetalow : ∀ d,4≤d→d≤24→beta d≤((d : ℝ)-1)/((d : ℝ)+1))
    (N : ℕ) (hN : 2≤N)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x,(g x)^2 ∂μ))
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator μ f K N+
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1≤0) :
    (∑ d∈Finset.Icc 3 N,generalResidualTailCoefficient K C beta s d*
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d))-
      symmetricQuadraticHeadCoefficient K C beta s*
        ((K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2)≤0 := by
  classical
  have hlower := actual_general_residual_degree_young_generator_sum_lower
    hμ f hunit hK hC s hs N beta
    (fun d hd => hbeta0 d (Finset.mem_Icc.mp hd).1)
    (fun d hd => hbeta1 d (Finset.mem_Icc.mp hd).1) hbeta2 hbeta3 hbetalow hprevious hstat hheat
  have hshift := CoupledEnergy.variable_factorial_weight_energy_shift
    (fun d => actualAppellEnergy μ f d) beta hK hbeta0
    (fun d => actualAppellEnergy_nonneg _ _ _) N hN
  simp only [CoupledEnergy.factorialWeight] at hshift
  have hsum := hshift.trans hlower
  have hset : Finset.Icc 2 N=insert 2 (Finset.Icc 3 N) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hnot : 2∉Finset.Icc 3 N := by simp
  have he : (∑ d∈Finset.Icc 3 N,generalResidualTailCoefficient K C beta s d*
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d))-
      symmetricQuadraticHeadCoefficient K C beta s*
        ((K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2) =
      (∑ d∈Finset.Icc 3 N,K*beta (d-1)*(d : ℝ)^2*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)-
      (∑ d∈Finset.Icc 2 N,
        (appellGeneralResidualGeneratorLoss beta d+(K*C/s d)*(d : ℝ)^2+
          1+properYoungPrefix s d)*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) := by
    rw [hset,Finset.sum_insert hnot]
    have htail : (∑ d∈Finset.Icc 3 N,generalResidualTailCoefficient K C beta s d*
        ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)) =
        (∑ d∈Finset.Icc 3 N,K*beta (d-1)*(d : ℝ)^2*
          (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)-
        (∑ d∈Finset.Icc 3 N,
          (appellGeneralResidualGeneratorLoss beta d+(K*C/s d)*(d : ℝ)^2+
            1+properYoungPrefix s d)*
          (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      simp only [generalResidualTailCoefficient]
      ring
    rw [htail]
    have hp2 : properYoungPrefix s 2=0 := by norm_num [properYoungPrefix]
    have hl2 : appellGeneralResidualGeneratorLoss beta 2=64/(3*(1-beta 2))-18 := by
      simp [appellGeneralResidualGeneratorLoss,appellSymmetricCubicGeneratorLoss,appellSymmetricQuadraticGeneratorLoss]
    rw [hp2,hl2]
    unfold symmetricQuadraticHeadCoefficient
    norm_num only [Nat.cast_ofNat]
    ring
  rw [he]
  exact sub_nonpos.mpr hsum

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_general_residual_generator_coefficients_nonpos
