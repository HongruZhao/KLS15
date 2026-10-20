import VariableCoefficientBarrier

/-! One genuine all-law Appell induction step. The maximizer, every actual
variation, terminal estimate and excess contradiction are constructed or
proved internally. Only previous lower-degree coefficient estimates and
proved scalar barrier data are used. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

 theorem actual_variable_coefficient_induction_step {n k : ℕ}
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n)))
    (hk : 2 ≤ k) {h : ℕ → ℝ}
    (hh : ∀ r : ℕ, 1 ≤ r → r ≤ k+1 → 0 < h r)
    (hprevious : ∀ r : ℕ, 1 ≤ r → r ≤ k → ∀ (μ : Measure (Space n)), admissibleMeasure μ →
      ∀ f : Space n → ℝ, MemLp f 2 μ → actualAppellEnergy μ f r ≤ h r*(∫ x, (f x)^2 ∂μ))
    (b : VariableCoefficientInductionBarrier k h) :
    ∀ (μ : Measure (Space n)), admissibleMeasure μ → ∀ f : Space n → ℝ,
      MemLp f 2 μ → actualAppellEnergy μ f (k+1) ≤ h (k+1)*(∫ x, (f x)^2 ∂μ) := by
  have hhk := hh k (by omega) (by omega)
  have hhj := hh (k+1) (by omega) le_rfl
  have hprevk := hprevious k (by omega) le_rfl
  obtain ⟨μ,hμ,c,hunit,hmax,hstat,henergy⟩ := exists_actual_joint_maximizer_energy_inequality
    hμ₀ hhk b.continuous b.positive b.antitone b.concave b.hasDeriv hprevk
  let p := boundedDegreePolynomial c
  let f : Lp ℝ 2 (μ : Measure (Space n)) := polynomialLp hμ.logConcave p
  have hpoly : (f : Space n → ℝ) =ᵐ[(μ : Measure (Space n))] polynomialEval p :=
    polynomialLp_coe hμ.logConcave p
  have hfunit : ‖f‖=1 := hunit
  have hfne : f ≠ 0 := by
    intro hfz
    rw [hfz,norm_zero] at hfunit
    norm_num at hfunit
  let X := actualAppellEnergy (μ : Measure (Space n)) f (k+1)
  let Y := actualAppellEnergy (μ : Measure (Space n)) f k
  let u := Y/(h k)
  let q := -deriv b.phi u/b.phi u
  have hu : u ∈ Icc (0 : ℝ) 1 := by
    have hu' := actualAppell_ratio_mem_Icc hμ hhk hprevk f hfne
    rw [hfunit,one_pow,mul_one,← actualAppellEnergy_eq_norm_sq] at hu'
    exact hu'
  have hq : 0 < q := b.q_positive hu
  have hE (d : ℕ) : actualCovarianceAppellEnergy (μ : Measure (Space n)) (polynomialEval p) d =
      actualAppellEnergy (μ : Measure (Space n)) f d := by
    rw [actualCovarianceAppellEnergy_isotropic hμ.isotropic]
    exact actualAppellEnergy_congr_ae hpoly.symm
  have hG (d : ℕ) : actualAppellEnergyHeatGenerator (μ : Measure (Space n)) (polynomialEval p) d =
      actualAppellEnergyHeatGenerator (μ : Measure (Space n)) f d :=
    actualAppellEnergyHeatGenerator_congr_ae hpoly.symm d
  have hmaximum : actualAppellEnergyHeatGenerator (μ : Measure (Space n)) f (k+1)+
      X*q/(h k)*actualAppellEnergyHeatGenerator (μ : Measure (Space n)) f k ≤ 0 := by
    change actualAppellEnergyHeatGenerator (μ : Measure (Space n)) (polynomialEval p) (k+1)+
      actualCovarianceAppellEnergy (μ : Measure (Space n)) (polynomialEval p) (k+1)*
      (-deriv b.phi (actualCovarianceAppellEnergy (μ : Measure (Space n)) (polynomialEval p) k/(h k))/
        b.phi (actualCovarianceAppellEnergy (μ : Measure (Space n)) (polynomialEval p) k/(h k)))/(h k)*
      actualAppellEnergyHeatGenerator (μ : Measure (Space n)) (polynomialEval p) k ≤ 0 at henergy
    rw [hE (k+1),hE k,hG (k+1),hG k] at henergy
    exact henergy
  have hstat' : ∀ ell : Lp ℝ 2 (μ : Measure (Space n)),
      inner ℝ (fullClassAppellTensor (k+1) f) (fullClassAppellTensor (k+1) ell)+
      X*q/(h k)*inner ℝ (fullClassAppellTensor k f) (fullClassAppellTensor k ell) =
      X*(1+u*q)*inner ℝ f ell := by
    intro ell
    have hs := hstat ell
    simp only [← actualAppellEnergy_eq_norm_sq] at hs
    exact hs
  have ht := actualAppell_weighted_energy_inequality hμ f hfunit hk hhk
    (fun r hr hrk => (hh r hr (by omega)).le)
    (fun r hr hrk => hprevious r hr hrk (μ : Measure (Space n)) hμ)
    (b.alpha_unit u hu).1.le (b.alpha_unit u hu).2 hq.le hstat' hmaximum
  have hbound : X ≤ h (k+1)*b.phi u := by
    by_contra hn
    have hex : h (k+1)*b.phi u < X := lt_of_not_ge hn
    have hY : Y = h k*u := by dsimp [u]; field_simp [hhk.ne']
    have hcrit := b.criterion u hu
    exact weighted_terminal_excess_contradiction hhk hhj (b.positive u hu)
      (b.alpha_unit u hu).1 hq (actualLowerConvolution_nonneg h (k+1)) hex hY hcrit
      (by simpa only [Nat.cast_add,Nat.cast_one] using ht)
  have hmaxbound : coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
      (fullClassAppellLinearMap hμ.logConcave (k+1)) (h k) b.phi f ≤ h (k+1) := by
    change ‖fullClassAppellTensor (k+1) f‖^2/
      (‖f‖^2*b.phi (‖fullClassAppellTensor k f‖^2/(h k*‖f‖^2))) ≤ _
    rw [hfunit,one_pow,one_mul,mul_one,← actualAppellEnergy_eq_norm_sq,
      ← actualAppellEnergy_eq_norm_sq]
    exact (div_le_iff₀ (b.positive u hu)).mpr hbound
  apply actual_energy_bound_of_all_quotients_le hhk hhj.le b.positive b.antitone b.zero.le hprevk
  intro ν hν g
  exact (hmax ν hν g).trans hmaxbound

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_variable_coefficient_induction_step
