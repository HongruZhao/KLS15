import CenteredVariableCoefficientBarrier

/-! The actual attained quotient controls the adjacent energies jointly.
This retains the proved barrier instead of discarding its shape at phi≤1. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

 theorem actual_centered_variable_coefficient_joint_unit_bound {n k : ℕ}
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n)))
    (hk : 2 ≤ k) {h : ℕ → ℝ}
    (hh : ∀ r : ℕ, 1 ≤ r → r ≤ k+1 → 0 < h r)
    (hprevious : ∀ r : ℕ, 1 ≤ r → r ≤ k → ∀ (μ : Measure (Space n)), admissibleMeasure μ →
      ∀ f : Space n → ℝ, MemLp f 2 μ → actualAppellEnergy μ f r ≤ h r*(∫ x, (f x)^2 ∂μ))
    (b : CenteredVariableCoefficientInductionBarrier k h)
    {ν : Measure (Space n)} [IsProbabilityMeasure ν] (hν : admissibleMeasure ν)
    (g : Lp ℝ 2 ν) (hg : ‖g‖=1) :
    actualAppellEnergy ν g (k+1) ≤ h (k+1)*b.phi (actualAppellEnergy ν g k/h k) := by
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
  have hstat' : ∀ ell : Lp ℝ 2 (μ : Measure (Space n)),
      inner ℝ (fullClassAppellTensor (k+1) f) (fullClassAppellTensor (k+1) ell)+
      X*q/(h k)*inner ℝ (fullClassAppellTensor k f) (fullClassAppellTensor k ell) =
      X*(1+u*q)*inner ℝ f ell := by
    intro ell
    have hs := hstat ell
    simp only [← actualAppellEnergy_eq_norm_sq] at hs
    exact hs
  have hbound : X ≤ h (k+1)*b.phi u := by
    by_contra hn
    have hex : h (k+1)*b.phi u < X := lt_of_not_ge hn
    have hXp : 0<X := (mul_pos hhj (b.positive u hu)).trans hex
    have hmaximum := actual_adjacent_quotient_centered_heat_nonpos hμ (by omega) p hhk hfunit
      b.concave b.positive hprevk (b.hasDeriv u hu) hXp hq.le hmax
    have ht := actualAppell_centered_weighted_energy_inequality hμ f hfunit hk hhk
      (fun r hr hrk => (hh r hr (by omega)).le)
      (fun r hr hrk => hprevious r hr hrk (μ : Measure (Space n)) hμ)
      (b.alpha_unit u hu).1.le (b.alpha_unit u hu).2 hq.le hstat' hmaximum
    have hY : Y = h k*u := by dsimp [u]; field_simp [hhk.ne']
    have hcrit := b.criterion u hu
    exact centered_weighted_terminal_excess_contradiction hhk hhj (b.positive u hu)
      (b.alpha_unit u hu).1 hq (actualLowerConvolution_nonneg h (k+1)) hex hY hcrit
      (by simpa only [Nat.cast_add,Nat.cast_one] using ht)
  have hmaxbound : coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
      (fullClassAppellLinearMap hμ.logConcave (k+1)) (h k) b.phi f ≤ h (k+1) := by
    change ‖fullClassAppellTensor (k+1) f‖^2/
      (‖f‖^2*b.phi (‖fullClassAppellTensor k f‖^2/(h k*‖f‖^2))) ≤ _
    rw [hfunit,one_pow,one_mul,mul_one,← actualAppellEnergy_eq_norm_sq,
      ← actualAppellEnergy_eq_norm_sq]
    exact (div_le_iff₀ (b.positive u hu)).mpr hbound
  have hgne : g≠0 := by
    intro he
    rw [he,norm_zero] at hg
    norm_num at hg
  have hug : actualAppellEnergy ν g k/h k∈Icc (0:ℝ) 1 := by
    have hhg := actualAppell_ratio_mem_Icc hν hhk hprevk g hgne
    rw [hg,one_pow,mul_one,←actualAppellEnergy_eq_norm_sq] at hhg
    exact hhg
  let ν₀ : ProbabilityMeasure (Space n) := ⟨ν,hν.isProb⟩
  have hgquot := (hmax ν₀ hν g).trans hmaxbound
  change ‖fullClassAppellTensor (k+1) g‖^2/
    (‖g‖^2*b.phi (‖fullClassAppellTensor k g‖^2/(h k*‖g‖^2)))≤h (k+1) at hgquot
  rw [hg,one_pow,one_mul,mul_one,←actualAppellEnergy_eq_norm_sq,
    ←actualAppellEnergy_eq_norm_sq] at hgquot
  exact (div_le_iff₀ (b.positive _ hug)).mp hgquot

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_centered_variable_coefficient_joint_unit_bound
