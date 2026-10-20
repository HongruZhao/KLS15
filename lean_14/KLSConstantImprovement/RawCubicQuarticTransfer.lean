import ActualQuarticCreation239Barrier
import KLSConstantImprovement.RawCubicWeightedBudget

/-! Generic actual-law cubic-to-quartic transfer, using the already proved
maximizer and arbitrary-H quartic terminal. The sole law input is the
displayed universal raw cubic bound. No old same-test seed curve is used.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLSConstantImprovement.RawCubicQuarticTransfer
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

structure RawCubicQuarticBarrier (H J : ℝ) extends ScalarVariableBarrierShape where
  alpha_ge_half : ∀ u∈Icc (0:ℝ) 1,(1/2:ℝ) ≤ alpha u
  criterion : ∀ u∈Icc (0:ℝ) 1,∀ Z∈Icc (0:ℝ) 8,
    (-deriv phi u/phi u)*
      (alpha u*J/H*phi u-(44/(1-alpha u)-32)*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/
        Real.sqrt (J*phi u)

theorem actual_raw_cubic_quartic_joint_unit_bound {n : ℕ}
    {H J : ℝ} (hH : 0 < H)
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound H)
    (hJ : 0 < J) (b : RawCubicQuarticBarrier H J)
    {ν : Measure (Space n)} [IsProbabilityMeasure ν] (hν : admissibleMeasure ν)
    (g : Lp ℝ 2 ν) (hg : ‖g‖=1) :
    actualAppellEnergy ν g 4 ≤ J*b.phi (actualAppellEnergy ν g 3/H) := by
  have hprevious : ∀ (μ : Measure (Space n)),admissibleMeasure μ →
      ∀ f : Space n → ℝ,MemLp f 2 μ →
        actualAppellEnergy μ f 3 ≤ H*(∫ x,(f x)^2 ∂μ) := by
    intro μ hμ f hf
    exact hraw hμ hf
  let μ₀ : ProbabilityMeasure (Space n) := ⟨ν, hν.isProb⟩
  obtain ⟨μ,hμ,c,hunit,hmax,hstat,henergy⟩ := exists_actual_joint_maximizer_energy_inequality
    (show admissibleMeasure (μ₀ : Measure (Space n)) from hν) hH b.continuous b.positive b.antitone b.concave b.hasDeriv hprevious
  let p := boundedDegreePolynomial c
  let f : Lp ℝ 2 (μ : Measure (Space n)) := polynomialLp hμ.logConcave p
  have hfunit : ‖f‖=1 := hunit
  have hfne : f ≠ 0 := by
    intro hfz
    rw [hfz,norm_zero] at hfunit
    norm_num at hfunit
  let X := actualAppellEnergy (μ : Measure (Space n)) f 4
  let Y := actualAppellEnergy (μ : Measure (Space n)) f 3
  let Z := actualAppellEnergy (μ : Measure (Space n)) f 2
  let u := Y/H
  let q := -deriv b.phi u/b.phi u
  have hu : u ∈ Icc (0:ℝ) 1 := by
    have hu' := actualAppell_ratio_mem_Icc hμ hH hprevious f hfne
    rw [hfunit,one_pow,mul_one,←actualAppellEnergy_eq_norm_sq] at hu'
    exact hu'
  have hZ : Z ∈ Icc (0:ℝ) 8 := by
    refine ⟨actualAppellEnergy_nonneg _ _ _,?_⟩
    have hb := actualAppellEnergy_two_le_eight_norm_sq hμ f
    rwa [hfunit,one_pow,mul_one] at hb
  have hq : 0 < q := div_pos (neg_pos.mpr (b.derivative_negative u hu)) (b.positive u hu)
  have hstat' : ∀ ell : Lp ℝ 2 (μ : Measure (Space n)),
      inner ℝ (fullClassAppellTensor 4 f) (fullClassAppellTensor 4 ell)+
      X*q/H*inner ℝ (fullClassAppellTensor 3 f) (fullClassAppellTensor 3 ell)=
      X*(1+u*q)*inner ℝ f ell := by
    intro ell
    have hs := hstat ell
    simp only [←actualAppellEnergy_eq_norm_sq] at hs
    exact hs
  have hbound : X ≤ J*b.phi u := by
    by_contra hn
    have hex : J*b.phi u < X := lt_of_not_ge hn
    have hXp : 0 < X := (mul_pos hJ (b.positive u hu)).trans hex
    have hmaximum := actual_adjacent_quotient_centered_heat_nonpos hμ (k:=3) (by norm_num)
      p hH hfunit b.concave b.positive hprevious (b.hasDeriv u hu) hXp hq.le hmax
    have ht := actualAppell_centered_weighted_energy_inequality_three_creation hμ f hfunit hH
      (b.alpha_ge_half u hu) (b.alpha_unit u hu).2 hq.le hstat' hmaximum
    have hY : Y=H*u := by dsimp [u]; field_simp [hH.ne']
    exact quartic_creation_terminal_excess_contradiction hH hJ (b.positive u hu)
      (b.alpha_unit u hu).1 hq hex hY (b.criterion u hu Z hZ) ht
  have hmaxbound : coefficientQuotient (fullClassAppellLinearMap hμ.logConcave 3)
      (fullClassAppellLinearMap hμ.logConcave 4) H b.phi f ≤ J := by
    change ‖fullClassAppellTensor 4 f‖^2/
      (‖f‖^2*b.phi (‖fullClassAppellTensor 3 f‖^2/(H*‖f‖^2))) ≤ _
    rw [hfunit,one_pow,one_mul,mul_one,←actualAppellEnergy_eq_norm_sq,
      ←actualAppellEnergy_eq_norm_sq]
    exact (div_le_iff₀ (b.positive u hu)).mpr hbound
  have hgne : g ≠ 0 := by
    intro he
    rw [he,norm_zero] at hg
    norm_num at hg
  have hug : actualAppellEnergy ν g 3/H ∈ Icc (0:ℝ) 1 := by
    have hb := actualAppell_ratio_mem_Icc hν hH hprevious g hgne
    rw [hg,one_pow,mul_one,←actualAppellEnergy_eq_norm_sq] at hb
    exact hb
  let ν₀ : ProbabilityMeasure (Space n) := ⟨ν,hν.isProb⟩
  have hgquot := (hmax ν₀ hν g).trans hmaxbound
  change ‖fullClassAppellTensor 4 g‖^2/
    (‖g‖^2*b.phi (‖fullClassAppellTensor 3 g‖^2/(H*‖g‖^2))) ≤ J at hgquot
  rw [hg,one_pow,one_mul,mul_one,←actualAppellEnergy_eq_norm_sq,
    ←actualAppellEnergy_eq_norm_sq] at hgquot
  exact (div_le_iff₀ (b.positive _ hug)).mp hgquot

end KLSConstantImprovement.RawCubicQuarticTransfer
#print axioms KLSConstantImprovement.RawCubicQuarticTransfer.actual_raw_cubic_quartic_joint_unit_bound
