import KLSConstantImprovement.ActualSameTestCreationTerminal
import ActualCreationCenteredCubicSeed24

/-! Fresh original-law same-test cubic barrier. Positive threshold transfer
uses the minimum of the new covariance ratio and the original cap48.
The full proper remainder and actual heat maximizer are retained.
The zero-dimensional energy is handled exactly. No author build. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLSConstantImprovement.OriginalUpperRecovery6SameTestBarrierDraft
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration KLSBelow25
open OriginalUpperRecovery6SameTestTerminalDraft
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

structure SameTestCreationCenteredCubicInductionBarrier (h : ℕ → ℝ) extends ScalarVariableBarrierShape where
  alpha_ge_third : ∀ u∈Icc (0:ℝ) 1,(1/3:ℝ)≤alpha u
  criterion : ∀ u∈Icc (0:ℝ) 1,
    (-deriv phi u/phi u)*(alpha u*h 3/h 2*phi u-
      ((32/(9*(1-alpha u))-2)*(2:ℝ)^2+((32/(9*(1-alpha u))-2)-3)*2+1)*u-
      2*actualLowerConvolution h 2/Real.sqrt (h 2)*Real.sqrt u) >
      2*(3:ℝ)^2-3+1+2*sameTestCreationRatio (h 3*phi u) (h 2*u)

theorem SameTestCreationCenteredCubicInductionBarrier.q_positive {h:ℕ→ℝ}
    (b:SameTestCreationCenteredCubicInductionBarrier h) {u:ℝ} (hu:u∈Icc (0:ℝ) 1) :
    0 < -deriv b.phi u/b.phi u :=
  div_pos (neg_pos.mpr (b.derivative_negative u hu)) (b.positive u hu)

theorem actual_same_test_creation_centered_cubic_unit_bound {n : ℕ}
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n)))
    {h : ℕ → ℝ}
    (hh : ∀ r : ℕ, 1 ≤ r → r ≤ 2+1 → 0 < h r)
    (hprevious : ∀ r : ℕ, 1 ≤ r → r ≤ 2 → ∀ (μ : Measure (Space n)), admissibleMeasure μ →
      ∀ f : Space n → ℝ, MemLp f 2 μ → actualAppellEnergy μ f r ≤ h r*(∫ x, (f x)^2 ∂μ))
    (b : SameTestCreationCenteredCubicInductionBarrier h)
    {ν : Measure (Space n)} [IsProbabilityMeasure ν] (hν : admissibleMeasure ν)
    (g : Lp ℝ 2 ν) (hg : ‖g‖=1) :
    actualAppellEnergy ν g (2+1) ≤ h (2+1)*b.phi (actualAppellEnergy ν g 2/h 2) := by
  classical
  by_cases hn0 : n=0
  · subst n
    have h2 : actualAppellEnergy ν g 2=0 := by simp [actualAppellEnergy]
    have h3 : actualAppellEnergy ν g (2+1)=0 := by simp [actualAppellEnergy]
    rw [h2,h3,zero_div,b.zero,mul_one]
    exact (hh (2+1) (by omega) le_rfl).le
  have hn : 1≤n := by omega
  have hhk := hh 2 (by omega) (by omega)
  have hhj := hh (2+1) (by omega) le_rfl
  have hprevk := hprevious 2 (by omega) le_rfl
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
  let X := actualAppellEnergy (μ : Measure (Space n)) f (2+1)
  let Y := actualAppellEnergy (μ : Measure (Space n)) f 2
  let u := Y/(h 2)
  let q := -deriv b.phi u/b.phi u
  have hu : u ∈ Icc (0 : ℝ) 1 := by
    have hu' := actualAppell_ratio_mem_Icc hμ hhk hprevk f hfne
    rw [hfunit,one_pow,mul_one,← actualAppellEnergy_eq_norm_sq] at hu'
    exact hu'
  have hq : 0 < q := b.q_positive hu
  have hstat' : ∀ ell : Lp ℝ 2 (μ : Measure (Space n)),
      inner ℝ (fullClassAppellTensor (2+1) f) (fullClassAppellTensor (2+1) ell)+
      X*q/(h 2)*inner ℝ (fullClassAppellTensor 2 f) (fullClassAppellTensor 2 ell) =
      X*(1+u*q)*inner ℝ f ell := by
    intro ell
    have hs := hstat ell
    simp only [← actualAppellEnergy_eq_norm_sq] at hs
    exact hs
  have hbound : X ≤ h (2+1)*b.phi u := by
    by_contra hnotbound
    have hex : h (2+1)*b.phi u < X := lt_of_not_ge hnotbound
    have hXp : 0<X := (mul_pos hhj (b.positive u hu)).trans hex
    have hmaximum := actual_adjacent_quotient_centered_heat_nonpos hμ (by omega) p hhk hfunit
      b.concave b.positive hprevk (b.hasDeriv u hu) hXp hq.le hmax
    have ht := actualAppell_centered_weighted_energy_inequality_two_same_test_creation hn hμ f hfunit hhk
      (fun r hr hrk => (hh r hr (by omega)).le)
      (fun r hr hrk => hprevious r hr hrk (μ : Measure (Space n)) hμ)
      (M := h (2+1)*b.phi u) (mul_pos hhj (b.positive u hu)) (by
        change h (2+1)*b.phi u≤actualAppellEnergy (μ : Measure (Space n)) f 3
        exact le_of_lt hex)
      (b.alpha_ge_third u hu) (b.alpha_unit u hu).2 hq.le hstat' hmaximum
    have hY : Y = h 2*u := by dsimp [u]; field_simp [hhk.ne']
    have hcrit := b.criterion u hu
    have ha : 1-b.alpha u≠0 := (sub_pos.mpr (b.alpha_unit u hu).2).ne'
    have hd2 : actualLowerConvolution h 2=0 := by norm_num [actualLowerConvolution]
    have hcrit' : q*(b.alpha u*(h (2+1)*b.phi u)/(h 2)-
        (64/(3*(1-b.alpha u))-17)*u) >
        16+2*sameTestCreationRatio (h (2+1)*b.phi u) (h 2*u) := by
      dsimp only [q]
      convert hcrit using 1 <;>
        norm_num only [hd2, show (2+1 : ℕ) = 3 from rfl,
          Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,mul_zero,zero_div,sub_zero]
      field_simp [ha,hhk.ne'] <;> ring
    have hp := mul_pos (mul_pos hXp hq) (mul_pos (b.alpha_unit u hu).1 (sub_pos.mpr hex))
    have hc := mul_lt_mul_of_pos_left hcrit' hXp
    have ht' : (X*q/(h 2))*b.alpha u*X-15*X-
        (X*q/(h 2))*(64/(3*(1-b.alpha u))-18)*Y-
        X*(1+u*q)-2*X*sameTestCreationRatio (h (2+1)*b.phi u) (h 2*u) ≤ 0 := by
      have ht0 : (X*q/(h 2))*b.alpha u*X-15*X-
          (X*q/(h 2))*(64/(3*(1-b.alpha u))-18)*Y-
          X*(1+u*q)-2*X*sameTestCreationRatio (h (2+1)*b.phi u) Y-
          2*(X*q/(h 2))*Real.sqrt Y*actualLowerConvolution h 2 ≤ 0 := ht
      simpa only [hd2,mul_zero,sub_zero,hY] using ht0
    have he : (X*q/(h 2))*b.alpha u*X-15*X-
        (X*q/(h 2))*(64/(3*(1-b.alpha u))-18)*(h 2*u)-
        X*(1+u*q)-2*X*sameTestCreationRatio (h (2+1)*b.phi u) (h 2*u) =
        X*(q*(b.alpha u*(h (2+1)*b.phi u)/(h 2)-
          (64/(3*(1-b.alpha u))-17)*u)-
          (16+2*sameTestCreationRatio (h (2+1)*b.phi u) (h 2*u)))+
        (X*q*b.alpha u*(X-h (2+1)*b.phi u))/(h 2) := by
      field_simp [hhk.ne']
      ring
    rw [hY,he] at ht'
    have hgap : 0 < (X*q*b.alpha u*(X-h (2+1)*b.phi u))/(h 2) := by
      convert div_pos hp hhk using 1 <;> ring
    nlinarith [hc,hgap]
  have hmaxbound : coefficientQuotient (fullClassAppellLinearMap hμ.logConcave 2)
      (fullClassAppellLinearMap hμ.logConcave (2+1)) (h 2) b.phi f ≤ h (2+1) := by
    change ‖fullClassAppellTensor (2+1) f‖^2/
      (‖f‖^2*b.phi (‖fullClassAppellTensor 2 f‖^2/(h 2*‖f‖^2))) ≤ _
    rw [hfunit,one_pow,one_mul,mul_one,← actualAppellEnergy_eq_norm_sq,
      ← actualAppellEnergy_eq_norm_sq]
    exact (div_le_iff₀ (b.positive u hu)).mpr hbound
  have hgne : g≠0 := by
    intro he
    rw [he,norm_zero] at hg
    norm_num at hg
  have hug : actualAppellEnergy ν g 2/h 2∈Icc (0:ℝ) 1 := by
    have hhg := actualAppell_ratio_mem_Icc hν hhk hprevk g hgne
    rw [hg,one_pow,mul_one,←actualAppellEnergy_eq_norm_sq] at hhg
    exact hhg
  let ν₀ : ProbabilityMeasure (Space n) := ⟨ν,hν.isProb⟩
  have hgquot := (hmax ν₀ hν g).trans hmaxbound
  change ‖fullClassAppellTensor (2+1) g‖^2/
    (‖g‖^2*b.phi (‖fullClassAppellTensor 2 g‖^2/(h 2*‖g‖^2)))≤h (2+1) at hgquot
  rw [hg,one_pow,one_mul,mul_one,←actualAppellEnergy_eq_norm_sq,
    ←actualAppellEnergy_eq_norm_sq] at hgquot
  exact (div_le_iff₀ (b.positive _ hug)).mp hgquot

end KLSConstantImprovement.OriginalUpperRecovery6SameTestBarrierDraft
#print axioms KLSConstantImprovement.OriginalUpperRecovery6SameTestBarrierDraft.SameTestCreationCenteredCubicInductionBarrier.q_positive
#print axioms KLSConstantImprovement.OriginalUpperRecovery6SameTestBarrierDraft.actual_same_test_creation_centered_cubic_unit_bound
