import KLSConstantImprovement.RawCubicQuarticWeightedBudget
import TwoRowsOutgoingShift

/-!
# Actual-source loss lower bounds for a synthetic generator dual

All selected first costs and harmonic charges are retained.  The base
budget pays eight times the canonical reservation parameter at every
degree, which dominates both possible noise refunds.  These are scalar
certificate consequences, not lower bounds on the universal KLS constant.

This source draft has not been compiled by its author.
-/

noncomputable section
open scoped BigOperators

namespace KLSConstantImprovement.SyntheticGeneratorLossLower

open KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSBelow25.PairProjection
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
open KLSConstantImprovement.PositiveEnergyWeightedGenerator
open KLSConstantImprovement.PositiveEnergyWeightedDrift
open KLSConstantImprovement.SignedQuadraticReservedNoise
open KLSConstantImprovement.SignedRowReservedNoise
open KLSConstantImprovement.SignedRowNoiseHigh

/-- Baseline gamma-one, kappa-zero generator loss, including the final one. -/
def unreservedG (d : ℕ) (a : ℝ) : ℝ := degreeLoss d a 1 0 + 1

variable {P : Parameters} {H A B : ℝ}

theorem selected_first_cost_nonneg
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (d : ℕ) (hd : 3 ≤ d) :
    0 ≤ TriplePositiveEnergyWeightedDrift.selectedFirstCost P.young P.t
      (twoRowsProfile P.theta (tripleHarmonicThetaProfile P.zeta))
      (twoRowsLambda P.lambda (tripleHarmonicLambdaProfile P.zeta)) d := by
  unfold TriplePositiveEnergyWeightedDrift.selectedFirstCost
  apply Finset.sum_nonneg
  intro aa haa
  have ha2 : 2 ≤ aa := (Finset.mem_Icc.mp haa).1
  have had : aa ≤ d-1 := (Finset.mem_Icc.mp haa).2
  have hb2 : 2 ≤ d-aa+1 := by omega
  have hden : 0 ≤ 1-twoRowsLambda P.lambda (tripleHarmonicLambdaProfile P.zeta)
      aa (d-aa+1) := by
    unfold twoRowsLambda
    split_ifs
    · exact sub_nonneg.mpr (h.lambda_le_one _ hb2)
    · exact sub_nonneg.mpr
        (tripleHarmonicLambdaProfile_lt_one P.zeta h.zeta_cap _ hb2).le
    · norm_num
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (h.young_positive _ hb2).le
        (div_nonneg (h.weight_positive d (by omega)).le
          (mul_nonneg (h.weight_positive aa ha2).le (h.weight_positive _ hb2).le)))
      (sq_nonneg _)) hden

theorem extra_nonneg
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B) (d : ℕ) :
    0 ≤ TriplePositiveEnergyWeightedBudgetDrift.extra P.young P.t P.zeta d := by
  unfold TriplePositiveEnergyWeightedBudgetDrift.extra
  by_cases hd : 4 ≤ d
  · rw [if_pos hd]
    have hb : 2 ≤ d-2 := by omega
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (tripleHarmonicThetaProfile_nonneg P.zeta h.zeta_nonneg d)
          (tripleHarmonicEtaProfile_pos P.zeta h.zeta_nonneg d).le)
        (h.young_positive _ hb).le)
      (div_nonneg (h.weight_positive d (by omega)).le
        (mul_nonneg (h.weight_positive 3 (by omega)).le (h.weight_positive _ hb).le))
  · simp only [if_neg hd,le_refl]

theorem raw_first_cost_nonneg
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (d : ℕ) (hd : 3 ≤ d) :
    0 ≤ TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost
      P.young P.t P.theta P.lambda P.zeta d := by
  exact add_nonneg (selected_first_cost_nonneg h d hd) (extra_nonneg h d)

theorem neighbor_charge_nonneg
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (d : ℕ) (hd : 2 ≤ d) :
    0 ≤ tripleHarmonicNeighborCharge P.K P.young P.zeta d :=
  tripleHarmonicNeighborCharge_nonneg h.K_positive P.young P.zeta d hd
    (h.young_positive d hd) (h.zeta_nonneg d hd)

theorem kappa_nonneg
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (d : ℕ) (hd : 2 ≤ d) :
    0 ≤ kappa P.K P.young P.t P.lambda d := by
  have hK := h.K_positive
  have hy := h.young_positive d hd
  have ht := h.weight_positive 2 (by omega)
  have hl := h.lambda_nonneg d hd
  unfold kappa
  positivity

/-- The same base budget pays every size-two reservation refund. -/
theorem base_cost_pays_refund
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (d : ℕ) (hd : 2 ≤ d) :
    8*kappa P.K P.young P.t P.lambda d ≤
      (P.K*P.C/P.young d)*(d : ℝ)^2 := by
  have hK := h.K_positive
  have hy := h.young_positive d hd
  have ht := h.weight_positive 2 (by omega)
  have hb : 2*P.t 2 ≤ P.C*P.K^2 :=
    (div_le_iff₀ (sq_pos_of_pos hK)).mp h.base_budget
  have hl : P.lambda d*P.t 2 ≤ P.t 2 := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (h.lambda_le_one d hd) ht.le
  have hn : 2*P.lambda d*P.t 2*(d : ℝ)^2 ≤
      P.K^2*P.C*(d : ℝ)^2 :=
    mul_le_mul_of_nonneg_right (by nlinarith [hb,hl]) (sq_nonneg _)
  have hh := div_le_div_of_nonneg_right hn (mul_nonneg hK.le hy.le)
  unfold kappa
  convert hh using 1 <;> field_simp [ne_of_gt hK,ne_of_gt hy] <;> ring

theorem lowRefund_le_eight {d : ℝ} (hd : 3 ≤ d) : lowRefund d ≤ 8 := by
  have hden : 0 < 3*(d-1) := by linarith
  have hh : 8*(d-2)/(3*(d-1)) ≤ 4 :=
    (div_le_iff₀ hden).mpr (by linarith)
  unfold lowRefund
  linarith

/-- Both max branches lose at most eight kappa under the reservation. -/
theorem degreeLoss_refund_lower (d : ℕ) (hd : 2 ≤ d) {a g kap : ℝ}
    (ha : a < 1) (hg : 1 ≤ g) (hk : 0 ≤ kap) :
    degreeLoss d a 1 0 ≤ degreeLoss d a g kap+8*kap := by
  have hden : 0 < 1-a := by linarith
  have hgs : (1 : ℝ) ≤ g^2 := by nlinarith
  by_cases hd2 : d=2
  · subst d
    have hlterm : 16/(1-a) ≤ 16*g^2/(1-a) := by
      exact div_le_div_of_nonneg_right (by nlinarith [hgs]) hden.le
    have hhterm : 64/(3*(1-a)) ≤ 64*g^2/(3*(1-a)) := by
      exact div_le_div_of_nonneg_right (by nlinarith [hgs]) (by linarith)
    have hl : 16/(1-a)-12 ≤ quadraticNoiseLoss a g kap+8*kap := by
      have hm := le_max_left (16*g^2/(1-a)-12-4*kap)
        (64*g^2/(3*(1-a))-20-8*kap)
      unfold quadraticNoiseLoss
      linarith
    have hh : 64/(3*(1-a))-20 ≤ quadraticNoiseLoss a g kap+8*kap := by
      have hm := le_max_right (16*g^2/(1-a)-12-4*kap)
        (64*g^2/(3*(1-a))-20-8*kap)
      unfold quadraticNoiseLoss
      linarith
    have hm : quadraticNoiseLoss a 1 0 ≤ quadraticNoiseLoss a g kap+8*kap := by
      simpa only [quadraticNoiseLoss,one_pow,mul_one,mul_zero,sub_zero] using max_le hl hh
    unfold degreeLoss
    simp only [ite_true,Nat.cast_ofNat]
    linarith
  · have hdr : (3 : ℝ) ≤ d := by exact_mod_cast (show 3 ≤ d by omega)
    have hlead : 0 ≤ leadingNoiseCoefficient (d : ℝ) := by
      unfold leadingNoiseCoefficient
      have hdm : 0 ≤ (d : ℝ)-1 := by linarith
      have hdm2 : 0 ≤ (d : ℝ)-2 := by linarith
      positivity
    have hhigh : 0 ≤ highLeading (d : ℝ) := by unfold highLeading; positivity
    have hlterm : leadingNoiseCoefficient (d : ℝ)/(1-a) ≤
        g^2*leadingNoiseCoefficient (d : ℝ)/(1-a) := by
      apply div_le_div_of_nonneg_right _ hden.le
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hgs hlead
    have hhterm : highLeading (d : ℝ)/(1-a) ≤ g^2*highLeading (d : ℝ)/(1-a) := by
      apply div_le_div_of_nonneg_right _ hden.le
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hgs hhigh
    have hrefund : 0 ≤ kap*(8-lowRefund (d : ℝ)) :=
      mul_nonneg hk (sub_nonneg.mpr (lowRefund_le_eight hdr))
    have hl : leadingNoiseCoefficient (d : ℝ)/(1-a)-positiveNoiseCoefficient (d : ℝ) ≤
        reservedNoiseLoss (d : ℝ) a g kap+8*kap := by
      have hm := le_max_left
        (g^2*leadingNoiseCoefficient (d : ℝ)/(1-a)-positiveNoiseCoefficient (d : ℝ)-kap*lowRefund (d : ℝ))
        (g^2*highLeading (d : ℝ)/(1-a)-highPositive (d : ℝ)-8*kap)
      unfold reservedNoiseLoss
      nlinarith only [hm,hlterm,hrefund]
    have hh : highLeading (d : ℝ)/(1-a)-highPositive (d : ℝ) ≤
        reservedNoiseLoss (d : ℝ) a g kap+8*kap := by
      have hm := le_max_right
        (g^2*leadingNoiseCoefficient (d : ℝ)/(1-a)-positiveNoiseCoefficient (d : ℝ)-kap*lowRefund (d : ℝ))
        (g^2*highLeading (d : ℝ)/(1-a)-highPositive (d : ℝ)-8*kap)
      unfold reservedNoiseLoss
      linarith
    have hm : reservedNoiseLoss (d : ℝ) a 1 0 ≤
        reservedNoiseLoss (d : ℝ) a g kap+8*kap := by
      simpa only [reservedNoiseLoss,one_pow,one_mul,zero_mul,mul_zero,sub_zero] using max_le hl hh
    unfold degreeLoss
    simp only [hd2,ite_false]
    linarith

theorem cost_pays_refund
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (d : ℕ) (hd : 2 ≤ d) :
    8*kappa P.K P.young P.t P.lambda d ≤
      TriplePositiveEnergyWeightedBudget.cost P d := by
  have hb := base_cost_pays_refund h d hd
  have hn : 0 ≤ P.t 3*tripleHarmonicNeighborCharge P.K P.young P.zeta d :=
    mul_nonneg (h.weight_positive 3 (by omega)).le (neighbor_charge_nonneg h d hd)
  unfold TriplePositiveEnergyWeightedBudget.cost TriplePositiveEnergyWeightedGenerator.cost
  split_ifs with hd3
  · have hf := raw_first_cost_nonneg h d hd3
    linarith
  · linarith

theorem effective_loss_lower
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (d : ℕ) (hd : 2 ≤ d) :
    unreservedG d (P.alpha d) ≤
      generatorLoss P.K P.young P.t P.alpha P.theta P.lambda d+1+
        TriplePositiveEnergyWeightedBudget.cost P d := by
  have hg := gamma_ge_one h.K_positive P.t P.theta d
    (h.weight_positive d hd) (h.weight_positive (d+1) (by omega))
    (h.theta_nonneg (d+1) (by omega))
  have hn := degreeLoss_refund_lower d hd (h.alpha_lt_one d hd) hg (kappa_nonneg h d hd)
  have hc := cost_pays_refund h d hd
  unfold unreservedG generatorLoss
  linarith

/-- A rational quadratic discriminant certificate for any positive slope. -/
theorem slope_of_discriminant {L Q m a : ℝ} (ha : a < 1) (hm : 0 < m)
    (hdisc : 0 ≤ 4*m*(L-Q)-(Q-m)^2) :
    m*a ≤ L/(1-a)-Q := by
  have hid : 4*m*(m*a^2+(Q-m)*a+(L-Q))=
      (2*m*a+Q-m)^2+(4*m*(L-Q)-(Q-m)^2) := by ring
  have hprod : 0 ≤ 4*m*(m*a^2+(Q-m)*a+(L-Q)) := by
    rw [hid]
    exact add_nonneg (sq_nonneg _) hdisc
  have hquad : 0 ≤ m*a^2+(Q-m)*a+(L-Q) :=
    (mul_nonneg_iff_of_pos_left (by linarith : 0 < 4*m)).mp hprod
  have hh : m*a+Q ≤ L/(1-a) :=
    (le_div_iff₀ (by linarith : 0 < 1-a)).mpr (by nlinarith only [hquad])
  linarith

theorem unreservedG_lower_low (d : ℕ) (hd : 3 ≤ d) (a : ℝ) :
    leadingNoiseCoefficient (d : ℝ)/(1-a)-positiveNoiseCoefficient (d : ℝ)+
      (d : ℝ)+1 ≤ unreservedG d a := by
  have hd2 : d≠2 := by omega
  unfold unreservedG degreeLoss
  simp only [hd2,ite_false,reservedNoiseLoss,one_pow,one_mul,zero_mul,mul_zero,sub_zero]
  have hm : leadingNoiseCoefficient (d : ℝ)/(1-a)-positiveNoiseCoefficient (d : ℝ) ≤
      max (leadingNoiseCoefficient (d : ℝ)/(1-a)-positiveNoiseCoefficient (d : ℝ))
        (highLeading (d : ℝ)/(1-a)-highPositive (d : ℝ)) := le_max_left _ _
  linarith only [hm]

theorem slope_two (a : ℝ) (ha : a < 1) : 45*a ≤ unreservedG 2 a := by
  have hden : 0 < 1-a := by linarith
  unfold unreservedG degreeLoss
  simp only [ite_true,quadraticNoiseLoss,one_pow,mul_one,mul_zero,sub_zero,Nat.cast_ofNat]
  by_cases hlo : a ≤ (1/3 : ℝ)
  · have hp : 0 ≤ ((1/3 : ℝ)-a)*((7/15 : ℝ)-a) :=
      mul_nonneg (by linarith) (by linarith)
    have hb : 45*a+9 ≤ 16/(1-a) :=
      (le_div_iff₀ hden).mpr (by nlinarith only [hp])
    have hm := le_max_left (16/(1-a)-12) (64/(3*(1-a))-20)
    linarith
  · have hp : 0 ≤ (a-(1/3 : ℝ))*(a-(13/45 : ℝ)) :=
      mul_nonneg (by linarith) (by linarith)
    have hb : 45*a+17 ≤ 64/(3*(1-a)) :=
      (le_div_iff₀ (by linarith : 0 < 3*(1-a))).mpr (by nlinarith only [hp])
    have hm := le_max_right (16/(1-a)-12) (64/(3*(1-a))-20)
    linarith

theorem slope_three (a : ℝ) (ha : a < 1) : 106*a ≤ unreservedG 3 a := by
  calc
    106*a ≤ 40/(1-a)-24 := slope_of_discriminant ha (by norm_num) (by norm_num)
    _ = leadingNoiseCoefficient 3/(1-a)-positiveNoiseCoefficient 3+3+1 := by
      norm_num [leadingNoiseCoefficient,positiveNoiseCoefficient] <;> ring
    _ ≤ unreservedG 3 a := unreservedG_lower_low 3 (by omega) a

theorem slope_four (a : ℝ) (ha : a < 1) : 190*a ≤ unreservedG 4 a := by
  calc
    190*a ≤ (640/9 : ℝ)/(1-a)-(379/9 : ℝ) :=
      slope_of_discriminant ha (by norm_num) (by norm_num)
    _ = leadingNoiseCoefficient 4/(1-a)-positiveNoiseCoefficient 4+4+1 := by
      norm_num [leadingNoiseCoefficient,positiveNoiseCoefficient] <;> ring
    _ ≤ unreservedG 4 a := unreservedG_lower_low 4 (by omega) a

theorem slope_five (a : ℝ) (ha : a < 1) : 298*a ≤ unreservedG 5 a := by
  calc
    298*a ≤ 110/(1-a)-64 := slope_of_discriminant ha (by norm_num) (by norm_num)
    _ = leadingNoiseCoefficient 5/(1-a)-positiveNoiseCoefficient 5+5+1 := by
      norm_num [leadingNoiseCoefficient,positiveNoiseCoefficient] <;> ring
    _ ≤ unreservedG 5 a := unreservedG_lower_low 5 (by omega) a

theorem slope_six (a : ℝ) (ha : a < 1) : 428*a ≤ unreservedG 6 a := by
  calc
    428*a ≤ (784/5 : ℝ)/(1-a)-(449/5 : ℝ) :=
      slope_of_discriminant ha (by norm_num) (by norm_num)
    _ = leadingNoiseCoefficient 6/(1-a)-positiveNoiseCoefficient 6+6+1 := by
      norm_num [leadingNoiseCoefficient,positiveNoiseCoefficient] <;> ring
    _ ≤ unreservedG 6 a := unreservedG_lower_low 6 (by omega) a

theorem slope_seven (a : ℝ) (ha : a < 1) : 582*a ≤ unreservedG 7 a := by
  calc
    582*a ≤ (1904/9 : ℝ)/(1-a)-(1076/9 : ℝ) :=
      slope_of_discriminant ha (by norm_num) (by norm_num)
    _ = leadingNoiseCoefficient 7/(1-a)-positiveNoiseCoefficient 7+7+1 := by
      norm_num [leadingNoiseCoefficient,positiveNoiseCoefficient] <;> ring
    _ ≤ unreservedG 7 a := unreservedG_lower_low 7 (by omega) a

theorem unreservedG_nonnegative (d : ℕ) (hd : 2 ≤ d) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) : 0 ≤ unreservedG d a := by
  by_cases hd2 : d=2
  · subst d
    exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 45) ha0).trans (slope_two a ha1)
  · have hdr : (3 : ℝ) ≤ d := by exact_mod_cast (show 3 ≤ d by omega)
    have hden : 0 < 1-a := by linarith
    have hlead : 0 ≤ leadingNoiseCoefficient (d : ℝ) := by
      unfold leadingNoiseCoefficient
      have hdm : 0 ≤ (d : ℝ)-1 := by linarith
      have hdm2 : 0 ≤ (d : ℝ)-2 := by linarith
      positivity
    have hdiv : leadingNoiseCoefficient (d : ℝ) ≤
        leadingNoiseCoefficient (d : ℝ)/(1-a) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith only [mul_nonneg hlead ha0]
    have hid : leadingNoiseCoefficient (d : ℝ)-positiveNoiseCoefficient (d : ℝ)+
        (d : ℝ)+1=2*(d : ℝ)^2-(d : ℝ)+1 := by
      unfold leadingNoiseCoefficient positiveNoiseCoefficient
      ring
    have hbase : 0 ≤ leadingNoiseCoefficient (d : ℝ)-
        positiveNoiseCoefficient (d : ℝ)+(d : ℝ)+1 := by
      rw [hid]
      have hm : 0 ≤ (d : ℝ)*(2*(d : ℝ)-1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith only [hm]
    have hl : 0 ≤ leadingNoiseCoefficient (d : ℝ)/(1-a)-
        positiveNoiseCoefficient (d : ℝ)+(d : ℝ)+1 := by
      linarith only [hbase,hdiv]
    exact hl.trans (unreservedG_lower_low d (by omega) a)

/-- In particular the last synthetic degree has a nonnegative residual,
without requiring a slope bound at that last degree. -/
theorem effective_loss_nonnegative
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (d : ℕ) (hd : 2 ≤ d) :
    0 ≤ generatorLoss P.K P.young P.t P.alpha P.theta P.lambda d+1+
      TriplePositiveEnergyWeightedBudget.cost P d :=
  (unreservedG_nonnegative d hd (h.alpha_nonneg d hd) (h.alpha_lt_one d hd)).trans
    (effective_loss_lower h d hd)

end KLSConstantImprovement.SyntheticGeneratorLossLower

#print axioms KLSConstantImprovement.SyntheticGeneratorLossLower.effective_loss_lower
#print axioms KLSConstantImprovement.SyntheticGeneratorLossLower.slope_two
#print axioms KLSConstantImprovement.SyntheticGeneratorLossLower.slope_five
