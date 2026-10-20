import KLSConstantImprovement.SyntheticEightDegreeBudget
import KLSConstantImprovement.ExtendedSyntheticLossSlopes

/-! Finite synthetic generator dual through any degree N ≤ 65.  The
energy table is an explicit input with exact nonnegative recurrence
inequalities. The current analytic head corner is retained explicitly.
These test energies are not asserted to come from an admissible law.
This isolated source draft has not been compiled by its author. -/

noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.ExtendedSyntheticDegreeBudget
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
open KLSConstantImprovement.SyntheticGeneratorLossLower
open KLSConstantImprovement.SyntheticEightDegreeBudget (G)

def energy (P : Parameters) (z : ℕ → ℝ) (d : ℕ) : ℝ := P.t d * z d / P.K ^ d

theorem energy_nonnegative {P : Parameters} {H A B : ℝ}
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (z : ℕ → ℝ) (d : ℕ) (hd : 2 ≤ d) (hz : 0 ≤ z d) : 0 ≤ energy P z d :=
  div_nonneg (mul_nonneg (h.weight_positive d hd).le hz) (pow_nonneg h.K_positive.le d)

theorem incoming_energy_identity {P : Parameters} {H A B : ℝ}
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (z : ℕ → ℝ) (d : ℕ) (hd : 3 ≤ d) :
    PositiveEnergyWeightedGenerator.incoming P.K P.t P.alpha d * energy P z d =
      ((d : ℝ) ^ 2 * z d) * (P.alpha (d - 1) * P.t (d - 1) / P.K ^ (d - 1)) := by
  have hK : P.K ≠ 0 := ne_of_gt h.K_positive
  have ht : P.t d ≠ 0 := ne_of_gt (h.weight_positive d (by omega))
  have hpow : P.K ^ d = P.K ^ (d - 1) * P.K := by
    rw [←pow_succ]
    congr 1
    omega
  unfold PositiveEnergyWeightedGenerator.incoming energy
  rw [hpow]
  field_simp [hK, ht, pow_ne_zero (d - 1) hK] <;> ring

theorem coefficient_edge {P : Parameters} {H A B : ℝ}
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (z : ℕ → ℝ) (d : ℕ) (hd : 3 ≤ d) (hD : d ≤ 65)
    (hzprev : 0 ≤ z (d - 1))
    (hzrec : (d : ℝ) ^ 2 * z d ≤ ExtendedSyntheticLossSlopes.slope (d - 1) * z (d - 1)) :
    coefficient P d * energy P z d ≤
      G P (d - 1) * energy P z (d - 1) - G P d * energy P z d := by
  have hfac : 0 ≤ P.alpha (d - 1) * P.t (d - 1) / P.K ^ (d - 1) :=
    div_nonneg (mul_nonneg (h.alpha_nonneg (d - 1) (by omega))
      (h.weight_positive (d - 1) (by omega)).le) (pow_nonneg h.K_positive.le _)
  have hrec := mul_le_mul_of_nonneg_right hzrec hfac
  have hs := ExtendedSyntheticLossSlopes.table_effective_slope h (d - 1) (by omega) (by omega)
  change ExtendedSyntheticLossSlopes.slope (d - 1) * P.alpha (d - 1) ≤ G P (d - 1) at hs
  have hscaled := mul_le_mul_of_nonneg_right hs
    (energy_nonnegative h z (d - 1) (by omega) hzprev)
  have hin : PositiveEnergyWeightedGenerator.incoming P.K P.t P.alpha d * energy P z d ≤
      G P (d - 1) * energy P z (d - 1) := by
    calc
      _ = ((d : ℝ) ^ 2 * z d) *
          (P.alpha (d - 1) * P.t (d - 1) / P.K ^ (d - 1)) := incoming_energy_identity h z d hd
      _ ≤ (ExtendedSyntheticLossSlopes.slope (d - 1) * z (d - 1)) *
          (P.alpha (d - 1) * P.t (d - 1) / P.K ^ (d - 1)) := hrec
      _ = (ExtendedSyntheticLossSlopes.slope (d - 1) * P.alpha (d - 1)) *
          energy P z (d - 1) := by unfold energy; ring
      _ ≤ _ := hscaled
  rw [SyntheticEightDegreeBudget.coefficient_eq]
  nlinarith only [hin]

theorem telescoping_bound {P : Parameters} {H A B : ℝ}
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (z : ℕ → ℝ) (N : ℕ) (hN : 3 ≤ N) (hNmax : N ≤ 65)
    (hz : ∀ d, 2 ≤ d → d ≤ N → 0 ≤ z d)
    (hrec : ∀ d, 3 ≤ d → d ≤ N →
      (d : ℝ) ^ 2 * z d ≤ ExtendedSyntheticLossSlopes.slope (d - 1) * z (d - 1)) :
    (∑ d ∈ Finset.Icc 3 N, coefficient P d * energy P z d) - G P 2 * energy P z 2 ≤
      -G P N * energy P z N := by
  have hall : ∀ M : ℕ, 3 ≤ M → M ≤ N →
      (∑ d ∈ Finset.Icc 3 M, coefficient P d * energy P z d) - G P 2 * energy P z 2 ≤
        -G P M * energy P z M := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      intro hMN
      have hh := coefficient_edge h z 3 (by omega) (by omega)
        (hz 2 (by omega) (by omega)) (hrec 3 (by omega) hMN)
      simp only [Finset.Icc_self, Finset.sum_singleton] 
      norm_num only [Nat.reduceSub] at hh
      nlinarith only [hh]
    | succ M hM ih =>
      intro hMN
      have hp := ih (by omega : M ≤ N)
      have hh := coefficient_edge h z (M + 1) (by omega) (by omega)
        (hz M (by omega) (by omega)) (hrec (M + 1) (by omega) hMN)
      rw [Finset.sum_Icc_succ_top (by omega : 3 ≤ M + 1)]
      simp only [Nat.add_sub_cancel] at hh
      nlinarith only [hp, hh]
  exact hall N hN le_rfl

theorem synthetic_generator_nonpositive {P : Parameters} {H A B : ℝ}
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (z : ℕ → ℝ) (N : ℕ) (hN : 3 ≤ N) (hNmax : N ≤ 65)
    (hz : ∀ d, 2 ≤ d → d ≤ N → 0 ≤ z d)
    (hrec : ∀ d, 3 ≤ d → d ≤ N →
      (d : ℝ) ^ 2 * z d ≤ ExtendedSyntheticLossSlopes.slope (d - 1) * z (d - 1)) :
    (∑ d ∈ Finset.Icc 3 N, coefficient P d * energy P z d) - head P * energy P z 2 ≤ 0 := by
  have hh := telescoping_bound h z N hN hNmax hz hrec
  have hlast : 0 ≤ G P N * energy P z N :=
    mul_nonneg (effective_loss_nonnegative h N (by omega))
      (energy_nonnegative h z N (by omega) (hz N (by omega) le_rfl))
  rw [SyntheticEightDegreeBudget.head_eq]
  nlinarith only [hh, hlast]

theorem synthetic_budget_lt {P : Parameters} {H A B : ℝ}
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (hH : (360 : ℝ) ≤ H) (hcorner : (265 / 4 : ℝ) + A * 10 ≤ B)
    (z : ℕ → ℝ) (N : ℕ) (hN : 4 ≤ N) (hNmax : N ≤ 65)
    (hz : ∀ d, 2 ≤ d → d ≤ N → 0 ≤ z d)
    (hz2 : z 2 = 2) (hz3 : z 3 = 10) (hz4 : z 4 = 265 / 4)
    (hrec : ∀ d, 3 ≤ d → d ≤ N →
      (d : ℝ) ^ 2 * z d ≤ ExtendedSyntheticLossSlopes.slope (d - 1) * z (d - 1)) :
    (∑ d ∈ Finset.Icc 2 N, P.t d * z d / P.K ^ d) < P.C := by
  apply RawCubicQuarticWeightedHead.finite_energy_sum_lt_budget (y := 10) (z := 265 / 4) P
    h.K_positive h.c_positive h.coefficient_lower h.head_nonneg h.fourth_nonneg h.head_margin
    (energy P z) N hN
  · intro d hd
    exact energy_nonnegative h z d (by have := (Finset.mem_Icc.mp hd).1; omega)
      (hz d (by have := (Finset.mem_Icc.mp hd).1; omega) (Finset.mem_Icc.mp hd).2)
  · norm_num [energy, hz2, mul_comm]
  · norm_num [energy, hz3]
  · norm_num [energy, hz4]
  · norm_num
  · exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 36)).mpr (by linarith)
  · exact hcorner
  · exact synthetic_generator_nonpositive h z N (by omega) hNmax hz hrec

end KLSConstantImprovement.ExtendedSyntheticDegreeBudget

#print axioms KLSConstantImprovement.ExtendedSyntheticDegreeBudget.telescoping_bound
#print axioms KLSConstantImprovement.ExtendedSyntheticDegreeBudget.synthetic_generator_nonpositive
#print axioms KLSConstantImprovement.ExtendedSyntheticDegreeBudget.synthetic_budget_lt
