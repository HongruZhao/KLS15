import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The actual complex Banach-algebra spectral-radius to power-envelope
bridge. A real operator still needs a compatible complexification and an
actual spectral-radius estimate before this can be used in its endgame. -/
noncomputable section
open Filter
open scoped Topology
namespace KLSBelow25

/-- A nonnegative sequence bounded by a geometric tail has a single
geometric bound valid also for its finite initial segment. -/
theorem geometric_bound_of_eventually {a : ℕ → ℝ} {r : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hr : 0 < r)
    (htail : ∀ᶠ n in atTop, a n ≤ r^n) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, a n ≤ C*r^n := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 htail
  let C : ℝ := 1+∑ i ∈ Finset.range N, a i/r^i
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, a i/r^i := by
    apply Finset.sum_nonneg
    intro i hi
    exact div_nonneg (ha i) (pow_pos hr i).le
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,fun n => ?_⟩
  by_cases hn : n < N
  · have hterm : a n/r^n ≤ ∑ i ∈ Finset.range N, a i/r^i := by
      exact Finset.single_le_sum (fun i hi => div_nonneg (ha i) (pow_pos hr i).le)
        (Finset.mem_range.2 hn)
    apply (div_le_iff₀ (pow_pos hr n)).mp
    dsimp [C]
    linarith
  · exact (hN n (by omega)).trans
      (by nlinarith [pow_pos hr n])

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Gelfand's formula gives a uniform geometric norm bound at every rate
strictly greater than the actual complex spectral radius. -/
theorem power_norm_bound_of_spectralRadius_lt (a : A) {r : ℝ} (hr : 0 < r)
    (hspec : spectralRadius ℂ a < ENNReal.ofReal r) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, ‖a^n‖ ≤ C*r^n := by
  have hroot : ∀ᶠ n : ℕ in atTop, ‖a^n‖^(1/(n : ℝ)) < r := by
    have he := (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a).eventually
      (eventually_lt_nhds hspec)
    filter_upwards [he] with n hn
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mp hn
  have htail : ∀ᶠ n : ℕ in atTop, ‖a^n‖ ≤ r^n := by
    filter_upwards [hroot,eventually_ge_atTop 1] with n hn hnpos
    have hne : n ≠ 0 := by omega
    have hh := pow_le_pow_left₀
      (Real.rpow_nonneg (norm_nonneg (a^n)) (1/(n : ℝ))) hn.le n
    simpa only [one_div,Real.rpow_inv_natCast_pow (norm_nonneg (a^n)) hne] using hh
  exact geometric_bound_of_eventually (fun n => norm_nonneg _) hr htail

/-- An actual spectral-radius bound by sqrt K implies the squared-power
envelope needed in Proposition 7.3, with every factor rho>1. -/
theorem squared_power_envelope_of_spectralRadius_le (a : A) {K : ℝ} (hK : 0 < K)
    (hspec : spectralRadius ℂ a ≤ ENNReal.ofReal (Real.sqrt K)) :
    ∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ n : ℕ, ‖a^n‖^2 ≤ M*(K*rho)^n := by
  intro rho hrho
  have hrhopos : 0 < rho := by linarith
  have hKrho : 0 < K*rho := mul_pos hK hrhopos
  have hr : 0 < Real.sqrt (K*rho) := Real.sqrt_pos.mpr hKrho
  have hrootlt : Real.sqrt K < Real.sqrt (K*rho) := by
    apply Real.sqrt_lt_sqrt hK.le
    nlinarith
  have hspeclt : spectralRadius ℂ a < ENNReal.ofReal (Real.sqrt (K*rho)) :=
    hspec.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hrootlt)
  obtain ⟨C,hC,hbound⟩ := power_norm_bound_of_spectralRadius_lt a hr hspeclt
  refine ⟨C^2,fun n => ?_⟩
  have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ C*(Real.sqrt (K*rho))^n)).mpr
    (hbound n)
  calc
    ‖a^n‖^2 ≤ (C*(Real.sqrt (K*rho))^n)^2 := hh
    _ = C^2*(K*rho)^n := by
      rw [mul_pow,← pow_mul, Nat.mul_comm n 2, pow_mul,Real.sq_sqrt hKrho.le]

#print axioms geometric_bound_of_eventually
#print axioms power_norm_bound_of_spectralRadius_lt
#print axioms squared_power_envelope_of_spectralRadius_le
end KLSBelow25
