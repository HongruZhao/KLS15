import ActualCubicExcludedHarmonicRawDrift
import ActualTwoRowsHarmonicCenteredDrift

/-! The whole cubic proper drift is excluded from Young's inequality.
Its canonical credit is retained. Only the first size-two neighbor charge
is absent; all remaining higher-row costs use the unchanged full budget. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def cubicExcludedHarmonicCost (K C : ℝ) (s zeta2 zeta3 : ℕ → ℝ) (d : ℕ) : ℝ :=
  (K*C/s d)*(d : ℝ)^2+(if 4 ≤ d then twoRowsHarmonicFirstCost s zeta2 zeta3 d else 0)+
    (if 3 ≤ d then harmonicNeighborCharge K s zeta2 d else 0)+
    tripleHarmonicNeighborCharge K s zeta3 d

 theorem sum_previous_degree_from_four_le (N : ℕ) (F : ℕ → ℝ)
    (hF : ∀ b ∈ Finset.Icc 2 N, 0 ≤ F b) :
    (∑ d ∈ Finset.Icc 4 N, F (d-1)) ≤
      ∑ b ∈ Finset.Icc 2 N, if 3 ≤ b then F b else 0 := by
  classical
  have hinj : Set.InjOn (fun d : ℕ => d-1) (Finset.Icc 4 N : Set ℕ) := by
    intro d hd e he hde
    simp only [Finset.mem_coe,Finset.mem_Icc] at hd he
    dsimp only at hde
    omega
  have hsub : (Finset.Icc 4 N).image (fun d : ℕ => d-1) ⊆ Finset.Icc 2 N := by
    intro b hb
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hb
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  calc
    _ = ∑ b ∈ (Finset.Icc 4 N).image (fun d : ℕ => d-1), F b := (Finset.sum_image hinj).symm
    _ = ∑ b ∈ (Finset.Icc 4 N).image (fun d : ℕ => d-1), if 3 ≤ b then F b else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hb
      have hh : 3 ≤ d-1 := by have := (Finset.mem_Icc.mp hd).1; omega
      rw [ite_eq_left hh]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro b hb _
      split_ifs
      · exact hF b hb
      · exact le_rfl)

 theorem actual_weighted_proper_drift_harmonic_excluding_cubic_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ}
    (s zeta2 zeta3 : ℕ → ℝ) (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (hzeta2 : ∀ b, 2 ≤ b → 0 ≤ zeta2 b)
    (hcap2 : ∀ b, 2 ≤ b → 2*zeta2 b < (b : ℝ)*((b : ℝ)+1))
    (hzeta3 : ∀ b, 2 ≤ b → 0 ≤ zeta3 b)
    (hcap3 : ∀ (b : ℕ), 2 ≤ b → tripleHarmonicRatio (b : ℝ)*zeta3 b < 1)
    (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x,(g x)^2 ∂μ)) :
    2*(∑ d ∈ Finset.Icc 4 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d))+
      (K/s 2)*(coupledAppellQ μ f K 2 2)^2 ≤
      ∑ d ∈ Finset.Icc 2 N, cubicExcludedHarmonicCost K C s zeta2 zeta3 d*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
  have hh := actual_weighted_proper_drift_two_rows_harmonic_raw_excluding_cubic_le hμ hf
    s zeta2 zeta3 hK hs hzeta2 hcap2 hzeta3 hcap3 N hN hprevious
  have hp := sum_previous_degree_from_four_le N (fun b => harmonicNeighborCharge K s zeta2 b*
    (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b) (by
      intro b hb
      have hb2 := (Finset.mem_Icc.mp hb).1
      exact mul_nonneg (mul_nonneg (harmonicNeighborCharge_nonneg hK s zeta2 b hb2
        (hs b hb2) (hzeta2 b hb2)) (by positivity)) (actualAppellEnergy_nonneg _ _ _))
  have ht := sum_two_previous_degrees_le N (fun b => tripleHarmonicNeighborCharge K s zeta3 b*
    (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b) (by
      intro b hb
      have hb2 := (Finset.mem_Icc.mp hb).1
      exact mul_nonneg (mul_nonneg (tripleHarmonicNeighborCharge_nonneg hK s zeta3 b hb2
        (hs b hb2) (hzeta3 b hb2)) (by positivity)) (actualAppellEnergy_nonneg _ _ _))
  have htriple : (∑ d ∈ Finset.Icc 4 N, if 4 ≤ d then
      tripleHarmonicNeighborCharge K s zeta3 (d-2)*
        (K^(d-2)*((d-2).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-2) else 0) =
      ∑ d ∈ Finset.Icc 3 N, if 4 ≤ d then
        tripleHarmonicNeighborCharge K s zeta3 (d-2)*
          (K^(d-2)*((d-2).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-2) else 0 := by
    apply Finset.sum_subset (by intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega)
    intro d hd hn
    have hn4 : ¬4 ≤ d := by simp only [Finset.mem_Icc] at hd hn; omega
    rw [ite_eq_right hn4]
  have hfirst : (∑ d ∈ Finset.Icc 4 N, twoRowsHarmonicFirstCost s zeta2 zeta3 d*
      (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) =
      ∑ d ∈ Finset.Icc 2 N, (if 4 ≤ d then twoRowsHarmonicFirstCost s zeta2 zeta3 d else 0)*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
    calc
      _ = ∑ d ∈ Finset.Icc 4 N, (if 4 ≤ d then twoRowsHarmonicFirstCost s zeta2 zeta3 d else 0)*
          (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [ite_eq_left (Finset.mem_Icc.mp hd).1]
      _ = _ := by
        apply Finset.sum_subset (by intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega)
        intro d hd hn
        have hn4 : ¬4 ≤ d := by simp only [Finset.mem_Icc] at hd hn; omega
        rw [ite_eq_right hn4,zero_mul,zero_mul]
  simp only [Finset.sum_add_distrib] at hh
  rw [hfirst,htriple] at hh
  have he : (∑ d ∈ Finset.Icc 2 N, cubicExcludedHarmonicCost K C s zeta2 zeta3 d*
      (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) =
      (∑ d ∈ Finset.Icc 2 N, (K*C/s d)*(d : ℝ)^2*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)+
      (∑ d ∈ Finset.Icc 2 N, (if 4 ≤ d then twoRowsHarmonicFirstCost s zeta2 zeta3 d else 0)*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)+
      (∑ d ∈ Finset.Icc 2 N, if 3 ≤ d then harmonicNeighborCharge K s zeta2 d*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d else 0)+
      ∑ d ∈ Finset.Icc 2 N, tripleHarmonicNeighborCharge K s zeta3 d*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    unfold cubicExcludedHarmonicCost
    split_ifs <;> ring
  rw [he]
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_weighted_proper_drift_harmonic_excluding_cubic_le
