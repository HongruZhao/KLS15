import TwoRowsHarmonicBudgetParameters
import ActualTwoRowsAppellDrift
import ActualHarmonicSelectiveBudgetDrift

/-! Literal selected triangular first-factor cost for two rows. The size-three
row starts at degree four; no terminal contraction is treated as proper. -/
noncomputable section
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem twoRows_selected_prefix_eq (s theta2 theta3 lambda2 lambda3 : ℕ → ℝ)
    {d : ℕ} (hd : 3 ≤ d) :
    selectedRowsPrefix s (twoRowsProfile theta2 theta3) (twoRowsLambda lambda2 lambda3) d =
      properYoungPrefix s d-s (d-1)+s (d-1)*(1-theta2 d)^2/(1-lambda2 (d-1)) +
      if 4 ≤ d then s (d-2)*(1-theta3 d)^2/(1-lambda3 (d-2))-s (d-2) else 0 := by
  classical
  have hmem2 : 2 ∈ Finset.Icc 2 (d-1) := by simp only [Finset.mem_Icc]; omega
  have hmem3 : (3 ∈ Finset.Icc 2 (d-1)) ↔ 4 ≤ d := by
    simp only [Finset.mem_Icc]
    omega
  have he : (∑ a ∈ Finset.Icc 2 (d-1),
      s (d-a+1)*(twoRowsProfile theta2 theta3 d a)^2/
        (1-twoRowsLambda lambda2 lambda3 a (d-a+1))) =
      ∑ a ∈ Finset.Icc 2 (d-1), (s (d-a+1)+
        (if a=2 then s (d-1)*(1-theta2 d)^2/(1-lambda2 (d-1))-s (d-1) else 0)+
        (if a=3 then s (d-2)*(1-theta3 d)^2/(1-lambda3 (d-2))-s (d-2) else 0)) := by
    apply Finset.sum_congr rfl
    intro a ha
    by_cases ha2 : a=2
    · subst a
      have hs : d-2+1=d-1 := by omega
      simp only [twoRowsProfile,twoRowsLambda,ite_true,hs,show (2:ℕ) ≠ 3 by decide,ite_false]
      ring
    · by_cases ha3 : a=3
      · subst a
        have hd4 : 4 ≤ d := hmem3.mp ha
        have hs : d-3+1=d-2 := by omega
        simp only [twoRowsProfile,twoRowsLambda,ha2,ite_false,ite_true,hs]
        ring
      · simp [twoRowsProfile,twoRowsLambda,ha2,ha3]
  unfold selectedRowsPrefix
  rw [he,Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',hmem2,ite_true,hmem3]
  have hp : (∑ a ∈ Finset.Icc 2 (d-1), s (d-a+1)) = properYoungPrefix s d := by
    unfold properYoungPrefix
    apply Finset.sum_bij (fun a _ => d-a+1)
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      omega
    · intro a ha b hb he
      simp only [Finset.mem_Icc] at ha hb
      omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      refine ⟨d-b+1,?_,?_⟩
      · simp only [Finset.mem_Icc]
        omega
      · omega
    · intro a ha
      rfl
  rw [hp]
  ring

def tripleHarmonicThetaProfile (zeta : ℕ → ℝ) (d : ℕ) : ℝ :=
  if 4 ≤ d then harmonicRatioTheta (tripleHarmonicRatio ((d-2 : ℕ) : ℝ)) (zeta (d-2)) else 0

def tripleHarmonicEtaProfile (zeta : ℕ → ℝ) (d : ℕ) : ℝ :=
  if 4 ≤ d then harmonicRatioEta (tripleHarmonicRatio ((d-2 : ℕ) : ℝ)) (zeta (d-2)) else 1

def tripleHarmonicLambdaProfile (zeta : ℕ → ℝ) (b : ℕ) : ℝ :=
  harmonicRatioLambda (tripleHarmonicRatio (b : ℝ)) (zeta b)

def twoRowsHarmonicFirstCost (s zeta2 zeta3 : ℕ → ℝ) (d : ℕ) : ℝ :=
  properYoungPrefix s d-
    (if 3 ≤ d then s (d-1)-s (d-1)/harmonicBudgetDenom ((d-1 : ℕ) : ℝ) (zeta2 (d-1)) else 0)-
    (if 4 ≤ d then s (d-2)-s (d-2)/
      harmonicRatioDenom (tripleHarmonicRatio ((d-2 : ℕ) : ℝ)) (zeta3 (d-2)) else 0)

theorem tripleHarmonicThetaProfile_nonneg (zeta : ℕ → ℝ)
    (hz : ∀ b, 2 ≤ b → 0 ≤ zeta b) (d : ℕ) :
    0 ≤ tripleHarmonicThetaProfile zeta d := by
  unfold tripleHarmonicThetaProfile
  split_ifs with hd
  · have hb : 2 ≤ d-2 := by omega
    exact harmonicRatioTheta_nonneg (tripleHarmonicRatio_le_one (by exact_mod_cast hb)) (hz _ hb)
  · norm_num

theorem tripleHarmonicThetaProfile_lt_one (zeta : ℕ → ℝ)
    (hz : ∀ b, 2 ≤ b → 0 ≤ zeta b)
    (hcap : ∀ (b : ℕ), 2 ≤ b → tripleHarmonicRatio (b : ℝ)*zeta b < 1) (d : ℕ) :
    tripleHarmonicThetaProfile zeta d < 1 := by
  unfold tripleHarmonicThetaProfile
  split_ifs with hd
  · have hb : 2 ≤ d-2 := by omega
    exact harmonicRatioTheta_lt_one (tripleHarmonicRatio_le_one (by exact_mod_cast hb)) (hz _ hb) (hcap _ hb)
  · norm_num

theorem tripleHarmonicEtaProfile_pos (zeta : ℕ → ℝ)
    (hz : ∀ b, 2 ≤ b → 0 ≤ zeta b) (d : ℕ) :
    0 < tripleHarmonicEtaProfile zeta d := by
  unfold tripleHarmonicEtaProfile
  split_ifs with hd
  · have hb : 2 ≤ d-2 := by omega
    exact harmonicRatioEta_pos (tripleHarmonicRatio_le_one (by exact_mod_cast hb)) (hz _ hb)
  · norm_num

theorem tripleHarmonicLambdaProfile_lt_one (zeta : ℕ → ℝ)
    (hcap : ∀ (b : ℕ), 2 ≤ b → tripleHarmonicRatio (b : ℝ)*zeta b < 1)
    (b : ℕ) (hb : 2 ≤ b) : tripleHarmonicLambdaProfile zeta b < 1 := hcap b hb

theorem twoRows_harmonic_first_cost_eq (s zeta2 zeta3 : ℕ → ℝ)
    (hz2 : ∀ b, 2 ≤ b → 0 ≤ zeta2 b)
    (hcap2 : ∀ b, 2 ≤ b → 2*zeta2 b < (b : ℝ)*((b : ℝ)+1))
    (hz3 : ∀ b, 2 ≤ b → 0 ≤ zeta3 b)
    (hcap3 : ∀ (b : ℕ), 2 ≤ b → tripleHarmonicRatio (b : ℝ)*zeta3 b < 1)
    (d : ℕ) (hd : 3 ≤ d) :
    selectedRowsPrefix s (twoRowsProfile (harmonicThetaProfile zeta2) (tripleHarmonicThetaProfile zeta3))
      (twoRowsLambda (harmonicLambdaProfile zeta2) (tripleHarmonicLambdaProfile zeta3)) d +
      harmonicThetaProfile zeta2 d*harmonicEtaProfile zeta2 d*s (d-1)+
      (if 4 ≤ d then tripleHarmonicThetaProfile zeta3 d*tripleHarmonicEtaProfile zeta3 d*s (d-2) else 0) =
      twoRowsHarmonicFirstCost s zeta2 zeta3 d := by
  have hb2 : 2 ≤ d-1 := by omega
  have hbc2 : (2 : ℝ) ≤ ((d-1 : ℕ) : ℝ) := by exact_mod_cast hb2
  have he2 := congrArg (fun x : ℝ => s (d-1)*x)
    (harmonicBudget_first_cost hbc2 (hz2 _ hb2) (hcap2 _ hb2))
  rw [twoRows_selected_prefix_eq s _ _ _ _ hd]
  unfold twoRowsHarmonicFirstCost
  rw [ite_eq_left hd]
  by_cases hd4 : 4 ≤ d
  · have hb3 : 2 ≤ d-2 := by omega
    have hbc3 : (2 : ℝ) ≤ ((d-2 : ℕ) : ℝ) := by exact_mod_cast hb3
    have he3 := congrArg (fun x : ℝ => s (d-2)*x)
      (harmonicRatio_first_cost (tripleHarmonicRatio_le_one hbc3) (hz3 _ hb3) (hcap3 _ hb3))
    simp only [ite_eq_left hd4,tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,
      harmonicThetaProfile,harmonicEtaProfile,harmonicLambdaProfile,tripleHarmonicLambdaProfile]
    linear_combination he2+he3
  · simp only [ite_eq_right hd4,harmonicThetaProfile,harmonicEtaProfile,harmonicLambdaProfile]
    linear_combination he2

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.twoRows_selected_prefix_eq
#print axioms KLS.DeterministicBridgeNext.tripleHarmonicThetaProfile_lt_one
