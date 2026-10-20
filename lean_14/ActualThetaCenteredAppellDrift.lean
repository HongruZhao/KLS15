import ActualThetaWeightedAppellDrift
import ActualDegreeYoungAppellDrift

/-! Outgoing normalization and the genuine centered maximum drift bound
for the size-two refinement.  The extra neighbor charge is visible in the
quadratic head as well as every tail degree. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def thetaNeighborCharge (K : ℝ) (s theta eta : ℕ → ℝ) (b : ℕ) : ℝ :=
  theta (b+1)*(b : ℝ)*((b : ℝ)+2/3)/(K*(eta (b+1)*s b))

def thetaFirstCost (s theta eta : ℕ → ℝ) (d : ℕ) : ℝ :=
  properYoungPrefix s d - if 3 ≤ d then theta d*(2-theta d-eta d)*s (d-1) else 0

theorem triangleDegreePrefix_eq_proper (s : ℕ → ℝ) (d : ℕ) :
    triangleDegreePrefix s d = properYoungPrefix s d := by
  classical
  unfold triangleDegreePrefix properYoungPrefix
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

theorem thetaFirstCost_two (s theta eta : ℕ → ℝ) : thetaFirstCost s theta eta 2 = 0 := by
  norm_num [thetaFirstCost,properYoungPrefix]

theorem sum_previous_degree_le (N : ℕ) (F : ℕ → ℝ)
    (hF : ∀ b ∈ Finset.Icc 2 N, 0 ≤ F b) :
    (∑ d ∈ Finset.Icc 3 N, F (d-1)) ≤ ∑ b ∈ Finset.Icc 2 N, F b := by
  classical
  have hinj : Set.InjOn (fun d : ℕ => d-1) (Finset.Icc 3 N : Set ℕ) := by
    intro d hd e he hde
    simp only [Finset.mem_coe,Finset.mem_Icc] at hd he
    dsimp only at hde
    omega
  have hsub : (Finset.Icc 3 N).image (fun d : ℕ => d-1) ⊆ Finset.Icc 2 N := by
    intro b hb
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hb
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  calc
    _ = ∑ b ∈ (Finset.Icc 3 N).image (fun d : ℕ => d-1), F b :=
      (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b hb _ => hF b hb)

theorem actual_weighted_proper_drift_theta_degree_young_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ} (s theta eta : ℕ → ℝ)
    (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (htheta0 : ∀ d, 3 ≤ d → 0 ≤ theta d)
    (htheta1 : ∀ d, 3 ≤ d → theta d ≤ 1)
    (heta : ∀ d, 3 ≤ d → 0 < eta d) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ)) :
    2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) ≤
      (∑ d ∈ Finset.Icc 3 N, thetaFirstCost s theta eta d *
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) +
      ∑ b ∈ Finset.Icc 2 N, ((K*C/s b)*(b : ℝ)^2 + thetaNeighborCharge K s theta eta b) *
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b := by
  have h := actual_weighted_proper_drift_theta_young_le hμ hf s theta eta hK hs htheta0 htheta1 heta N hprevious
  have hcharge : (∑ d ∈ Finset.Icc 3 N,
      (theta d*((d : ℝ)-1)*((d : ℝ)-1/3)/(K*(eta d*s (d-1)))) *
        (K^(d-1)*((d-1).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-1)) ≤
      ∑ b ∈ Finset.Icc 2 N, thetaNeighborCharge K s theta eta b *
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b := by
    have he : (∑ d ∈ Finset.Icc 3 N,
        (theta d*((d : ℝ)-1)*((d : ℝ)-1/3)/(K*(eta d*s (d-1)))) *
          (K^(d-1)*((d-1).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-1)) =
        ∑ d ∈ Finset.Icc 3 N, thetaNeighborCharge K s theta eta (d-1) *
          (K^(d-1)*((d-1).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-1) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd3 := (Finset.mem_Icc.mp hd).1
      have he : d-1+1 = d := by omega
      have hc : ((d-1 : ℕ) : ℝ) = (d : ℝ)-1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ d)]
        norm_num
      unfold thetaNeighborCharge
      rw [he,hc]
      ring
    rw [he]
    apply sum_previous_degree_le N (fun b => thetaNeighborCharge K s theta eta b *
      (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b)
    intro b hb
    have hb2 := (Finset.mem_Icc.mp hb).1
    have ht := htheta0 (b+1) (by omega)
    have hs' := hs b hb2
    have he := heta (b+1) (by omega)
    have hbc : (0 : ℝ) ≤ b := by positivity
    unfold thetaNeighborCharge
    exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg ht hbc)
      (by positivity)) (mul_pos hK (mul_pos he hs')).le) (by positivity))
      (actualAppellEnergy_nonneg _ _ _)
  have hfirst : (∑ d ∈ Finset.Icc 3 N,
      (triangleDegreePrefix s d-theta d*(2-theta d-eta d)*s (d-1)) *
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) =
      ∑ d ∈ Finset.Icc 3 N, thetaFirstCost s theta eta d *
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [triangleDegreePrefix_eq_proper]
    simp only [thetaFirstCost,ite_eq_left (Finset.mem_Icc.mp hd).1]
  rw [hfirst] at h
  have he : (∑ b ∈ Finset.Icc 2 N, ((K*C/s b)*(b : ℝ)^2 + thetaNeighborCharge K s theta eta b) *
      (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b) =
      (∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(b : ℝ)^2 *
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b) +
      ∑ b ∈ Finset.Icc 2 N, thetaNeighborCharge K s theta eta b *
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [he]
  linarith

theorem actual_weighted_centered_full_drift_theta_young_le
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖ = 1) {K C : ℝ} (s theta eta : ℕ → ℝ)
    (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (htheta0 : ∀ d, 3 ≤ d → 0 ≤ theta d)
    (htheta1 : ∀ d, 3 ≤ d → theta d ≤ 1)
    (heta : ∀ d, 3 ≤ d → 0 < eta d) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ))
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N =
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell) :
    2*(∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)) -
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤
      actualWeightedAppellEnergy μ f K N +
      (∑ d ∈ Finset.Icc 3 N, thetaFirstCost s theta eta d *
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) +
      ∑ b ∈ Finset.Icc 2 N, ((K*C/s b)*(b : ℝ)^2 + thetaNeighborCharge K s theta eta b) *
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b := by
  have ht := actual_weighted_terminal_eq hμ f K N hstat
  have hb : actualAppellEnergy μ f 1 ≤ 1 := by
    rw [actualAppellEnergy_eq_norm_sq]
    simpa only [hunit,one_pow] using fullClassAppellTensor_one_norm_sq_le hμ.logConcave hμ.isotropic f
  have hM := actualWeightedAppellEnergy_nonneg μ f hK N
  have hMb := mul_le_of_le_one_right hM hb
  have hp := actual_weighted_proper_drift_theta_degree_young_le hμ (Lp.memLp f)
    s theta eta hK hs htheta0 htheta1 heta N hprevious
  rw [actual_weighted_proper_drift_sum_eq f K N] at hp
  have he : (∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)) =
      (∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellCoefficient μ
          (fun x => inner ℝ x (affineProjectionVector hμ.isotropic f)) d)) +
      ∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f
      (Finset.mem_Icc.mp hd).1,dotProduct_add]
    ring
  rw [he]
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_weighted_proper_drift_theta_degree_young_le
#print axioms KLS.DeterministicBridgeNext.actual_weighted_centered_full_drift_theta_young_le
