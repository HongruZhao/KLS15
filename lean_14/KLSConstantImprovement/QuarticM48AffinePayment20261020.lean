import KLSConstantImprovement.QuarticM48TrueCapBellman20261020Data
import KLSConstantImprovement.WeightedOrbitBellmanTail

/-! FixedM48 finite-affine payment for an arbitrary real budget B.
This copies the staged scalar proof through its actual payment conclusion,
retaining Z1 explicitly, before the endpoint contradiction. Root compiles. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.QuarticM48AffinePayment20261020
open KLSConstantImprovement.PositiveFiniteHeadBellman
open KLSConstantImprovement.ExactQuadraticCapBellmanCertificates
open KLSConstantImprovement.WeightedOrbitBellmanTail
open KLSConstantImprovement.QuarticM48TrueCapBellman20261020Data
open KLSConstantImprovement.QuarticM48Profile20261020Data
set_option maxHeartbeats 6500000
set_option backward.isDefEq.respectTransparency false

theorem affine_payment (Z c : ℕ → ℝ) (B : ℝ)
    (hZ : ∀ i,0 ≤ Z i) (hc : ∀ i,0 ≤ c i) (hZ0 : Z 0=1)
    (hzero : ∀ i,Z i=0 → Z (i+1)=0)
    (hrec : ∀ i,0 < Z i → 0 < Z (i+1) →
      Z (i+1)^2/Z i-c i ≤ Z (i+2))
    (hcap : ∀ i,c i ≤ A*Z i)
    (hupper : ∀ i,Z (i+1) ≤ ratioUpper*Z i)
    (hbudget : ∀ N,spend w c N ≤ B)
    (henv : ∀ ρ : ℝ,1 < ρ → ∃ M : ℝ,∀ i,Z i ≤ M*ρ^i) :
    Z 1*(line 0).positive (Z 1) ≤ B := by
  let r : ℕ → ℝ := fun i=>Z (i+1)/Z i
  have hr (i : ℕ) : 0 ≤ r i := div_nonneg (hZ _) (hZ _)
  have hrU (i : ℕ) : r i ≤ ratioUpper := by
    by_cases hz : Z i=0
    · simp only [r,hz,div_zero]
      exact ratioUpper_positive.le
    · have hp : 0 < Z i := lt_of_le_of_ne (hZ _) (Ne.symm hz)
      exact (div_le_iff₀ hp).mpr (hupper i)
  have hstage (i : ℕ) (hi : i < 47) :
      Z (i+1)*(line i).positive (r i) ≤
        w i*c i+Z (i+2)*(line (i+1)).positive (r (i+1)) := by
    by_cases hr1 : r i ≤ 1
    · rw [Affine.positive_zero (line i) (line_slope_nonneg i (by omega))
        (line_at_one i (by omega)) hr1,mul_zero]
      exact add_nonneg (mul_nonneg (stage_certificate i hi).weight_nonneg (hc i))
        (mul_nonneg (hZ _) (Affine.positive_nonneg _ _))
    have hr1' : 1 ≤ r i := (lt_of_not_ge hr1).le
    have hZi : 0 < Z i := by
      by_contra hn
      have hz : Z i=0 := le_antisymm (le_of_not_gt hn) (hZ _)
      have he : r i=0 := by simp [r,hz]
      linarith
    have hz : 0 < Z (i+1) := by
      have hp : 0 < r i := by linarith
      exact (div_pos_iff_of_pos_right hZi).mp hp
    let d : ℝ := c i/Z (i+1)
    have hd : 0 ≤ d := div_nonneg (hc _) hz.le
    have hdrop : r i-r (i+1) ≤ d := by
      have hh := div_le_div_of_nonneg_right (hrec i hZi hz) hz.le
      have he : (Z (i+1)^2/Z i-c i)/Z (i+1)=r i-d := by
        dsimp only [r,d]
        field_simp [ne_of_gt hz,ne_of_gt hZi]
      rw [he] at hh
      change r i-d ≤ r (i+1) at hh
      linarith
    have hdcap : d ≤ A/r i := by
      have hh := div_le_div_of_nonneg_right (hcap i) hz.le
      convert hh using 1 <;> dsimp only [r,d] <;>
        field_simp [ne_of_gt hz,ne_of_gt hZi] <;> ring
    have hh := transition_payment_of_exact_cap (stage_certificate i hi)
      A_nonneg (hZ (i+1)) hr1' (hr (i+1)) hd
      (hrU i) hdrop hdcap
    have hcd : Z (i+1)*d=c i := by
      dsimp only [d]
      field_simp
    have hzs : Z (i+1)*r (i+1)=Z (i+2) := by
      dsimp only [r]
      rw [show i+1+1=i+2 by omega]
      field_simp
    rwa [hcd,hzs] at hh
  have hh := finite_head_payment 47 w c (fun i=>Z (i+1)) r line
    (by
      intro i hi
      simpa only [Nat.add_assoc,Nat.reduceAdd] using hstage i hi)
  have ht : ∀ i,47 ≤ i → w i=tTail := by
    intro i hi
    exact t_eq_tail (i+2) (by omega)
  have hp := tail_payment Z c w 47 (by norm_num [tTail] : 0 < tTail)
    hZ hc hzero hrec ht hbudget henv
  have hterminal : (line 47).positive (r 47)=max 0 (tTail*(Z 48/Z 47-1)) := by
    unfold Affine.positive
    rw [terminal_line]
    simp only [Affine.eval,r]
    congr 1 <;> ring
  rw [hterminal] at hh
  change Z 1*(line 0).positive (r 0) ≤ spend w c 47+
    Z 48*max 0 (tTail*(Z 48/Z 47-1)) at hh
  have htotal : Z 1*(line 0).positive (Z 1) ≤ B := by
    have hr0 : r 0=Z 1 := by simp [r,hZ0]
    rw [hr0] at hh
    linarith
  exact htotal

end KLSConstantImprovement.QuarticM48AffinePayment20261020
#print axioms KLSConstantImprovement.QuarticM48AffinePayment20261020.affine_payment
