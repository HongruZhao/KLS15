import DegreeWeightedTriangleYoung

/-! Extracting a fraction of the size-two contraction changes the first
Young cost by its squared coefficient.  The second-factor joint budget
is retained in full. -/
noncomputable section
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def thetaTriangleCoefficient (theta : ℕ → ℝ) (d a : ℕ) : ℝ :=
  if a = 2 then 1 - theta d else 1

def thetaDegreePrefix (s theta : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 2 (d-1), s (d-a+1) * (thetaTriangleCoefficient theta d a)^2

theorem thetaDegreePrefix_eq (s theta : ℕ → ℝ) {d : ℕ} (hd : 3 ≤ d) :
    thetaDegreePrefix s theta d =
      (∑ a ∈ Finset.Icc 2 (d-1), s (d-a+1)) -
        theta d * (2-theta d) * s (d-1) := by
  classical
  have hmem : 2 ∈ Finset.Icc 2 (d-1) := by simp only [Finset.mem_Icc]; omega
  have he : (∑ a ∈ Finset.Icc 2 (d-1), s (d-a+1) *
      (thetaTriangleCoefficient theta d a)^2) =
      ∑ a ∈ Finset.Icc 2 (d-1), (s (d-a+1) -
        if a = 2 then theta d * (2-theta d) * s (d-1) else 0) := by
    apply Finset.sum_congr rfl
    intro a ha
    by_cases ha2 : a = 2
    · subst a
      have hsub : d-2+1 = d-1 := by omega
      simp only [thetaTriangleCoefficient,ite_true,hsub]
      ring
    · simp [thetaTriangleCoefficient,ha2]
  unfold thetaDegreePrefix
  rw [he,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq',hmem,ite_true]

theorem coupled_triangle_theta_weighted_young (N : ℕ) (P : ℕ → ℝ)
    (Q : ℕ → ℕ → ℝ) (s theta : ℕ → ℝ) {C K : ℝ}
    (hK : 0 ≤ K) (hs : ∀ b ∈ Finset.Icc 2 N, 0 < s b)
    (hjoint : ∀ b ∈ Finset.Icc 2 N,
      (∑ a ∈ Finset.Icc 2 (N-1), (Q a b)^2) ≤ C*(P b)^2) :
    2*Real.sqrt K*(∑ d ∈ Finset.Icc 3 N, ∑ a ∈ Finset.Icc 2 (d-1),
      thetaTriangleCoefficient theta d a * (P d/(d : ℝ)) * Q a (d-a+1)) ≤
      (∑ d ∈ Finset.Icc 3 N, thetaDegreePrefix s theta d * (P d/(d : ℝ))^2) +
        ∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(P b)^2 := by
  classical
  have hp : ∀ p ∈ coupledDriftPairs N, p.1-p.2+1 ∈ Finset.Icc 2 N := by
    intro p hp
    obtain ⟨hd,ha⟩ := Finset.mem_sigma.mp hp
    simp only [Finset.mem_Icc] at hd ha ⊢
    omega
  have hy := Finset.sum_le_sum (s := coupledDriftPairs N) (fun p hmem =>
    sqrt_weighted_young hK (hs _ (hp p hmem))
      (thetaTriangleCoefficient theta p.1 p.2 * (P p.1/(p.1 : ℝ)))
      (Q p.2 (p.1-p.2+1)))
  have he : (∑ p ∈ coupledDriftPairs N,
      2*Real.sqrt K*(thetaTriangleCoefficient theta p.1 p.2 *
        (P p.1/(p.1 : ℝ))) * Q p.2 (p.1-p.2+1)) =
      2*Real.sqrt K*(∑ d ∈ Finset.Icc 3 N, ∑ a ∈ Finset.Icc 2 (d-1),
        thetaTriangleCoefficient theta d a * (P d/(d : ℝ)) * Q a (d-a+1)) := by
    rw [coupledDriftPairs,Finset.sum_sigma,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hf : (∑ p ∈ coupledDriftPairs N, s (p.1-p.2+1) *
      (thetaTriangleCoefficient theta p.1 p.2 * (P p.1/(p.1 : ℝ)))^2) =
      ∑ d ∈ Finset.Icc 3 N, thetaDegreePrefix s theta d * (P d/(d : ℝ))^2 := by
    rw [coupledDriftPairs,Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro d hd
    unfold thetaDegreePrefix
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [he,Finset.sum_add_distrib,hf] at hy
  have hj := coupled_triangle_second_factor_weighted N P Q (fun b => K/s b)
    (fun b hb => div_nonneg hK (hs b hb).le) hjoint
  have hj' : (∑ p ∈ coupledDriftPairs N,
      (K/s (p.1-p.2+1))*(Q p.2 (p.1-p.2+1))^2) ≤
      ∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(P b)^2 := by
    convert hj using 1
    apply Finset.sum_congr rfl
    intro b hb
    ring
  exact hy.trans (add_le_add le_rfl hj')

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.thetaDegreePrefix_eq
#print axioms KLS.DeterministicBridgeNext.coupled_triangle_theta_weighted_young
