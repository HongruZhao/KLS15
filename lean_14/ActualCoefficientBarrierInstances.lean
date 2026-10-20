import ActualScalarTerminalNormalization
import ActualAppellRemainderBounds
import CubicSeedBarrier

/-! Actual scalar barriers for every coefficient induction step. The data
contain only scalar functions and proved scalar inequalities; no analytic
Appell estimate or maximum principle is postulated. -/
noncomputable section
open Set
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 structure CoefficientInductionBarrier (k : ℕ) (h : ℕ → ℝ) where
  phi : ℝ → ℝ
  alpha : ℝ
  continuous : ContinuousOn phi (Icc 0 1)
  positive : ∀ u ∈ Icc (0 : ℝ) 1, 0 < phi u
  antitone : AntitoneOn phi (Icc (0 : ℝ) 1)
  concave : ConcaveOn ℝ (Icc 0 1) phi
  hasDeriv : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt phi (deriv phi u) u
  derivative_negative : ∀ u ∈ Icc (0 : ℝ) 1, deriv phi u < 0
  zero : phi 0 = 1
  alpha_unit : alpha ∈ Ioo (0 : ℝ) 1
  criterion : ∀ u ∈ Icc (0 : ℝ) 1,
    (-deriv phi u/phi u)*(alpha*h (k+1)/h k*phi u-
      ((4/(1-alpha)-2)*(k : ℝ)^2+((4/(1-alpha)-2)-3)*k+2)*u-
      2*actualLowerConvolution h k/Real.sqrt (h k)*Real.sqrt u) >
      2*(k+1 : ℝ)^2-(k+1 : ℝ)+2+
        2*actualLowerConvolution h (k+1)/Real.sqrt (h (k+1)*phi u)

 theorem CoefficientInductionBarrier.q_positive {k : ℕ} {h : ℕ → ℝ}
    (b : CoefficientInductionBarrier k h) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 < -deriv b.phi u/b.phi u :=
  div_pos (neg_pos.mpr (b.derivative_negative u hu)) (b.positive u hu)

 theorem actualLowerConvolution_coefficientH (d : ℕ) :
    actualLowerConvolution Quintic24886.coefficientH d = Quintic24886.coefficientD d := rfl

 def cubicCoefficientInductionBarrier : CoefficientInductionBarrier 2 Quintic24886.coefficientH where
  phi := CubicSeedBarrier.phi
  alpha := CubicSeedBarrier.alpha
  continuous := fun u hu => (CubicSeedBarrier.contDiffAt_phi
    (CubicSeedBarrier.unit_in_domain hu)).continuousAt.continuousWithinAt
  positive := fun u hu => lt_trans (by norm_num) (CubicSeedBarrier.phi_range hu).1
  antitone := CubicSeedBarrier.strictAntiOn_phi.antitoneOn
  concave := CubicSeedBarrier.strictConcaveOn_phi.concaveOn
  hasDeriv := fun u hu => (CubicSeedBarrier.contDiffAt_phi
    (CubicSeedBarrier.unit_in_domain hu)).differentiableAt (by simp) |>.hasDerivAt
  derivative_negative := fun u hu => CubicSeedBarrier.derivative_negative (CubicSeedBarrier.unit_in_domain hu)
  zero := CubicSeedBarrier.phi_zero
  alpha_unit := CubicSeedBarrier.alpha_mem_unit
  criterion := by
    intro u hu
    have hc := CubicSeedBarrier.original_degree_three_criterion hu
    convert hc using 1 <;> norm_num only [actualLowerConvolution_coefficientH,
      CubicSeedBarrier.A_formula,CubicSeedBarrier.q,Nat.cast_ofNat] <;> ring

 def quinticCoefficientInductionBarrier (k : ℕ) (hk : 3 ≤ k) :
    CoefficientInductionBarrier k Quintic24886.coefficientH where
  phi := Quintic24886.phi
  alpha := Quintic24886.alpha
  continuous := Quintic24886.contDiffOn_phi.continuousOn
  positive := fun u hu => lt_of_lt_of_le (by norm_num) (Quintic24886.phi_branch_of_unit hu).1.1
  antitone := Quintic24886.phi_strictAntiOn.antitoneOn
  concave := Quintic24886.phi_strictConcaveOn.concaveOn
  hasDeriv := fun u hu => by
    have hd := Quintic24886.hasDerivAt_phi hu
    rwa [← hd.deriv] at hd
  derivative_negative := fun u hu => Quintic24886.deriv_phi_negative hu
  zero := Quintic24886.phi_zero
  alpha_unit := by norm_num [Quintic24886.alpha]
  criterion := by
    intro u hu
    have hc := Quintic24886.all_degree_scalar_criterion hk hu
    have hA : Quintic24886.A = 4/(1-Quintic24886.alpha)-2 := by
      norm_num [Quintic24886.A,Quintic24886.alpha]
    simpa only [actualLowerConvolution_coefficientH,Quintic24886.qPhi,hA] using hc

 theorem exists_coefficientInductionBarrier {k : ℕ} (hk : 2 ≤ k) :
    Nonempty (CoefficientInductionBarrier k Quintic24886.coefficientH) := by
  by_cases hk2 : k = 2
  · subst k
    exact ⟨cubicCoefficientInductionBarrier⟩
  · exact ⟨quinticCoefficientInductionBarrier k (by omega)⟩

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.cubicCoefficientInductionBarrier
#print axioms KLS.DeterministicBridgeNext.quinticCoefficientInductionBarrier
#print axioms KLS.DeterministicBridgeNext.exists_coefficientInductionBarrier
