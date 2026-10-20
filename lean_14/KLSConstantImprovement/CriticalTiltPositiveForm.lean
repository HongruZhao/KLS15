import KLSConstantImprovement.ActualCubicQuadraticRegression
import Mathlib

/-! Local positive-form calculus and the ordered original cubic contraction.
These are finite/analytic components of the simultaneous-critical tilt proof.
The actual tilted covariance/cumulant derivative identification is still a
paper bridge; no all-law fifth identity is hidden in these declarations.
The author performs no builds or accepted-source edits. -/
noncomputable section
open Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology BigOperators
namespace KLSConstantImprovement.OriginalUpperRecovery6CriticalTilt
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
open ActualDeficitTensorBounds ActualCubicQuadraticRegression

theorem critical_nonnegative_derivative {f : ℝ → ℝ} {a : ℝ}
    (hpos : ∀ᶠ t in 𝓝 0, 0 ≤ f t) (hzero : f 0 = 0)
    (hd : HasDerivAt f a 0) : a = 0 := by
  have hm : IsLocalMin f 0 := by
    filter_upwards [hpos] with t ht
    simpa only [hzero] using ht
  exact hm.hasDerivAt_eq_zero hd

theorem critical_bilinear_derivative
    {a b c : ℝ → ℝ} {da db dc : ℝ}
    (hpos : ∀ s : ℝ, ∀ᶠ t in 𝓝 0, 0 ≤ a t+2*s*b t+s^2*c t)
    (ha : a 0 = 0) (hc : c 0 = 0)
    (hda : HasDerivAt a da 0) (hdb : HasDerivAt b db 0)
    (hdc : HasDerivAt c dc 0) : db = 0 := by
  have hp0 := (hpos 1).self_of_nhds
  have hm0 := (hpos (-1)).self_of_nhds
  have hb : b 0 = 0 := by
    rw [ha,hc] at hp0 hm0
    nlinarith
  have hp : da+2*db+dc = 0 := by
    apply critical_nonnegative_derivative (hpos 1)
    · simp [ha,hb,hc]
    · convert (hda.add (hdb.const_mul 2)).add hdc using 1 <;>
        norm_num <;> (try funext t) <;> (try simp only [Pi.add_apply]) <;> ring
  have hm : da-2*db+dc = 0 := by
    apply critical_nonnegative_derivative (hpos (-1))
    · simp [ha,hb,hc]
    · convert (hda.add (hdb.const_mul (-2))).add hdc using 1 <;>
        norm_num <;> (try funext t) <;> (try simp only [Pi.add_apply]) <;> ring
  linarith

def originalTiltDerivativeMain {n : ℕ} (μ : Measure (Space n))
    (T : Array3 (Fin n)) : ℝ :=
  4*tripleSum (fun i j k =>
    creation (actualThirdCubicArray μ) (symmetricAnnihilation μ T) i j k*T i j k)

theorem originalTiltDerivativeMain_eq_twelve {n : ℕ} (μ : Measure (Space n))
    (T : Array3 (Fin n))
    (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) :
    originalTiltDerivativeMain μ T =
      12*matrixFrobeniusSq (symmetricAnnihilation μ T) := by
  have hK : ∀ i j, symmetricAnnihilation μ T i j=symmetricAnnihilation μ T j i := by
    intro i j
    exact congrFun (congrFun (symmetricAnnihilation_isSymm μ T) j) i
  have hp := creation_pairing (actualThirdCubicArray μ) T
    (symmetricAnnihilation μ T) hT12 hT23 hK
  unfold originalTiltDerivativeMain
  rw [hp]
  simp only [symmetricAnnihilation,matrixFrobeniusSq,pow_two]
  ring

end KLSConstantImprovement.OriginalUpperRecovery6CriticalTilt
#print axioms KLSConstantImprovement.OriginalUpperRecovery6CriticalTilt.critical_nonnegative_derivative
#print axioms KLSConstantImprovement.OriginalUpperRecovery6CriticalTilt.critical_bilinear_derivative
#print axioms KLSConstantImprovement.OriginalUpperRecovery6CriticalTilt.originalTiltDerivativeMain_eq_twelve
