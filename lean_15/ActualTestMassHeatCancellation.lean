import ActualAppellEnergyEvolution
import ActualTiltHeatCancellation

/-! The actual squared test-function mass in the tilted law is smooth locally,
has its genuine one-sided damping derivative, and has zero heat generator
at an isotropic base law. Polynomial tests satisfy every required moment. -/
noncomputable section
open MeasureTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 def actualTestL2Field {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ)
    (s : ℝ) (z : Space n) : ℝ := ∫ x, (f x)^2 ∂actualDampedTiltLaw μ z s

 theorem actualDampedTiltLaw_zero_tilt {n : ℕ} (μ : Measure (Space n)) (s : ℝ) :
    actualDampedTiltLaw μ 0 s = μ.tilted (fun x => -s*(‖x‖^2/2)) := by
  unfold actualDampedTiltLaw
  congr 1
  funext x
  simp

 @[simp] theorem actualTestL2Field_zero {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (f : Space n → ℝ) :
    actualTestL2Field μ f 0 0 = ∫ x, (f x)^2 ∂μ := by
  unfold actualTestL2Field
  rw [actualDampedTiltLaw_zero_damping,exponentialTilt_zero]

 theorem contDiffAt_actualTestL2Field_theta {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) {f : Space n → ℝ}
    (hf : MemLp (fun x => (f x)^2) 2 μ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (actualTestL2Field μ f 0) 0 := by
  have he : actualTestL2Field μ f 0 = fun z => ∫ x, (f x)^2 ∂exponentialTilt μ z := by
    funext z
    unfold actualTestL2Field
    rw [actualDampedTiltLaw_zero_damping]
  rw [he]
  exact contDiffAt_normalized_tilt_average hLC hf

 theorem differentiableWithinAt_actualTestL2Field_damping {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) {f : Space n → ℝ}
    (hf : MemLp (fun x => (f x)^2) 2 μ) :
    DifferentiableWithinAt ℝ (fun s => actualTestL2Field μ f s 0) (Ici 0) 0 := by
  have he : (fun s => actualTestL2Field μ f s 0) =
      fun s => ∫ x, (f x)^2 ∂μ.tilted (fun x => -s*(‖x‖^2/2)) := by
    funext s
    unfold actualTestL2Field
    rw [actualDampedTiltLaw_zero_tilt]
  rw [he]
  exact (hasDerivWithinAt_quadratic_damping_average hLC hf).differentiableWithinAt

 theorem localHeatGenerator_actualTestL2Field {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) (hiso : IsIsotropic μ)
    {f : Space n → ℝ} (hf : MemLp (fun x => (f x)^2) 2 μ) :
    localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1)
      (actualTestL2Field μ f) = 0 := by
  have heθ : actualTestL2Field μ f 0 = fun z => ∫ x, (f x)^2 ∂exponentialTilt μ z := by
    funext z
    unfold actualTestL2Field
    rw [actualDampedTiltLaw_zero_damping]
  have hes : (fun s => actualTestL2Field μ f s 0) =
      fun s => ∫ x, (f x)^2 ∂μ.tilted (fun x => -s*(‖x‖^2/2)) := by
    funext s
    unfold actualTestL2Field
    rw [actualDampedTiltLaw_zero_tilt]
  unfold localHeatGenerator
  rw [heθ,hes]
  change actualHeatGenerator μ (fun x => (f x)^2) = 0
  exact actualHeatGenerator_eq_zero hLC hiso hf

 theorem polynomialEval_square_memLp {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) (p : MvPolynomial (Fin n) ℝ) :
    MemLp (fun x => (polynomialEval p x)^2) 2 μ := by
  have hp := polynomialEval_memLp_two hLC (p^2)
  convert hp using 1
  funext x
  change (MvPolynomial.eval (fun j => x j) p)^2 = MvPolynomial.eval (fun j => x j) (p^2)
  rw [map_pow]

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.localHeatGenerator_actualTestL2Field
#print axioms KLS.DeterministicBridgeNext.polynomialEval_square_memLp
