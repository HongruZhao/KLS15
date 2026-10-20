import ActualCovarianceHeatDrift
import ActualAppellFieldEvolution
import ActualAppellWhiteningEnergy
import LocalTensorMetricGenerator
import KLS.TensorEnergyCorrection

/-! Literal covariance-normalized Appell energy evolution (3.12), with
 the actual coefficient and covariance dynamics proved in preceding modules. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLS.TensorEnergy
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem localHeatGenerator_actualCovarianceField
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1)
      (actualCovarianceField μ) = -1 := by
  have hA := contDiffAt_actualCovarianceField_theta hμ
  have hAs := (hasDerivWithinAt_actualCovarianceField_damping_matrix hμ).differentiableWithinAt
  ext i j
  let L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ))
  have he := localHeatGenerator_compCLM L hA hAs
    (fun k : Fin n => EuclideanSpace.single k 1)
  change localHeatGenerator (fun k : Fin n => EuclideanSpace.single k 1)
      (fun s z => actualCovarianceField μ s z i j) =
    (localHeatGenerator (fun k : Fin n => EuclideanSpace.single k 1)
      (actualCovarianceField μ)) i j at he
  rw [← he]
  change actualCovarianceHeatGenerator μ i j = (-1 : Matrix (Fin n) (Fin n) ℝ) i j
  exact congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j)
    (actualCovarianceHeatGenerator_eq_neg_one hμ)

 theorem localHeatGenerator_actualAppellField
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (d : ℕ) :
    localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1)
      (actualAppellField μ f d) =
      -((d : ℝ) • actualAppellCoefficient μ f d+actualAppellLowerDriftTensor μ f d) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hT := contDiffAt_actualAppellField_theta hμ.logConcave hf d
  have hTs := (hasDerivWithinAt_actualAppellField_damping hμ.logConcave hf d).differentiableWithinAt
  have he : localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1)
      (actualAppellField μ f d) = actualAppellFieldHeatGenerator μ f d := by
    funext a
    have ha := localHeatGenerator_compCLM (ContinuousLinearMap.proj a) hT hTs
      (fun i : Fin n => EuclideanSpace.single i 1)
    exact ha.symm
  rw [he,actualAppellFieldHeatGenerator_eq_drift hμ hf]

 theorem fderiv_actualAppellField
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (i : Fin n) :
    fderiv ℝ (actualAppellField μ f d 0) 0 (EuclideanSpace.single i 1) =
      fun a => actualAppellCoefficient μ f (d+1) (Fin.cons i a) := by
  have hd := (contDiffAt_actualAppellField_theta hLC hf d).differentiableAt (by simp)
  funext a
  rw [← fderiv_vector_entry hd a]
  exact coordinateDerivative_actualAppellField hLC hf d a i

 theorem actualAppellEnergy_eq_dotProduct (μ : Measure (Space n)) (f : Space n → ℝ) (d : ℕ) :
    actualAppellEnergy μ f d = actualAppellCoefficient μ f d ⬝ᵥ actualAppellCoefficient μ f d := by
  simp only [actualAppellEnergy,dotProduct,pow_two]

 theorem contDiffAt_actualCovarianceAppellEnergy_theta
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (d : ℕ) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z => actualCovarianceAppellEnergy (actualDampedTiltLaw μ z 0) f d) 0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  change ContDiffAt ℝ (⊤ : ℕ∞)
    (fun z => tensorMetric (actualCovarianceField μ 0 z) (actualAppellField μ f d 0 z)) 0
  apply contDiffAt_tensorMetric (contDiffAt_actualCovarianceField_theta hμ) _
    (contDiffAt_actualAppellField_theta hμ.logConcave hf d)
  rw [actualCovarianceField_zero hμ]
  simp

 theorem differentiableWithinAt_actualCovarianceAppellEnergy_damping
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (d : ℕ) :
    DifferentiableWithinAt ℝ
      (fun s => actualCovarianceAppellEnergy (actualDampedTiltLaw μ 0 s) f d) (Ici 0) 0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  exact (hasDerivWithinAt_tensorMetric_at_identity
    (hasDerivWithinAt_actualCovarianceField_damping_matrix hμ)
    (hasDerivWithinAt_actualAppellField_damping hμ.logConcave hf d)
    (actualCovarianceField_zero hμ)).differentiableWithinAt

 /-- Literal full-class energy evolution (3.12). Every covariance, Appell
 and one-sided family derivative in this theorem has been derived from
 the genuine normalized tilted law. -/
 theorem actualCovarianceAppellEnergy_generator_exact
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (d : ℕ) :
    localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1)
      (fun s z => actualCovarianceAppellEnergy (actualDampedTiltLaw μ z s) f d) =
      -(d : ℝ)*actualAppellEnergy μ f d-
        2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)+
        ∑ i : Fin n, energyNoiseCorrection (actualAppellCoefficient μ f d)
          (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
          (fun a => actualAppellCoefficient μ f (d+1) (Fin.cons i a)) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hh := localHeatGenerator_tensorMetric_with_drift
    (contDiffAt_actualCovarianceField_theta hμ)
    (contDiffAt_actualAppellField_theta hμ.logConcave hf d)
    (hasDerivWithinAt_actualCovarianceField_damping_matrix hμ).differentiableWithinAt
    (hasDerivWithinAt_actualAppellField_damping hμ.logConcave hf d).differentiableWithinAt
    (fun i : Fin n => EuclideanSpace.single i 1) (actualCovarianceField_zero hμ)
    (fun i => by rw [fderiv_actualCovarianceField hμ]; exact (thirdCumulantMatrix_isSymm _ _).eq)
    (d : ℝ) (actualAppellLowerDriftTensor μ f d)
    (localHeatGenerator_actualCovarianceField hμ)
    (by simpa only [actualAppellField_zero] using localHeatGenerator_actualAppellField hμ hf d)
  simp only [actualAppellField_zero,fderiv_actualCovarianceField hμ,
    fderiv_actualAppellField hμ.logConcave hf d] at hh
  have hc : (d : ℝ)-2*(d : ℝ) = -(d : ℝ) := by ring
  rw [hc,← actualAppellEnergy_eq_dotProduct] at hh
  exact hh

 theorem actualAppell_next_slices_square (μ : Measure (Space n)) (f : Space n → ℝ) (d : ℕ) :
    (∑ i : Fin n,
      (fun a => actualAppellCoefficient μ f (d+1) (Fin.cons i a)) ⬝ᵥ
        (fun a => actualAppellCoefficient μ f (d+1) (Fin.cons i a))) =
      actualAppellEnergy μ f (d+1) := by
  rw [actualAppellEnergy_eq_dotProduct]
  unfold dotProduct
  have hh := (Fin.consEquiv (fun _ : Fin (d+1) => Fin n)).sum_comp
    (fun a => actualAppellCoefficient μ f (d+1) a*actualAppellCoefficient μ f (d+1) a)
  have he (i : Fin n) (a : Fin d → Fin n) :
      (Fin.consEquiv (fun _ : Fin (d+1) => Fin n)) (i,a) = Fin.cons i a := rfl
  simpa only [Fintype.sum_prod_type,he] using hh

 /-- Literal (3.14), using the already-proved universal actual two-slot
 third-moment bound. No matrix seed or energy evolution premise remains. -/
 theorem actualCovarianceAppellEnergy_generator_lower
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (d : ℕ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    β*actualAppellEnergy μ f (d+1)-
      ((4/(1-β)-2)*(d : ℝ)^2+((4/(1-β)-2)-3)*(d : ℝ))*actualAppellEnergy μ f d-
      2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d) ≤
    localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1)
      (fun s z => actualCovarianceAppellEnergy (actualDampedTiltLaw μ z s) f d) := by
  have hn := actualAppell_noiseCorrection_lower hμ hf
    (fun i a => actualAppellCoefficient μ f (d+1) (Fin.cons i a)) hβ0 hβ1
  rw [actualAppell_next_slices_square,← actualAppellEnergy_eq_dotProduct] at hn
  rw [actualCovarianceAppellEnergy_generator_exact hμ hf d]
  linarith

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualCovarianceAppellEnergy_generator_exact
#print axioms KLS.DeterministicBridgeIntegration.actualCovarianceAppellEnergy_generator_lower
#print axioms KLS.DeterministicBridgeIntegration.contDiffAt_actualCovarianceAppellEnergy_theta
#print axioms KLS.DeterministicBridgeIntegration.differentiableWithinAt_actualCovarianceAppellEnergy_damping
