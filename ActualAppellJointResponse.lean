import ActualAppellMultiplication
import ActualRetainedSquareEnergy

/-! Literal first law variation of the polarized covariance Appell energy,
and its cancellation against the x_i g test variation at a joint maximum.
This identifies the law-test Hessian response but does not bound its size. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.TensorEnergy KLS.DeterministicBridgeNext KLS.MatrixCalculus
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 def actualCovarianceAppellPairing (μ : Measure (Space n))
    (f g : Space n → ℝ) (d : ℕ) : ℝ :=
  actualAppellCoefficient μ f d ⬝ᵥ
    (tensorMatrix (covarianceMatrix μ)⁻¹ *ᵥ actualAppellCoefficient μ g d)

 theorem contDiffAt_actualCovarianceAppellPairing_theta
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f g : Space n → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (d : ℕ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => actualCovarianceAppellPairing
      (actualDampedTiltLaw μ z 0) f g d) 0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hA := contDiffAt_actualCovarianceField_theta hμ
  have hT := contDiffAt_actualAppellField_theta hμ.logConcave hf d
  have hS := contDiffAt_actualAppellField_theta hμ.logConcave hg d
  have hQ := contDiffAt_tensorInverse (r := d) hA
    (show (actualCovarianceField μ 0 0).det ≠ 0 by rw [actualCovarianceField_zero hμ]; simp)
  change ContDiffAt ℝ (⊤ : ℕ∞) (fun z => actualAppellField μ f d 0 z ⬝ᵥ
    (tensorMatrix (actualCovarianceField μ 0 z)⁻¹ *ᵥ actualAppellField μ g d 0 z)) 0
  unfold Matrix.mulVec dotProduct
  apply ContDiffAt.sum
  intro a _
  apply (contDiffAt_pi.mp hT a).mul
  apply ContDiffAt.sum
  intro b _
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp hQ a) b).mul (contDiffAt_pi.mp hS b)

 theorem fderiv_actualCovarianceAppellPairing
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f g : Space n → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (d : ℕ) (i : Fin n) :
    fderiv ℝ (fun z => actualCovarianceAppellPairing
      (actualDampedTiltLaw μ z 0) f g d) 0 (EuclideanSpace.single i 1) =
      (fun a => actualAppellCoefficient μ f (d+1) (Fin.cons i a)) ⬝ᵥ
        actualAppellCoefficient μ g d+
      actualAppellCoefficient μ f d ⬝ᵥ
        (fun a => actualAppellCoefficient μ g (d+1) (Fin.cons i a))-
      actualAppellSlotResponse μ f d i ⬝ᵥ actualAppellCoefficient μ g d := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let A := actualCovarianceField μ 0
  let T := actualAppellField μ f d 0
  let S := actualAppellField μ g d 0
  have hA := (contDiffAt_actualCovarianceField_theta hμ).differentiableAt (by simp)
  have hT := (contDiffAt_actualAppellField_theta hμ.logConcave hf d).differentiableAt (by simp)
  have hS := (contDiffAt_actualAppellField_theta hμ.logConcave hg d).differentiableAt (by simp)
  have hI : A 0 = 1 := actualCovarianceField_zero hμ
  have hdet : (A 0).det ≠ 0 := by simp [hI]
  have hInv : DifferentiableAt ℝ (fun y => (A y)⁻¹) 0 :=
    (differentiableAt_matrix_inv (A 0) hdet).comp 0 hA
  have hQ : DifferentiableAt ℝ (fun y => tensorMatrix (r := d) (A y)⁻¹) 0 :=
    differentiableAt_tensorMatrixFamily (fun _ => hInv)
  change fderiv ℝ (fun z => T z ⬝ᵥ (tensorMatrix (A z)⁻¹ *ᵥ S z))
    0 (EuclideanSpace.single i 1) = _
  rw [fderiv_dotProduct_apply hT (differentiableAt_mulVec hQ hS),
    fderiv_mulVec_apply hQ hS,fderiv_tensorInverse_at_identity hA hI]
  simp only [hI,inv_one,tensorMatrix_one,Matrix.one_mulVec,Matrix.neg_mulVec,
    dotProduct_add,dotProduct_neg]
  change _ = _
  rw [actualAppellField_zero,actualAppellField_zero,
    fderiv_actualAppellField hμ.logConcave hf,
    fderiv_actualAppellField hμ.logConcave hg,fderiv_actualCovarianceField hμ]
  have hsym : (tensorSlotSum (r := d)
      (thirdCumulantMatrix μ (MomentMap.coordinateVector i))).transpose =
      tensorSlotSum (thirdCumulantMatrix μ (MomentMap.coordinateVector i)) := by
    rw [tensorSlotSum_transpose,(thirdCumulantMatrix_isSymm _ _).eq]
  rw [← hsym,Matrix.dotProduct_transpose_mulVec]
  rw [dotProduct_comm (actualAppellCoefficient μ g d)]
  unfold actualAppellSlotResponse
  ring

 theorem fderiv_actualCovarianceAppellEnergy
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (d : ℕ) (i : Fin n) :
    fderiv ℝ (fun z => actualCovarianceAppellEnergy
      (actualDampedTiltLaw μ z 0) f d) 0 (EuclideanSpace.single i 1) =
      2*(actualAppellCoefficient μ f d ⬝ᵥ
        (fun a => actualAppellCoefficient μ f (d+1) (Fin.cons i a)))-
      actualAppellCoefficient μ f d ⬝ᵥ actualAppellSlotResponse μ f d i := by
  have hh := fderiv_actualCovarianceAppellPairing hμ hf hf d i
  change fderiv ℝ (fun z => actualCovarianceAppellEnergy
    (actualDampedTiltLaw μ z 0) f d) 0 (EuclideanSpace.single i 1) = _ at hh
  rw [dotProduct_comm (fun a => actualAppellCoefficient μ f (d+1) (Fin.cons i a))
    (actualAppellCoefficient μ f d),dotProduct_comm (actualAppellSlotResponse μ f d i)
    (actualAppellCoefficient μ f d)] at hh
  linarith

 def actualAppellCoordinateLowerTensor (μ : Measure (Space n)) (f : Space n → ℝ)
    (d : ℕ) (i : Fin n) : (Fin d → Fin n) → ℝ :=
  fun a => actualAppellCoordinateLower μ f i (fun j => EuclideanSpace.single (a j) 1)

 theorem actualAppell_joint_response_factorization
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f g : Space n → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (k : ℕ) (i : Fin n) (w lam : ℝ)
    (hstat : actualAppellCoefficient μ f (k+1) ⬝ᵥ
        actualAppellCoefficient μ (fun x => x i*g x) (k+1)+
      w*(actualAppellCoefficient μ f k ⬝ᵥ
        actualAppellCoefficient μ (fun x => x i*g x) k) =
      lam*(∫ x, x i*f x*g x ∂μ)) :
    fderiv ℝ (fun z => actualCovarianceAppellPairing
      (actualDampedTiltLaw μ z 0) f g (k+1)) 0 (EuclideanSpace.single i 1)+
    w*fderiv ℝ (fun z => actualCovarianceAppellPairing
      (actualDampedTiltLaw μ z 0) f g k) 0 (EuclideanSpace.single i 1)-
    lam*(∫ x, x i*f x*g x ∂μ) =
      ((fun a => actualAppellCoefficient μ f (k+2) (Fin.cons i a))-
        actualAppellSlotResponse μ f (k+1) i) ⬝ᵥ actualAppellCoefficient μ g (k+1)-
      actualAppellCoefficient μ f (k+1) ⬝ᵥ actualAppellCoordinateLowerTensor μ g (k+1) i+
      w*(((fun a => actualAppellCoefficient μ f (k+1) (Fin.cons i a))-
        actualAppellSlotResponse μ f k i) ⬝ᵥ actualAppellCoefficient μ g k-
        actualAppellCoefficient μ f k ⬝ᵥ actualAppellCoordinateLowerTensor μ g k i) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have he (d : ℕ) : actualAppellCoefficient μ (fun x => x i*g x) d =
      (fun a => actualAppellCoefficient μ g (d+1) (Fin.cons i a))+
        actualAppellCoordinateLowerTensor μ g d i := by
    funext a
    exact actualAppellCoefficient_coordinate_mul hμ.logConcave hg i a
  rw [he (k+1),he k,dotProduct_add,dotProduct_add] at hstat
  rw [fderiv_actualCovarianceAppellPairing hμ hf hg,
    fderiv_actualCovarianceAppellPairing hμ hf hg]
  simp only [sub_dotProduct]
  change _ = _
  linarith

 def actualAppellTangentPairing (μ : Measure (Space n)) (f g : Space n → ℝ)
    (k : ℕ) (w lam : ℝ) : ℝ :=
  actualCovarianceAppellPairing μ f g (k+1)+
    w*actualCovarianceAppellPairing μ f g k-lam*(∫ x, f x*g x ∂μ)

 theorem fderiv_actualAppellTangentPairing
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f g : Space n → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfg : MemLp (fun x => f x*g x) 2 μ) (k : ℕ) (i : Fin n) (w lam : ℝ) :
    fderiv ℝ (fun z => actualAppellTangentPairing
      (actualDampedTiltLaw μ z 0) f g k w lam) 0 (EuclideanSpace.single i 1) =
      fderiv ℝ (fun z => actualCovarianceAppellPairing
        (actualDampedTiltLaw μ z 0) f g (k+1)) 0 (EuclideanSpace.single i 1)+
      w*fderiv ℝ (fun z => actualCovarianceAppellPairing
        (actualDampedTiltLaw μ z 0) f g k) 0 (EuclideanSpace.single i 1)-
      lam*(∫ x, x i*f x*g x ∂μ) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hj := (contDiffAt_actualCovarianceAppellPairing_theta hμ hf hg (k+1)).differentiableAt (by simp)
  have hk := (contDiffAt_actualCovarianceAppellPairing_theta hμ hf hg k).differentiableAt (by simp)
  have hm := hasFDerivAt_normalized_tilt_average_zero_of_isotropic hμ.logConcave hμ.isotropic hfg
  have hmass : HasFDerivAt (fun z => ∫ x, f x*g x ∂actualDampedTiltLaw μ z 0)
      (∑ a, (∫ x, (f x*g x)*x a ∂μ) • (EuclideanSpace.proj a : Space n →L[ℝ] ℝ)) 0 := by
    simpa only [actualDampedTiltLaw_zero_damping] using hm
  have hd := (hj.hasFDerivAt.add (hk.hasFDerivAt.const_smul w)).sub (hmass.const_smul lam)
  have he := congrArg (fun L : Space n →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hd.fderiv
  change fderiv ℝ (fun z => actualAppellTangentPairing
    (actualDampedTiltLaw μ z 0) f g k w lam) 0 (EuclideanSpace.single i 1) = _ at he
  simp at he
  rw [he]
  congr 2
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

 theorem actualAppell_joint_response_top_degree
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f g : Space n → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfg : MemLp (fun x => f x*g x) 2 μ) (k : ℕ) (i : Fin n) (w lam : ℝ)
    (hzero : ∀ vs : List (Space n), vs.length < k+1 →
      directionalWordDerivative (actualDampedAverage μ g 0) vs 0 = 0)
    (hstat : actualAppellCoefficient μ f (k+1) ⬝ᵥ
        actualAppellCoefficient μ (fun x => x i*g x) (k+1)+
      w*(actualAppellCoefficient μ f k ⬝ᵥ
        actualAppellCoefficient μ (fun x => x i*g x) k) =
      lam*(∫ x, x i*f x*g x ∂μ)) :
    fderiv ℝ (fun z => actualAppellTangentPairing
      (actualDampedTiltLaw μ z 0) f g k w lam) 0 (EuclideanSpace.single i 1) =
      ((fun a => actualAppellCoefficient μ f (k+2) (Fin.cons i a))-
        actualAppellSlotResponse μ f (k+1) i) ⬝ᵥ actualAppellCoefficient μ g (k+1) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hBk := actualAppellCoefficient_zero_of_vanishing_words hμ.logConcave hg
    (Nat.lt_succ_self k) hzero
  have hLj : actualAppellCoordinateLowerTensor μ g (k+1) i = 0 := by
    funext a
    exact actualAppellCoordinateLower_zero_of_vanishing_words hμ.logConcave hμ.isotropic
      g i _ hzero
  have hLk : actualAppellCoordinateLowerTensor μ g k i = 0 := by
    funext a
    exact actualAppellCoordinateLower_zero_of_vanishing_words hμ.logConcave hμ.isotropic
      g i _ (fun vs hvs => hzero vs (by omega))
  rw [fderiv_actualAppellTangentPairing hμ hf hg hfg,
    actualAppell_joint_response_factorization hμ hf hg k i w lam hstat]
  simp only [hBk,hLj,hLk,dotProduct_zero,sub_zero,mul_zero,add_zero]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.contDiffAt_actualCovarianceAppellPairing_theta
#print axioms KLS.DeterministicBridgeIntegration.fderiv_actualCovarianceAppellPairing
#print axioms KLS.DeterministicBridgeIntegration.fderiv_actualCovarianceAppellEnergy
#print axioms KLS.DeterministicBridgeIntegration.actualAppell_joint_response_factorization
#print axioms KLS.DeterministicBridgeIntegration.fderiv_actualAppellTangentPairing
#print axioms KLS.DeterministicBridgeIntegration.actualAppell_joint_response_top_degree
