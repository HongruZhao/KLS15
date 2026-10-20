import ActualAppellJointResponse
import ActualEnergyQuotientMaximum
import JointMaximumSchur

/-! Genuine joint law/test variations of the constructed all-law/all-L2
maximum. The law is the actual normalized tilt, its covariance metric
includes whitening, and the test may have arbitrary polynomial degree. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped ContDiff Topology BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25 KLS.TensorEnergy
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

 theorem actualCovarianceAppellPairing_symm (μ : Measure (Space n))
    (f g : Space n → ℝ) (d : ℕ) :
    actualCovarianceAppellPairing μ f g d=actualCovarianceAppellPairing μ g f d := by
  have hs : (tensorMatrix (r := d) (covarianceMatrix μ)⁻¹).transpose=
      tensorMatrix (covarianceMatrix μ)⁻¹ := by
    rw [← tensorMatrix_transpose,(covarianceMatrix_posSemidef μ).isHermitian.inv.isSymm.eq]
  unfold actualCovarianceAppellPairing
  simpa only [hs] using Matrix.dotProduct_transpose_mulVec
    (tensorMatrix (r := d) (covarianceMatrix μ)⁻¹)
    (actualAppellCoefficient μ f d) (actualAppellCoefficient μ g d)


 theorem actualAppellCoefficient_add_scaled_test {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f g : Space n → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (t : ℝ) (d : ℕ) (a : Fin d → Fin n) :
    actualAppellCoefficient μ (fun x => f x+t*g x) d a=
      actualAppellCoefficient μ f d a+t*actualAppellCoefficient μ g d a := by
  have he : (fun x => f x+t*g x)=(fun x => f x-(-t)*g x) := by funext x;ring
  rw [he,actualAppellCoefficient_sub hLC hf (hg.const_mul (-t)),
    actualAppellCoefficient_const_mul hLC hg]
  ring

 theorem actualCovarianceAppellEnergy_add_scaled_test {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f g : Space n → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (t : ℝ) (d : ℕ) :
    actualCovarianceAppellEnergy μ (fun x => f x+t*g x) d=
      actualCovarianceAppellEnergy μ f d+2*t*actualCovarianceAppellPairing μ f g d+
        t^2*actualCovarianceAppellEnergy μ g d := by
  have he : actualAppellCoefficient μ (fun x => f x+t*g x) d=
      actualAppellCoefficient μ f d+t • actualAppellCoefficient μ g d := by
    funext a
    exact actualAppellCoefficient_add_scaled_test hLC hf hg t d a
  unfold actualCovarianceAppellEnergy tensorMetric
  rw [he]
  simp only [Matrix.mulVec_add,Matrix.mulVec_smul,dotProduct_add,add_dotProduct,
    dotProduct_smul,smul_dotProduct,smul_eq_mul]
  have hs := actualCovarianceAppellPairing_symm μ f g d
  unfold actualCovarianceAppellPairing at hs
  unfold actualCovarianceAppellPairing
  rw [hs]
  change actualAppellCoefficient μ f d ⬝ᵥ
      (tensorMatrix (covarianceMatrix μ)⁻¹ *ᵥ actualAppellCoefficient μ f d)+
      t*(actualAppellCoefficient μ g d ⬝ᵥ
        (tensorMatrix (covarianceMatrix μ)⁻¹ *ᵥ actualAppellCoefficient μ f d))+
      t*((actualAppellCoefficient μ g d ⬝ᵥ
        (tensorMatrix (covarianceMatrix μ)⁻¹ *ᵥ actualAppellCoefficient μ f d))+
        t*(actualAppellCoefficient μ g d ⬝ᵥ
          (tensorMatrix (covarianceMatrix μ)⁻¹ *ᵥ actualAppellCoefficient μ g d))) =
      actualAppellCoefficient μ f d ⬝ᵥ
        (tensorMatrix (covarianceMatrix μ)⁻¹ *ᵥ actualAppellCoefficient μ f d)+
      2*t*(actualAppellCoefficient μ g d ⬝ᵥ
        (tensorMatrix (covarianceMatrix μ)⁻¹ *ᵥ actualAppellCoefficient μ f d))+
      t^2*(actualAppellCoefficient μ g d ⬝ᵥ
        (tensorMatrix (covarianceMatrix μ)⁻¹ *ᵥ actualAppellCoefficient μ g d))
  ring

 theorem actual_test_mass_add_scaled {μ : Measure (Space n)}
    {f g : Space n → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (t : ℝ) :
    (∫ x, (f x+t*g x)^2 ∂μ)=(∫ x, (f x)^2 ∂μ)+
      2*t*(∫ x, f x*g x ∂μ)+t^2*(∫ x, (g x)^2 ∂μ) := by
  have he : (fun x => (f x+t*g x)^2)=
      (fun x => (f x)^2+2*t*(f x*g x)+t^2*(g x)^2) := by funext x;ring
  rw [he]
  have hfg : Integrable (fun x => f x*g x) μ := by
    convert hf.integrable_mul hg using 1
  have h1 : Integrable (fun x => (f x)^2+2*t*(f x*g x)) μ :=
    hf.integrable_sq.add (hfg.const_mul (2*t))
  rw [integral_add h1 ((hg.integrable_sq).const_mul (t^2)),
    integral_add hf.integrable_sq (hfg.const_mul (2*t)),
    integral_const_mul,integral_const_mul]


 def actualJointTangentQuadratic (μ : Measure (Space n))
    (f g : Space n → ℝ) (k : ℕ) (w lam : ℝ) (z : Space n × ℝ) : ℝ :=
  actualAppellTangentPairing (actualDampedTiltLaw μ z.1 0) f f k w lam+
    2*z.2*actualAppellTangentPairing (actualDampedTiltLaw μ z.1 0) f g k w lam+
      z.2^2*actualAppellTangentPairing (actualDampedTiltLaw μ z.1 0) g g k w lam

 theorem actualJointTangentQuadratic_eq {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f g : Space n → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (t : ℝ) (w lam : ℝ) :
    actualAppellTangentPairing μ f f k w lam+
      2*t*actualAppellTangentPairing μ f g k w lam+
        t^2*actualAppellTangentPairing μ g g k w lam=
      actualCovarianceAppellEnergy μ (fun x => f x+t*g x) (k+1)+
        w*actualCovarianceAppellEnergy μ (fun x => f x+t*g x) k-
          lam*(∫ x, (f x+t*g x)^2 ∂μ) := by
  rw [actualCovarianceAppellEnergy_add_scaled_test hLC hf hg,
    actualCovarianceAppellEnergy_add_scaled_test hLC hf hg,
    actual_test_mass_add_scaled hf hg]
  simp only [actualAppellTangentPairing,actualCovarianceAppellPairing,
    actualCovarianceAppellEnergy,tensorMetric,pow_two]
  ring

 theorem contDiffAt_actualAppellTangentPairing_theta {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f g : Space n → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfg : MemLp (fun x => f x*g x) 2 μ) (k : ℕ) (w lam : ℝ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => actualAppellTangentPairing
      (actualDampedTiltLaw μ z 0) f g k w lam) 0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hm : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z => ∫ x, f x*g x ∂actualDampedTiltLaw μ z 0) 0 := by
    simpa only [actualDampedTiltLaw_zero_damping] using
      contDiffAt_normalized_tilt_average hμ.logConcave hfg
  exact ((contDiffAt_actualCovarianceAppellPairing_theta hμ hf hg (k+1)).add
    (contDiffAt_const.mul (contDiffAt_actualCovarianceAppellPairing_theta hμ hf hg k))).sub
      (contDiffAt_const.mul hm)

 theorem polynomialEval_mul_memLp_two {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (p q : MvPolynomial (Fin n) ℝ) :
    MemLp (fun x => polynomialEval p x*polynomialEval q x) 2 μ := by
  convert polynomialEval_memLp_two hLC (p*q) using 1
  funext x
  simp [polynomialEval]

 theorem contDiffAt_actualJointTangentQuadratic {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (p q : MvPolynomial (Fin n) ℝ)
    (k : ℕ) (w lam : ℝ) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (actualJointTangentQuadratic μ (polynomialEval p) (polynomialEval q) k w lam) 0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hp := polynomialEval_memLp_two hμ.logConcave p
  have hq := polynomialEval_memLp_two hμ.logConcave q
  have hpp := contDiffAt_actualAppellTangentPairing_theta hμ hp hp
    (polynomialEval_mul_memLp_two hμ.logConcave p p) k w lam
  have hpq := contDiffAt_actualAppellTangentPairing_theta hμ hp hq
    (polynomialEval_mul_memLp_two hμ.logConcave p q) k w lam
  have hqq := contDiffAt_actualAppellTangentPairing_theta hμ hq hq
    (polynomialEval_mul_memLp_two hμ.logConcave q q) k w lam
  exact ((hpp.comp (0 : Space n × ℝ) contDiffAt_fst).add
    (((contDiffAt_const (c := (2 : ℝ))).mul contDiffAt_snd).mul
      (hpq.comp (0 : Space n × ℝ) contDiffAt_fst))).add
        ((contDiffAt_snd.pow 2).mul (hqq.comp (0 : Space n × ℝ) contDiffAt_fst))

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualCovarianceAppellPairing_symm
#print axioms KLS.DeterministicBridgeNext.actualCovarianceAppellEnergy_add_scaled_test
#print axioms KLS.DeterministicBridgeNext.actualJointTangentQuadratic_eq
#print axioms KLS.DeterministicBridgeNext.contDiffAt_actualJointTangentQuadratic
