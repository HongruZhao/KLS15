import BoundedDegreePolynomialPairs

/-! Joint continuity of actual polynomial weighted moments as both the
admissible law and the finite coefficient vector vary. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal BigOperators
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 def coordinateWordPolynomial {n d : ℕ} (a : Fin d → Fin n) : MvPolynomial (Fin n) ℝ :=
  ∏ j, MvPolynomial.X (a j)

 theorem polynomialEval_coordinateWord {n d : ℕ} (a : Fin d → Fin n) (x : Space n) :
    polynomialEval (coordinateWordPolynomial a) x = ∏ j, x (a j) := by
  simp only [polynomialEval,coordinateWordPolynomial,MvPolynomial.eval_prod,MvPolynomial.eval_X]

 def weightedPolynomialMoment {n : ℕ} {I : Type*} [Fintype I]
    (e : I → (Fin n →₀ ℕ)) (q : MvPolynomial (Fin n) ℝ)
    (μ : ProbabilityMeasure (Space n)) (c : I → ℝ) : ℝ :=
  ∑ i, c i*(∫ x, polynomialEval ((MvPolynomial.monomial (e i) 1)*q) x
    ∂(μ : Measure (Space n)))

 theorem weightedPolynomialMoment_eq_integral {n : ℕ} {I : Type*} [Fintype I]
    (e : I → (Fin n →₀ ℕ)) (q : MvPolynomial (Fin n) ℝ)
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (c : I → ℝ) : weightedPolynomialMoment e q μ c =
      ∫ x, polynomialEval (polynomialCombination e c) x*polynomialEval q x
        ∂(μ : Measure (Space n)) := by
  have hmul (i : I) : Integrable (fun x =>
      c i*(coordinateMonomial (e i) x*polynomialEval q x)) (μ : Measure (Space n)) := by
    convert ((coordinateMonomial_memLp_two hμ.logConcave (e i)).integrable_mul
      (polynomialEval_memLp_two hμ.logConcave q)).const_mul (c i) using 1
  have hexp (x : Space n) : polynomialEval (polynomialCombination e c) x*polynomialEval q x =
      ∑ i, c i*(coordinateMonomial (e i) x*polynomialEval q x) := by
    rw [polynomialEval_combination,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [hexp]
  rw [integral_finsetSum Finset.univ (fun i _ => hmul i)]
  unfold weightedPolynomialMoment
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [polynomialEval,MvPolynomial.eval_mul,MvPolynomial.eval_monomial,one_mul]
    rfl

 theorem weightedPolynomialMoment_continuousOn {n : ℕ} {I : Type*} [Fintype I]
    (e : I → (Fin n →₀ ℕ)) (q : MvPolynomial (Fin n) ℝ) :
    ContinuousOn (fun z : ProbabilityMeasure (Space n) × (I → ℝ) =>
      weightedPolynomialMoment e q z.1 z.2) ((admissibleProbabilityLaws n) ×ˢ univ) := by
  unfold weightedPolynomialMoment
  apply continuousOn_finsetSum
  intro i hi
  exact ((continuous_apply i).comp continuous_snd).continuousOn.mul
    ((continuousOn_integral_polynomialEval _).comp continuous_fst.continuousOn
      (by intro z hz; exact hz.1))

 theorem polynomialMean_continuousOn {n : ℕ} {I : Type*} [Fintype I]
    (e : I → (Fin n →₀ ℕ)) :
    ContinuousOn (fun z : ProbabilityMeasure (Space n) × (I → ℝ) =>
      ∫ x, polynomialEval (polynomialCombination e z.2) x ∂(z.1 : Measure (Space n)))
      ((admissibleProbabilityLaws n) ×ˢ univ) := by
  apply (weightedPolynomialMoment_continuousOn e 1).congr
  intro z hz
  simpa only [polynomialEval,map_one,mul_one] using (weightedPolynomialMoment_eq_integral e 1 hz.1 z.2).symm

 theorem polynomialWeightedCoordinateWord_continuousOn {n d : ℕ} {I : Type*} [Fintype I]
    (e : I → (Fin n →₀ ℕ)) (a : Fin d → Fin n) :
    ContinuousOn (fun z : ProbabilityMeasure (Space n) × (I → ℝ) =>
      ∫ x, polynomialEval (polynomialCombination e z.2) x*(∏ j, x (a j))
        ∂(z.1 : Measure (Space n))) ((admissibleProbabilityLaws n) ×ˢ univ) := by
  apply (weightedPolynomialMoment_continuousOn e (coordinateWordPolynomial a)).congr
  intro z hz
  simpa only [polynomialEval_coordinateWord] using
    (weightedPolynomialMoment_eq_integral e (coordinateWordPolynomial a) hz.1 z.2).symm

 theorem coordinateWordMoment_continuousOn {n d : ℕ} {I : Type*} [Fintype I]
    (a : Fin d → Fin n) :
    ContinuousOn (fun z : ProbabilityMeasure (Space n) × (I → ℝ) =>
      ∫ x, (∏ j, x (a j)) ∂(z.1 : Measure (Space n)))
      ((admissibleProbabilityLaws n) ×ˢ univ) := by
  have h : ContinuousOn (fun z : ProbabilityMeasure (Space n) × (I → ℝ) =>
      ∫ x, polynomialEval (coordinateWordPolynomial a) x ∂(z.1 : Measure (Space n)))
      ((admissibleProbabilityLaws n) ×ˢ univ) :=
    (continuousOn_integral_polynomialEval (coordinateWordPolynomial a)).comp
    continuous_fst.continuousOn (by intro z hz; exact hz.1)
  simpa only [polynomialEval_coordinateWord] using h

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.polynomialWeightedCoordinateWord_continuousOn
#print axioms KLS.DeterministicBridgeNext.polynomialMean_continuousOn
