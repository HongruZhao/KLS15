import ActualAppellFiniteMoments
import PolynomialJointMoments

/-! Joint continuity of genuine Appell coefficients and ordered tensor energies
on the actual admissible-law / finite-polynomial coefficient space. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem scalarRatio_jet_line_continuous (r : ℕ) :
    Continuous (fun a : ℝ => iteratedFDeriv ℝ r scalarRatio (a,1)) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  have hline : ContinuousAt (fun t : ℝ => (t,(1 : ℝ))) a :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hjet : ContinuousAt (iteratedFDeriv ℝ r scalarRatio) (a,1) :=
    (scalarRatio_contDiffAt a 1 one_ne_zero).continuousAt_iteratedFDeriv (by simp)
  exact ContinuousAt.comp (f := fun t : ℝ => (t,(1 : ℝ))) hjet hline

 theorem actualAppellPolynomial_coefficient_continuousOn {n r : ℕ} {I : Type*} [Fintype I]
    (e : I → (Fin n →₀ ℕ)) (a : Fin r → Fin n) :
    ContinuousOn (fun z : ProbabilityMeasure (Space n) × (I → ℝ) =>
      actualAppellCoefficient (z.1 : Measure (Space n))
        (polynomialEval (polynomialCombination e z.2)) r a)
      ((admissibleProbabilityLaws n) ×ˢ univ) := by
  have hsum : ContinuousOn (fun z : ProbabilityMeasure (Space n) × (I → ℝ) =>
      ∑ c : OrderedFinpartition r,
        iteratedFDeriv ℝ c.length scalarRatio
          (∫ x, polynomialEval (polynomialCombination e z.2) x ∂(z.1 : Measure (Space n)),1)
          (fun j => (∫ x, polynomialEval (polynomialCombination e z.2) x*
              (∏ i, x (a (c.emb j i))) ∂(z.1 : Measure (Space n)),
            ∫ x, (∏ i, x (a (c.emb j i))) ∂(z.1 : Measure (Space n)))))
      ((admissibleProbabilityLaws n) ×ˢ univ) := by
    apply continuousOn_finsetSum
    intro c hc
    have houter : ContinuousOn (fun z : ProbabilityMeasure (Space n) × (I → ℝ) =>
        iteratedFDeriv ℝ c.length scalarRatio
          (∫ x, polynomialEval (polynomialCombination e z.2) x ∂(z.1 : Measure (Space n)),1))
        ((admissibleProbabilityLaws n) ×ˢ univ) :=
      (scalarRatio_jet_line_continuous c.length).comp_continuousOn (polynomialMean_continuousOn e)
    have hinner : ContinuousOn (fun z : ProbabilityMeasure (Space n) × (I → ℝ) =>
        fun j : Fin c.length =>
          (∫ x, polynomialEval (polynomialCombination e z.2) x*
              (∏ i, x (a (c.emb j i))) ∂(z.1 : Measure (Space n)),
            ∫ x, (∏ i, x (a (c.emb j i))) ∂(z.1 : Measure (Space n))))
        ((admissibleProbabilityLaws n) ×ˢ univ) := by
      apply continuousOn_pi.mpr
      intro j
      exact (polynomialWeightedCoordinateWord_continuousOn e (fun i => a (c.emb j i))).prodMk
        (coordinateWordMoment_continuousOn (I := I) (fun i => a (c.emb j i)))
    exact continuous_eval.comp_continuousOn (houter.prodMk hinner)
  apply hsum.congr
  intro z hz
  exact actualAppellCoefficient_finite_moment_formula hz.1.logConcave
    (polynomialEval_memLp_two hz.1.logConcave _) a

 def actualAppellEnergy {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) (r : ℕ) : ℝ :=
  ∑ a : Fin r → Fin n, (actualAppellCoefficient μ f r a)^2

 theorem actualAppellEnergy_nonneg {n : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) (r : ℕ) : 0 ≤ actualAppellEnergy μ f r :=
  Finset.sum_nonneg fun a _ => sq_nonneg _

 theorem actualAppellPolynomial_energy_continuousOn {n r : ℕ} {I : Type*} [Fintype I]
    (e : I → (Fin n →₀ ℕ)) :
    ContinuousOn (fun z : ProbabilityMeasure (Space n) × (I → ℝ) =>
      actualAppellEnergy (z.1 : Measure (Space n))
        (polynomialEval (polynomialCombination e z.2)) r)
      ((admissibleProbabilityLaws n) ×ˢ univ) := by
  unfold actualAppellEnergy
  exact continuousOn_finsetSum _ fun a _ =>
    (actualAppellPolynomial_coefficient_continuousOn e a).pow 2

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualAppellPolynomial_coefficient_continuousOn
#print axioms KLS.DeterministicBridgeNext.actualAppellPolynomial_energy_continuousOn
