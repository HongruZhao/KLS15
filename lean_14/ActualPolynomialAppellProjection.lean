import ActualPolynomialL2Projection
import ActualAppellJointContinuity
import FullClassAppellStationarity

/-! Actual polynomial moment projection preserves all normalized Laplace jets
through the projection degree, hence the genuine Appell tensors. -/
noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem coordinateWordPolynomial_totalDegree_le {n r : ℕ} (a : Fin r → Fin n) :
    (coordinateWordPolynomial a).totalDegree ≤ r := by
  unfold coordinateWordPolynomial
  exact (MvPolynomial.totalDegree_finsetProd _ _).trans (by simp)

 theorem actualAppellCoefficient_eq_of_polynomial_pairings {n d r : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f g : Space n → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hpair : ∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ d →
      (∫ x, polynomialEval q x*f x ∂μ) = ∫ x, polynomialEval q x*g x ∂μ)
    (hr : r ≤ d) (a : Fin r → Fin n) :
    actualAppellCoefficient μ f r a = actualAppellCoefficient μ g r a := by
  have hmean : (∫ x, f x ∂μ) = ∫ x, g x ∂μ := by
    simpa [polynomialEval] using hpair 1 (by simp)
  rw [actualAppellCoefficient_finite_moment_formula hLC hf,
    actualAppellCoefficient_finite_moment_formula hLC hg,hmean]
  apply Finset.sum_congr rfl
  intro c hc
  congr 1
  funext j
  congr 1
  have hp := hpair (coordinateWordPolynomial (fun i => a (c.emb j i)))
    ((coordinateWordPolynomial_totalDegree_le _).trans ((c.partSize_le j).trans hr))
  simpa only [polynomialEval_coordinateWord,mul_comm] using hp

/-- The projection is constructed, norm-contracting, and preserves each actual
Appell coefficient of every order up to d. -/
 theorem exists_actual_polynomial_Appell_projection {n d : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    ∃ c : DegreeIndex n d → ℝ,
      ‖polynomialLp hμ.logConcave (boundedDegreePolynomial c)‖ ≤ ‖f‖ ∧
      ∀ r ≤ d, ∀ a : Fin r → Fin n,
        actualAppellCoefficient μ (polynomialEval (boundedDegreePolynomial c)) r a =
          actualAppellCoefficient μ f r a := by
  obtain ⟨c,hc,hpair⟩ := exists_actual_polynomial_L2_projection (d := d) hμ f
  refine ⟨c,hc,?_⟩
  intro r hr a
  exact actualAppellCoefficient_eq_of_polynomial_pairings hμ.logConcave
    (polynomialEval_memLp_two hμ.logConcave _) (Lp.memLp f) hpair hr a

 theorem exists_actual_polynomial_Appell_energy_projection {n d : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    ∃ c : DegreeIndex n d → ℝ,
      ‖polynomialLp hμ.logConcave (boundedDegreePolynomial c)‖ ≤ ‖f‖ ∧
      ∀ r ≤ d, actualAppellEnergy μ (polynomialEval (boundedDegreePolynomial c)) r =
        actualAppellEnergy μ f r := by
  obtain ⟨c,hc,hjet⟩ := exists_actual_polynomial_Appell_projection (d := d) hμ f
  refine ⟨c,hc,?_⟩
  intro r hr
  unfold actualAppellEnergy
  exact Finset.sum_congr rfl fun a _ => congrArg (fun t : ℝ => t^2) (hjet r hr a)

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualAppellCoefficient_eq_of_polynomial_pairings
#print axioms KLS.DeterministicBridgeNext.exists_actual_polynomial_Appell_projection
#print axioms KLS.DeterministicBridgeNext.exists_actual_polynomial_Appell_energy_projection
