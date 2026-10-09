import AdmissibleLawCompactness
import Mathlib.Topology.Algebra.MvPolynomial

/-! All actual multivariate polynomial moments are weakly continuous on the
literal admissible-law class. Monomial growth is bounded directly; the result
has no moment-continuity premise. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal BigOperators
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 def coordinateMonomial {n : ℕ} (s : Fin n →₀ ℕ) (x : Space n) : ℝ :=
  ∏ j ∈ s.support, (x j)^(s j)

 theorem coordinateMonomial_continuous {n : ℕ} (s : Fin n →₀ ℕ) :
    Continuous (coordinateMonomial s) := by unfold coordinateMonomial; fun_prop

 theorem coordinateMonomial_norm_le {n : ℕ} (s : Fin n →₀ ℕ) (x : Space n) :
    ‖coordinateMonomial s x‖ ≤ ‖x‖^(∑ j ∈ s.support, s j) := by
  unfold coordinateMonomial
  rw [norm_prod]
  calc
    _ ≤ ∏ j ∈ s.support, ‖x‖^(s j) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j hj
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le x j) _
    _ = _ := (Finset.prod_pow_eq_pow_sum _ _ _)

 theorem coordinateMonomial_memLp_two {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) (s : Fin n →₀ ℕ) :
    MemLp (coordinateMonomial s) 2 μ :=
  memLp_two_of_norm_pow_bound hLC (coordinateMonomial_continuous s) _
    (coordinateMonomial_norm_le s)

 def polynomialEval {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Space n) : ℝ :=
  MvPolynomial.eval (fun j => x j) p

 theorem polynomialEval_sum {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Space n) :
    polynomialEval p x = ∑ s ∈ p.support, p.coeff s*coordinateMonomial s x := rfl

 theorem polynomialEval_continuous {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Continuous (polynomialEval p) := by
  change Continuous (fun x => ∑ s ∈ p.support, p.coeff s*coordinateMonomial s x)
  exact continuous_finsetSum _ fun s _ => continuous_const.mul (coordinateMonomial_continuous s)

 theorem polynomialEval_memLp_two {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) (p : MvPolynomial (Fin n) ℝ) :
    MemLp (polynomialEval p) 2 μ := by
  have he : polynomialEval p = fun x => ∑ s ∈ p.support, p.coeff s*coordinateMonomial s x :=
    funext (polynomialEval_sum p)
  rw [he]
  exact memLp_finsetSum _ fun s _ => (coordinateMonomial_memLp_two hLC s).const_mul _

 theorem integral_polynomialEval_sum {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) (p : MvPolynomial (Fin n) ℝ) :
    (∫ x, polynomialEval p x ∂μ) =
      ∑ s ∈ p.support, p.coeff s*(∫ x, coordinateMonomial s x ∂μ) := by
  simp_rw [polynomialEval_sum]
  rw [integral_finsetSum _ (fun s _ =>
    ((coordinateMonomial_memLp_two hLC s).integrable (by norm_num)).const_mul _)]
  simp_rw [integral_const_mul]

 theorem tendsto_integral_polynomialEval
    {n : ℕ} {ι : Type*} {l : Filter ι} [NeBot l]
    {ν : ι → ProbabilityMeasure (Space n)} {μ : ProbabilityMeasure (Space n)}
    (hlim : Tendsto ν l (𝓝 μ))
    (hν : ∀ i, admissibleMeasure (ν i : Measure (Space n)))
    (p : MvPolynomial (Fin n) ℝ) :
    Tendsto (fun i => ∫ x, polynomialEval p x ∂(ν i : Measure (Space n))) l
      (𝓝 (∫ x, polynomialEval p x ∂(μ : Measure (Space n)))) := by
  have hLC := (admissibleMeasure_of_probability_tendsto hlim hν).logConcave
  simp_rw [integral_polynomialEval_sum (hν _).logConcave,
    integral_polynomialEval_sum hLC]
  apply tendsto_finsetSum
  intro s hs
  exact (tendsto_integral_norm_pow_bounded_observable hlim hν
      (coordinateMonomial_continuous s) _ (coordinateMonomial_norm_le s)).const_mul _

 theorem continuousOn_integral_polynomialEval {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    ContinuousOn (fun μ : ProbabilityMeasure (Space n) =>
      ∫ x, polynomialEval p x ∂(μ : Measure (Space n))) (admissibleProbabilityLaws n) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_iff_seqContinuous.mpr
  intro ν μ hlim
  have hlim' := (continuous_subtype_val.tendsto μ).comp hlim
  exact tendsto_integral_polynomialEval hlim' (fun i => (ν i).property) p

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.tendsto_integral_polynomialEval
#print axioms KLS.DeterministicBridgeNext.continuousOn_integral_polynomialEval
