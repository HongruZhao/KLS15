import PolynomialLawMoments
import KLS.LogConcavitySupport
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Algebra.MvPolynomial.Funext

/-! Genuine polynomial nondegeneracy for every original admissible law.
Continuity upgrades an almost-everywhere zero polynomial to zero on the
support; the released full-dimensional support theorem and the analytic
identity principle then force the polynomial itself to vanish. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal BigOperators
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem polynomialEval_analyticOnNhd {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    AnalyticOnNhd ℝ (polynomialEval p) univ :=
by
  intro x hx
  change AnalyticAt ℝ (fun y : Space n => MvPolynomial.eval (fun j => y j) p) x
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval_C]
      exact analyticAt_const
  | add p q hp hq =>
      simp only [MvPolynomial.eval_add]
      exact AnalyticAt.add hp hq
  | mul_X p j hp =>
      simp only [MvPolynomial.eval_mul,MvPolynomial.eval_X]
      have hpi : AnalyticAt ℝ (fun y : Space n => y j) x :=
        (EuclideanSpace.proj (𝕜 := ℝ) j).analyticAt x
      exact AnalyticAt.mul hp hpi

/-- The literal polynomial evaluation map into L² of any admissible law is
injective. There is no positivity-of-density assumption. -/
 theorem polynomial_eq_zero_of_ae_eval_zero {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (p : MvPolynomial (Fin n) ℝ)
    (hae : polynomialEval p =ᵐ[μ] 0) : p = 0 := by
  have hsub : μ.support ⊆ {x | polynomialEval p x = 0} :=
    μ.support_subset_of_isClosed (isClosed_eq (polynomialEval_continuous p) continuous_const) hae
  obtain ⟨x,hx⟩ := hμ.support_interior_nonempty
  have hzero : polynomialEval p =ᶠ[𝓝 x] 0 := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hx] with y hy
    exact hsub hy
  have heq : polynomialEval p = 0 :=
    (polynomialEval_analyticOnNhd p).eq_of_eventuallyEq analyticOnNhd_const hzero
  apply MvPolynomial.funext
  intro y
  have h := congrFun heq (WithLp.toLp 2 y : Space n)
  simpa only [polynomialEval,Pi.zero_apply,map_zero] using h

 theorem integral_polynomialEval_sq_pos {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    0 < ∫ x, (polynomialEval p x)^2 ∂μ := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hLp := polynomialEval_memLp_two hμ.logConcave p
  have hi := (memLp_two_iff_integrable_sq hLp.aestronglyMeasurable).mp hLp
  have hnon : 0 ≤ ∫ x, (polynomialEval p x)^2 ∂μ := integral_nonneg fun x => sq_nonneg _
  by_contra h
  have hz : (∫ x, (polynomialEval p x)^2 ∂μ) = 0 := le_antisymm (le_of_not_gt h) hnon
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (polynomialEval p x)) hi).mp hz
  apply hp
  apply polynomial_eq_zero_of_ae_eval_zero hμ p
  filter_upwards [hae] with x hx
  exact sq_eq_zero_iff.mp hx

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.polynomial_eq_zero_of_ae_eval_zero
#print axioms KLS.DeterministicBridgeNext.integral_polynomialEval_sq_pos
