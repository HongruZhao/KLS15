import ActualAppellFiniteMoments
import PolynomialJointMoments
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Actual L² orthogonal projection onto the total-degree polynomial space.
The finite subspace consists of genuine polynomial representatives. -/
noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 def polynomialLp {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (p : MvPolynomial (Fin n) ℝ) : Lp ℝ 2 μ :=
  (polynomialEval_memLp_two hLC p).toLp (polynomialEval p)

 theorem polynomialLp_coe {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (p : MvPolynomial (Fin n) ℝ) :
    (polynomialLp hLC p : Space n → ℝ) =ᵐ[μ] polynomialEval p :=
  (polynomialEval_memLp_two hLC p).coeFn_toLp

 def monomialLp {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (s : Fin n →₀ ℕ) : Lp ℝ 2 μ :=
  (coordinateMonomial_memLp_two hLC s).toLp (coordinateMonomial s)

 theorem monomialLp_coe {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (s : Fin n →₀ ℕ) :
    (monomialLp hLC s : Space n → ℝ) =ᵐ[μ] coordinateMonomial s :=
  (coordinateMonomial_memLp_two hLC s).coeFn_toLp

 def polynomialCoefficientLpLinearMap {n : ℕ} {I : Type*} [Fintype I]
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (e : I → (Fin n →₀ ℕ)) : (I → ℝ) →ₗ[ℝ] Lp ℝ 2 μ where
  toFun c := ∑ i, c i • monomialLp hLC (e i)
  map_add' c d := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r c := by simp only [Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply]

 theorem polynomialCoefficientLp_coe {n : ℕ} {I : Type*} [Fintype I]
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (e : I → (Fin n →₀ ℕ)) (c : I → ℝ) :
    (polynomialCoefficientLpLinearMap hLC e c : Space n → ℝ) =ᵐ[μ]
      polynomialEval (polynomialCombination e c) := by
  change (((∑ i, c i • monomialLp hLC (e i)) : Lp ℝ 2 μ) : Space n → ℝ) =ᵐ[μ] _
  apply (Lp.coeFn_finsetSum _ _).trans
  have hs : (∑ i : I, ⇑(c i • monomialLp hLC (e i))) =ᵐ[μ]
      ∑ i : I, (fun x => c i*coordinateMonomial (e i) x) := by
    apply eventuallyEq_sum
    intro i hi
    exact (Lp.coeFn_smul _ _).trans ((monomialLp_coe hLC (e i)).const_smul _)
  apply hs.trans
  exact Eventually.of_forall fun x => by
    simp only [Finset.sum_apply,polynomialEval_combination]

 theorem polynomialCoefficientLp_eq {n : ℕ} {I : Type*} [Fintype I]
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (e : I → (Fin n →₀ ℕ)) (c : I → ℝ) :
    polynomialCoefficientLpLinearMap hLC e c = polynomialLp hLC (polynomialCombination e c) := by
  apply Lp.ext
  exact (polynomialCoefficientLp_coe hLC e c).trans (polynomialLp_coe hLC _).symm

 theorem inner_polynomialLp_eq_integral {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (p : MvPolynomial (Fin n) ℝ) (f : Lp ℝ 2 μ) :
    inner ℝ (polynomialLp hLC p) f = ∫ x, polynomialEval p x*f x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [polynomialLp_coe hLC p] with x hx
  rw [hx]
  simp only [RCLike.inner_apply,conj_trivial]
  ring

/-- Orthogonal projection is constructed in actual L². It has a genuine
bounded-degree polynomial representative, contracts the norm, and preserves
all actual polynomial pairings through that degree. -/
 theorem exists_actual_polynomial_L2_projection {n d : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ]
    (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    ∃ c : DegreeIndex n d → ℝ,
      ‖polynomialLp hμ.logConcave (boundedDegreePolynomial c)‖ ≤ ‖f‖ ∧
      ∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ d →
        (∫ x, polynomialEval q x*polynomialEval (boundedDegreePolynomial c) x ∂μ) =
        ∫ x, polynomialEval q x*f x ∂μ := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let L := polynomialCoefficientLpLinearMap hμ.logConcave (degreeExponent n d)
  let U : Submodule ℝ (Lp ℝ 2 μ) := LinearMap.range L
  letI : FiniteDimensional ℝ U := LinearMap.finiteDimensional_range L
  obtain ⟨c,hc⟩ := U.starProjection_apply_mem f
  have hcrep : L c = polynomialLp hμ.logConcave (boundedDegreePolynomial c) :=
    polynomialCoefficientLp_eq _ _ _
  refine ⟨c,?_,?_⟩
  · rw [← hcrep,hc]
    exact U.norm_starProjection_apply_le f
  · intro q hq
    let cq : DegreeIndex n d → ℝ := fun s => q.coeff s.val
    have hqrep : L cq = polynomialLp hμ.logConcave q := by
      rw [show L cq = polynomialLp hμ.logConcave (boundedDegreePolynomial cq) from
        polynomialCoefficientLp_eq _ _ _]
      rw [boundedDegreePolynomial_representation q hq]
    have hmem : polynomialLp hμ.logConcave q ∈ U := ⟨cq,hqrep⟩
    have ho := U.starProjection_inner_eq_zero f (polynomialLp hμ.logConcave q) hmem
    rw [inner_sub_left] at ho
    have he : inner ℝ (polynomialLp hμ.logConcave q)
        (polynomialLp hμ.logConcave (boundedDegreePolynomial c)) =
        inner ℝ (polynomialLp hμ.logConcave q) f := by
      calc
        _ = inner ℝ (polynomialLp hμ.logConcave (boundedDegreePolynomial c))
            (polynomialLp hμ.logConcave q) := real_inner_comm _ _
        _ = inner ℝ f (polynomialLp hμ.logConcave q) := by
          rw [← hcrep,hc]
          linarith
        _ = _ := real_inner_comm _ _
    rw [inner_polynomialLp_eq_integral,inner_polynomialLp_eq_integral] at he
    calc
      _ = ∫ x, polynomialEval q x*(polynomialLp hμ.logConcave (boundedDegreePolynomial c)) x ∂μ :=
        integral_congr_ae (EventuallyEq.rfl.mul (polynomialLp_coe hμ.logConcave _).symm)
      _ = _ := he

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.exists_actual_polynomial_L2_projection
