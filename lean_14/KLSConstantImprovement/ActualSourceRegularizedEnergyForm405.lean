import KLSConstantImprovement.ActualSourceInverseMetricRegularization405
import KLSConstantImprovement.ActualSourceOrdinaryPoincare405
import EllipticPdes.Sobolev.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
A concrete uniformly elliptic inverse on the ordinary source H1 graph.
The coefficient matrix is the actual inverse of the regularized metric;
the measure is always the original exp(-phi) dx. Coercivity follows from
the proved per-source ordinary Poincare theorem. No Poincare constant,
variational solution, or weak derivative is supplied as an analytic premise.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceRegularizedEnergyForm405
open KLS ActualBoundedCanonicalSource ActualSourceMetricRegularization405
open ActualSourceInverseMetricRegularization405 ActualSourceOrdinaryPoincare405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def regularizedInverseCoefficientAction (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (i j : Fin n) :
    Lp ℝ 2 (potentialMeasure d.potential) →L[ℝ] Lp ℝ 2 (potentialMeasure d.potential) :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).holderL (potentialMeasure d.potential) ∞ 2 2
    ((regularizedMetricInverse_entry_memLp_top d k hε i j
      (potentialMeasure d.potential)).toLp (fun x => regularizedMetricInverse d k ε x i j))

theorem regularizedInverseCoefficientAction_ae (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (i j : Fin n) (f : Lp ℝ 2 (potentialMeasure d.potential)) :
    (regularizedInverseCoefficientAction d k hε i j f : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] (fun x => regularizedMetricInverse d k ε x i j * f x) := by
  let hc := regularizedMetricInverse_entry_memLp_top d k hε i j (potentialMeasure d.potential)
  filter_upwards [ContinuousLinearMap.coeFn_holder (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ))
    (hc.toLp (fun x => regularizedMetricInverse d k ε x i j)) f (r := 2), hc.coeFn_toLp]
    with x hx hcx
  rw [regularizedInverseCoefficientAction, ContinuousLinearMap.holderL_apply_apply, hx, hcx]
  rfl

theorem regularizedInverseCoefficientAction_inner (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (i j : Fin n) (f g : Lp ℝ 2 (potentialMeasure d.potential)) :
    inner ℝ (regularizedInverseCoefficientAction d k hε i j f) g =
      ∫ x, regularizedMetricInverse d k ε x i j * f x * g x ∂potentialMeasure d.potential := by
  rw [L2.real_inner_eq_integral]
  exact integral_congr_ae ((regularizedInverseCoefficientAction_ae d k hε i j f).fun_mul EventuallyEq.rfl)

theorem regularizedInverseCoefficientAction_integrable (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (i j : Fin n) (f g : Lp ℝ 2 (potentialMeasure d.potential)) :
    Integrable (fun x => regularizedMetricInverse d k ε x i j * f x * g x)
      (potentialMeasure d.potential) := by
  exact ((Lp.memLp (regularizedInverseCoefficientAction d k hε i j f)).integrable_mul
    (Lp.memLp g)).congr
      ((regularizedInverseCoefficientAction_ae d k hε i j f).fun_mul EventuallyEq.rfl)

def regularizedOrdinaryEnergyForm (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    WeightedCenteredH1 d.potential →L[ℝ] WeightedCenteredH1 d.potential →L[ℝ] ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, (innerSL ℝ).bilinearComp
    ((regularizedInverseCoefficientAction d k hε i j).comp (weightedH1Derivative d.potential i))
    (weightedH1Derivative d.potential j)

theorem regularizedOrdinaryEnergyForm_eq_sum_integral (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (U V : WeightedCenteredH1 d.potential) :
    regularizedOrdinaryEnergyForm d k hε U V =
      ∑ i : Fin n, ∑ j : Fin n, ∫ x, regularizedMetricInverse d k ε x i j *
        weightedH1Derivative d.potential i U x * weightedH1Derivative d.potential j V x
          ∂potentialMeasure d.potential := by
  simp only [regularizedOrdinaryEnergyForm, _root_.sum_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    regularizedInverseCoefficientAction_inner d k hε i j _ _

theorem regularizedOrdinaryEnergyForm_symm (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (U V : WeightedCenteredH1 d.potential) :
    regularizedOrdinaryEnergyForm d k hε U V = regularizedOrdinaryEnergyForm d k hε V U := by
  rw [regularizedOrdinaryEnergyForm_eq_sum_integral, regularizedOrdinaryEnergyForm_eq_sum_integral]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    have hs := (Matrix.isHermitian_iff_isSymm.mp
      (regularizedMetricInverse_posDef d k hε x).isHermitian).apply i j
    change regularizedMetricInverse d k ε x j i = regularizedMetricInverse d k ε x i j at hs
    dsimp only
    rw [hs]
    ring

theorem regularizedOrdinaryEnergyForm_lower (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (U : WeightedCenteredH1 d.potential) :
    (4 / d.targetConvexityConstant + ε)⁻¹ *
        ∑ i : Fin n, ‖weightedH1Derivative d.potential i U‖ ^ 2 ≤
      regularizedOrdinaryEnergyForm d k hε U U := by
  let p (i : Fin n) : Lp ℝ 2 (potentialMeasure d.potential) := weightedH1Derivative d.potential i U
  let c : ℝ := (4 / d.targetConvexityConstant + ε)⁻¹
  have hl : Integrable (fun x => c * ∑ i : Fin n, (p i x)^2) (potentialMeasure d.potential) :=
    (integrable_finsetSum Finset.univ (fun i _ => (Lp.memLp (p i)).integrable_sq)).const_mul c
  have hr : Integrable (fun x => ∑ i : Fin n, ∑ j : Fin n,
      regularizedMetricInverse d k ε x i j * p i x * p j x) (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ =>
      regularizedInverseCoefficientAction_integrable d k hε i j (p i) (p j)
  have hp : ∀ x, c * ∑ i : Fin n, (p i x)^2 ≤
      ∑ i : Fin n, ∑ j : Fin n, regularizedMetricInverse d k ε x i j * p i x * p j x := by
    intro x
    have h := (regularizedMetricInverse_quadratic_bounds d k hε x (fun i => p i x)).1
    rw [← matrix_quadratic_sum_eq_dotProduct] at h
    simpa only [c, dotProduct, pow_two] using h
  have h := integral_mono hl hr hp
  rw [integral_const_mul, integral_finsetSum Finset.univ
    (fun i _ => (Lp.memLp (p i)).integrable_sq)] at h
  simp_rw [← L2.norm_sq_eq_integral_sq] at h
  rw [regularizedOrdinaryEnergyForm_eq_sum_integral]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => regularizedInverseCoefficientAction_integrable d k hε i j (p i) (p j)))] at h
  simp_rw [integral_finsetSum Finset.univ
    (fun j _ => regularizedInverseCoefficientAction_integrable d k hε _ j (p _) (p j))] at h
  exact h

/-- Coercivity is paid by the actual source gap; its value is used solely
for existence, before the independent vector Gaffney estimate. -/
theorem regularizedOrdinaryEnergyForm_isCoercive (d : SourceData μ) (hn : 1 ≤ n)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) : IsCoercive (regularizedOrdinaryEnergyForm d k hε) := by
  obtain ⟨C, hC, hP⟩ := exists_source_ordinary_H1_poincare d hn
  let c : ℝ := (4 / d.targetConvexityConstant + ε)⁻¹
  have hc : 0 < c := by
    have hκ := d.target_convexity_pos
    dsimp [c]
    positivity
  have hCp : 0 < 1 + C := by linarith
  refine ⟨c * (1 + C)⁻¹, mul_pos hc (inv_pos.mpr hCp), ?_⟩
  intro U
  have hp := hP U
  have hnrm := weightedH1_norm_sq d.potential U
  have hnorm : ‖U‖ ^ 2 ≤ (1 + C) * ∑ i : Fin n, ‖weightedH1Derivative d.potential i U‖ ^ 2 := by
    nlinarith
  calc
    (c * (1 + C)⁻¹) * ‖U‖ * ‖U‖ = c * ((1 + C)⁻¹ * ‖U‖ ^ 2) := by ring
    _ ≤ c * ∑ i : Fin n, ‖weightedH1Derivative d.potential i U‖ ^ 2 :=
      mul_le_mul_of_nonneg_left ((inv_mul_le_iff₀ hCp).mpr hnorm) hc.le
    _ ≤ _ := regularizedOrdinaryEnergyForm_lower d k hε U

def regularizedOrdinaryInverse (d : SourceData μ) (hn : 1 ≤ n)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Lp ℝ 2 (potentialMeasure d.potential) →L[ℝ] WeightedCenteredH1 d.potential :=
  (regularizedOrdinaryEnergyForm_isCoercive d hn k hε).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (weightedH1Value d.potential).adjoint

theorem regularizedOrdinaryInverse_variational (d : SourceData μ) (hn : 1 ≤ n)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (V : WeightedCenteredH1 d.potential) :
    regularizedOrdinaryEnergyForm d k hε (regularizedOrdinaryInverse d hn k hε g) V =
      inner ℝ g (weightedH1Value d.potential V) := by
  let hc := regularizedOrdinaryEnergyForm_isCoercive d hn k hε
  rw [← hc.continuousLinearEquivOfBilin_apply]
  change inner ℝ (hc.continuousLinearEquivOfBilin
    (hc.continuousLinearEquivOfBilin.symm ((weightedH1Value d.potential).adjoint g))) V = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]

theorem regularizedOrdinaryInverse_unique (d : SourceData μ) (hn : 1 ≤ n)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    {U : WeightedCenteredH1 d.potential}
    (hU : ∀ V, regularizedOrdinaryEnergyForm d k hε U V =
      inner ℝ g (weightedH1Value d.potential V)) : U = regularizedOrdinaryInverse d hn k hε g := by
  let hc := regularizedOrdinaryEnergyForm_isCoercive d hn k hε
  have he : (weightedH1Value d.potential).adjoint g = hc.continuousLinearEquivOfBilin U := by
    apply hc.unique_continuousLinearEquivOfBilin
    intro V
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact (hU V).symm
  change U = hc.continuousLinearEquivOfBilin.symm ((weightedH1Value d.potential).adjoint g)
  rw [he, ContinuousLinearEquiv.symm_apply_apply]

theorem regularizedOrdinaryInverse_mean_zero (d : SourceData μ) (hn : 1 ≤ n)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    (∫ x, weightedH1Value d.potential (regularizedOrdinaryInverse d hn k hε g) x
      ∂potentialMeasure d.potential) = 0 := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  exact weightedH1_integral_eq_zero d.source_C1.continuous _

end KLSConstantImprovement.ActualSourceRegularizedEnergyForm405
#print axioms KLSConstantImprovement.ActualSourceRegularizedEnergyForm405.regularizedInverseCoefficientAction_ae
#print axioms KLSConstantImprovement.ActualSourceRegularizedEnergyForm405.regularizedInverseCoefficientAction_inner
#print axioms KLSConstantImprovement.ActualSourceRegularizedEnergyForm405.regularizedInverseCoefficientAction_integrable
#print axioms KLSConstantImprovement.ActualSourceRegularizedEnergyForm405.regularizedOrdinaryEnergyForm_eq_sum_integral
#print axioms KLSConstantImprovement.ActualSourceRegularizedEnergyForm405.regularizedOrdinaryEnergyForm_symm
#print axioms KLSConstantImprovement.ActualSourceRegularizedEnergyForm405.regularizedOrdinaryEnergyForm_lower
#print axioms KLSConstantImprovement.ActualSourceRegularizedEnergyForm405.regularizedOrdinaryEnergyForm_isCoercive
#print axioms KLSConstantImprovement.ActualSourceRegularizedEnergyForm405.regularizedOrdinaryInverse_variational
#print axioms KLSConstantImprovement.ActualSourceRegularizedEnergyForm405.regularizedOrdinaryInverse_unique
#print axioms KLSConstantImprovement.ActualSourceRegularizedEnergyForm405.regularizedOrdinaryInverse_mean_zero
