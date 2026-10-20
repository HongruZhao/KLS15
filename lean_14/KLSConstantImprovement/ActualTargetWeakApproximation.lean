import PaperRegularApproximation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Actual probability weak convergence of the retained target approximations.
The existing compact-test coupling proofs use only a bound on the test.
These bounded-continuous versions discharge probability weak convergence
for actual cutoff, Gaussian and damped-whitened target laws. No source or
Poisson field is constructed or passed; no numerical bound is asserted. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix Metric
open scoped Topology ENNReal NNReal BigOperators
namespace KLSConstantImprovement.ActualTargetWeakApproximation
open KLS KLS.DeterministicBridgeIntegration
variable {n : ℕ}

def probabilityOf (μ : Measure (Space n)) (hμ : IsProbabilityMeasure μ) :
    ProbabilityMeasure (Space n) := @Measure.toProbabilityMeasure (Space n) inferInstance μ hμ

def dampedWhitenedProbability {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (ε : ℝ) (hε : 0 ≤ ε) : ProbabilityMeasure (Space n) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  letI : IsProbabilityMeasure (quadraticDamping μ ε) :=
    isProbabilityMeasure_quadraticDamping_nonneg μ hε
  exact (whitenedMeasure (quadraticDamping μ ε)).toProbabilityMeasure

def gaussianProbability (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (ε : ℝ) : ProbabilityMeasure (Space n) :=
  (isotropicGaussianSmoothing μ ε).toProbabilityMeasure

def cutoffWhitenedProbability {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {R : ℝ} (hR : μ (closedBall (0 : Space n) R) ≠ 0) (k : ℕ) :
    ProbabilityMeasure (Space n) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  letI : IsProbabilityMeasure (ballCutoffMeasure μ R k) :=
    isProbabilityMeasure_ballCutoffMeasure hR k
  exact (whitenedMeasure (ballCutoffMeasure μ R k)).toProbabilityMeasure

theorem tendsto_integral_bounded_affine_damping
    (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    {ε : ℕ → ℝ} (hε : ∀ k, 0 ≤ ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {b : ℕ → Space n}
    (hcoeff : ∀ i j, Tendsto (fun k => affineCoordinateCoefficient (A k) (b k) i j)
      atTop (𝓝 (affineCoordinateCoefficient 1 0 i j)))
    {f : Space n → ℝ} (hf : Continuous f) {B : ℝ} (hb : ∀ x, ‖f x‖ ≤ B) :
    Tendsto (fun k => ∫ x, f x ∂affineMatrixMeasure (quadraticDamping μ (ε k)) (A k) (b k))
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Space n => B)
    (F := fun k x => f (affineMatrixMap (A k) (b k) x) * Real.exp (-ε k * ‖x‖ ^ 2))
    (f := f) (μ := μ) (fun _ => by fun_prop) (integrable_const _)
    (fun k => Eventually.of_forall fun x => by
      simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_of_le_one_right (abs_nonneg _) (exp_quadraticDamping_le_one (hε k) x)).trans (hb _))
    (Eventually.of_forall fun x => by
      have he := (Real.continuous_exp.tendsto 0).comp
        (by simpa using hεlim.neg.mul_const (‖x‖ ^ 2))
      have hfx := hf.continuousAt.tendsto.comp (tendsto_affineMatrixMap_of_coefficients hcoeff x)
      simpa only [Real.exp_zero, mul_one, neg_mul, Function.comp_def] using hfx.mul he)
  have hden : Tendsto (fun k => tiltPartition μ (fun x => -ε k * ‖x‖ ^ 2)) atTop (𝓝 1) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ : Space n => (1 : ℝ))
      (F := fun k x => Real.exp (-ε k * ‖x‖ ^ 2)) (f := fun _ => (1 : ℝ)) (μ := μ)
      (fun _ => by fun_prop) (integrable_const _)
      (fun k => Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using exp_quadraticDamping_le_one (hε k) x)
      (Eventually.of_forall fun x => by
        simpa only [Real.exp_zero, Function.comp_def, neg_mul] using
          (Real.continuous_exp.tendsto 0).comp (by simpa using hεlim.neg.mul_const (‖x‖ ^ 2)))
    simpa only [tiltPartition, integral_const, probReal_univ, one_smul] using h
  have he (k : ℕ) : (∫ x, f x ∂affineMatrixMeasure (quadraticDamping μ (ε k)) (A k) (b k)) =
      (∫ x, f (affineMatrixMap (A k) (b k) x) * Real.exp (-ε k * ‖x‖ ^ 2) ∂μ) /
        tiltPartition μ (fun x => -ε k * ‖x‖ ^ 2) := by
    rw [affineMatrixMeasure, integral_map (by fun_prop) hf.aestronglyMeasurable]
    exact tiltAverage_eq_ratio μ _ _
  simp_rw [he]
  simpa only [Pi.div_def, div_one] using ht.div hden one_ne_zero

theorem tendsto_integral_bounded_gaussian_smoothing
    (μ : Measure (Space n)) [IsProbabilityMeasure μ] {f : Space n → ℝ}
    (hf : Continuous f) {B : ℝ} (hb : ∀ x, ‖f x‖ ≤ B) :
    Tendsto (fun k => ∫ x, f x ∂isotropicGaussianSmoothing μ (cutoffScale k))
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Space n × Space n => B)
    (fun k => (hf.comp (by fun_prop : Continuous (fun p : Space n × Space n =>
      gaussianNormalization (cutoffScale k) • (p.1 + cutoffScale k • p.2)))).aestronglyMeasurable)
    (μ := μ.prod (gaussianExample n)) (integrable_const _)
    (fun _ => Eventually.of_forall fun _ => hb _)
    (Eventually.of_forall fun p => by
      have hg := gaussianNormalization_tendsto.comp cutoffScale_tendsto_zero
      have hx := (tendsto_const_nhds (x := p.1)).add
        (cutoffScale_tendsto_zero.smul_const p.2)
      simpa only [zero_smul, add_zero, one_smul, Function.comp_def] using
        (hf.continuousAt.tendsto.comp (hg.smul hx)))
  have he (k : ℕ) : (∫ x, f x ∂isotropicGaussianSmoothing μ (cutoffScale k)) =
      ∫ p : Space n × Space n,
        f (gaussianNormalization (cutoffScale k) • (p.1 + cutoffScale k • p.2))
          ∂μ.prod (gaussianExample n) := by
    rw [isotropicGaussianSmoothing, integral_map (by fun_prop) hf.aestronglyMeasurable]
    exact integral_gaussianSmoothing_eq_prod μ _ (by fun_prop)
  simp_rw [he]
  simpa only [integral_fun_fst (μ := μ) (ν := gaussianExample n), probReal_univ,
    one_smul, Function.comp_def] using ht

theorem tendsto_integral_bounded_whitened_cutoff
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0)
    {f : Space n → ℝ} (hf : Continuous f) {B : ℝ} (hb : ∀ x, ‖f x‖ ≤ B) :
    Tendsto (fun k => ∫ x, f x ∂whitenedBallCutoffMeasure μ R k)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  let ν := fun k => ballCutoffMeasure μ R k
  let A := fun k => inverseSqrtMatrix (covarianceMatrix (ν k))
  let b := fun k => -matrixAction (A k) (∫ x, x ∂ν k)
  have hmap (x : Space n) : Tendsto (fun k => affineMatrixMap (A k) (b k) x) atTop (𝓝 x) :=
    tendsto_affineMatrixMap_of_coefficients (hμ.tendsto_whitening_coefficient hR) x
  have hB0 : 0 ≤ B := (norm_nonneg (f 0)).trans (hb 0)
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Space n => B)
    (F := fun k => (closedBall (0 : Space n) (R + k)).indicator
      (fun x => f (affineMatrixMap (A k) (b k) x))) (f := f) (μ := μ)
    (fun _ => (by fun_prop : AEStronglyMeasurable
      (fun x => f (affineMatrixMap (A _) (b _) x)) μ).indicator measurableSet_closedBall)
    (integrable_const _)
    (fun k => Eventually.of_forall fun x => by
      by_cases hx : x ∈ closedBall (0 : Space n) (R + k)
      · rw [indicator_of_mem hx]
        exact hb _
      · rw [indicator_of_notMem hx, norm_zero]
        exact hB0)
    (Eventually.of_forall fun x => by
      obtain ⟨N, hN⟩ := mem_iUnion.mp (show x ∈ ⋃ k : ℕ, closedBall (0 : Space n) (R + k) by
        rw [iUnion_cutoffBalls]; exact mem_univ x)
      apply (hf.continuousAt.tendsto.comp (hmap x)).congr'
      filter_upwards [eventually_ge_atTop N] with k hk
      simp only [indicator_of_mem ((monotone_cutoffBalls R hk) hN), Function.comp_apply])
  have he (k : ℕ) : (∫ x, f x ∂whitenedBallCutoffMeasure μ R k) =
      (μ.real (closedBall (0 : Space n) (R + k)))⁻¹ *
        ∫ x, (closedBall (0 : Space n) (R + k)).indicator
          (fun x => f (affineMatrixMap (A k) (b k) x)) x ∂μ := by
    rw [whitenedBallCutoffMeasure, whitenedMeasure, affineMatrixMeasure,
      integral_map (by fun_prop) hf.aestronglyMeasurable,
      ballCutoffMeasure, ProbabilityTheory.cond, integral_smul_measure,
      ENNReal.toReal_inv, smul_eq_mul, ← integral_indicator measurableSet_closedBall]
    rfl
  simp_rw [he]
  simpa only [inv_one, one_mul, Pi.mul_apply] using
    ((tendsto_cutoffMass μ R).inv₀ one_ne_zero).mul ht

theorem damped_whitened_probability_tendsto {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {ε : ℕ → ℝ} (hε : ∀ k, 0 ≤ ε k)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => dampedWhitenedProbability hμ (ε k) (hε k)) atTop
      (𝓝 (probabilityOf μ hμ.isProb)) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  change Tendsto (fun k => ∫ x, f x ∂whitenedMeasure (quadraticDamping μ (ε k)))
    atTop (𝓝 (∫ x, f x ∂μ))
  exact tendsto_integral_bounded_affine_damping μ hε hεlim
    (tendsto_whitening_coefficient_quadraticDamping_nonneg hμ hε hεlim)
    f.continuous f.norm_coe_le_norm

theorem gaussian_probability_tendsto (μ : Measure (Space n)) [IsProbabilityMeasure μ] :
    Tendsto (fun k => gaussianProbability μ (cutoffScale k)) atTop
      (𝓝 μ.toProbabilityMeasure) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  change Tendsto (fun k => ∫ x, f x ∂isotropicGaussianSmoothing μ (cutoffScale k))
    atTop (𝓝 (∫ x, f x ∂μ))
  exact tendsto_integral_bounded_gaussian_smoothing μ f.continuous f.norm_coe_le_norm

theorem cutoff_whitened_probability_tendsto {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) :
    Tendsto (fun k => cutoffWhitenedProbability hμ hR k) atTop
      (𝓝 (probabilityOf μ hμ.isProb)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  change Tendsto (fun k => ∫ x, f x ∂whitenedBallCutoffMeasure μ R k)
    atTop (𝓝 (∫ x, f x ∂μ))
  exact tendsto_integral_bounded_whitened_cutoff hμ hR f.continuous f.norm_coe_le_norm

end KLSConstantImprovement.ActualTargetWeakApproximation
#print axioms KLSConstantImprovement.ActualTargetWeakApproximation.tendsto_integral_bounded_affine_damping
#print axioms KLSConstantImprovement.ActualTargetWeakApproximation.tendsto_integral_bounded_gaussian_smoothing
#print axioms KLSConstantImprovement.ActualTargetWeakApproximation.tendsto_integral_bounded_whitened_cutoff
#print axioms KLSConstantImprovement.ActualTargetWeakApproximation.damped_whitened_probability_tendsto
#print axioms KLSConstantImprovement.ActualTargetWeakApproximation.gaussian_probability_tendsto
#print axioms KLSConstantImprovement.ActualTargetWeakApproximation.cutoff_whitened_probability_tendsto
