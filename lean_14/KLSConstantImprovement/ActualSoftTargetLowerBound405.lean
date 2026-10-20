import KLSConstantImprovement.ActualSoftTargetWhitening405
import Mathlib.Topology.Algebra.Group.Matrix

/-! A common GLOBAL lower bound for the actual affine soft-target potentials.
The nonnegative barrier only improves the original quadratic tangent bound;
the two normalization constants converge to zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix InnerProductSpace
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualSoftTargetLowerBound405
open KLS ActualConvexSoftBarrier405 ActualSoftTargetIntegrals405 ActualStrongPotentialMoments405
open ActualSoftTargetNormalization405 ActualSoftTargetWhitening405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem strongPotential_global_lower {V : Space n → ℝ} (hV : ContDiff ℝ 2 V)
    {κ : ℝ} (hκ : 0 < κ) (hs : StrongConvexOn univ κ V) :
    ∃ L : ℝ, ∀ x, L ≤ V x := by
  let G := ‖gradient V (0 : Space n)‖
  let C := G^2 / (2*κ)
  refine ⟨V 0-C, fun x => ?_⟩
  have hq := potential_quadratic_lower_bound hV
    (coordinateHessian_lower_of_strongConvexOn hV hs) x
  have hg : -(inner ℝ (gradient V 0) x) ≤ G*‖x‖ :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have hd : (2*κ)*C = G^2 := mul_div_cancel₀ _ (by positivity : (2*κ : ℝ) ≠ 0)
  have hq' := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ 2*κ)
  have hg' := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 2*κ)
  apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 2*κ)).mp
  nlinarith [sq_nonneg (κ*‖x‖-G)]

theorem softTargetMass_tendsto_one {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {V : Space n → ℝ} (hV : Measurable V) [IsFiniteMeasure (potentialMeasure V)]
    {K : Set (Space n)} (hK : IsClosed K) (hne : K.Nonempty)
    (heq : μ = (potentialMeasure V).restrict K) :
    Tendsto (softTargetMass V K) atTop (𝓝 1) := by
  have hh := tendsto_rawSoftTargetMeasure_integral hV K hK hne (integrable_const (1 : ℝ))
  rw [← heq] at hh
  change Tendsto (fun j => ∫ _x, (1 : ℝ) ∂rawSoftTargetMeasure V K j) atTop (𝓝 1)
  simpa only [integral_const, probReal_univ, smul_eq_mul, mul_one] using hh

theorem eventually_softTarget_affine_potential_lower
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    {κ : ℝ} (hκ : 0 < κ) (hs : StrongConvexOn univ κ V)
    {K : Set (Space n)} (hK : IsClosed K) (hne : K.Nonempty) (hc : Convex ℝ K)
    (heq : μ = (potentialMeasure V).restrict K) :
    ∃ L : ℝ, ∀ᶠ j in atTop,
      let ν := softTargetMeasure V K j
      let A := inverseSqrtMatrix (covarianceMatrix ν)
      let b := -matrixAction A (∫ x, x ∂ν)
      ∀ (hA : A.det ≠ 0) (p : Space n),
        L ≤ affineTransformedPotential (normalizedSoftTargetPotential V K j) A b hA p := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  letI := strongPotential_isFiniteMeasure (hV.of_le (by simp)) hκ hs
  let A : ℕ → Matrix (Fin n) (Fin n) ℝ := fun j =>
    inverseSqrtMatrix (covarianceMatrix (softTargetMeasure V K j))
  have hA : Tendsto A atTop (𝓝 (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [A, affineCoordinateCoefficient] using
      softTarget_whitening_coefficients hμ hV hκ hs hK hne hc heq i (some j)
  have hdetCont : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M.det) := continuous_id.matrix_det
  have hdet : Tendsto (fun j => (A j).det) atTop (𝓝 1) := by
    simpa only [Matrix.det_one, Function.comp_def] using hdetCont.continuousAt.tendsto.comp hA
  have hdetInv : Tendsto (fun j => |(A j).det⁻¹|) atTop (𝓝 1) := by
    simpa only [inv_one, abs_one] using (hdet.inv₀ one_ne_zero).abs
  have hlogdet : Tendsto (fun j => Real.log |(A j).det⁻¹|) atTop (𝓝 0) := by
    have hh := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hdetInv
    simpa only [Real.log_one, Function.comp_def] using hh
  have hlogMass : Tendsto (fun j => Real.log (softTargetMass V K j)) atTop (𝓝 0) := by
    have hh := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      (softTargetMass_tendsto_one hV.continuous.measurable hK hne heq)
    simpa only [Real.log_one, Function.comp_def] using hh
  obtain ⟨L, hL⟩ := strongPotential_global_lower (hV.of_le (by simp)) hκ hs
  refine ⟨L-2, ?_⟩
  filter_upwards [hlogMass.eventually (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0)),
    hlogdet.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with j hj hj'
  dsimp only
  intro hAj p
  dsimp only [affineTransformedPotential, normalizedSoftTargetPotential, softTargetPotential]
  have hb := convexSoftBarrier_nonneg K j
    ((affineMatrixEquiv (A j) (-matrixAction (A j) (∫ x, x ∂softTargetMeasure V K j)) hAj).symm p)
  have hv := hL
    ((affineMatrixEquiv (A j) (-matrixAction (A j) (∫ x, x ∂softTargetMeasure V K j)) hAj).symm p)
  change -1 < Real.log (softTargetMass V K j) at hj
  change Real.log |(A j).det⁻¹| < 1 at hj'
  linarith

end KLSConstantImprovement.ActualSoftTargetLowerBound405
#print axioms KLSConstantImprovement.ActualSoftTargetLowerBound405.strongPotential_global_lower
#print axioms KLSConstantImprovement.ActualSoftTargetLowerBound405.softTargetMass_tendsto_one
#print axioms KLSConstantImprovement.ActualSoftTargetLowerBound405.eventually_softTarget_affine_potential_lower
