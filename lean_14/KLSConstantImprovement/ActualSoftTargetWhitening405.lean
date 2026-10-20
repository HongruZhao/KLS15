import KLSConstantImprovement.ActualSoftTargetNormalization405
import KLSConstantImprovement.ActualSecondMomentWhitening405
import KLS.DampedWhiteningWeakLimit

/-! Actual first/second moments, covariance whitening and weak probability
convergence for the soft-barrier growing-ball targets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix Metric
open scoped Topology NNReal ContDiff ENNReal BigOperators
namespace KLSConstantImprovement.ActualSoftTargetWhitening405
open KLS ActualConvexSoftBarrier405 ActualSoftTargetIntegrals405 ActualStrongPotentialMoments405
open ActualSoftTargetNormalization405 ActualSecondMomentWhitening405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
variable {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
variable {κ : ℝ} (hκ : 0 < κ) (hs : StrongConvexOn univ κ V)
variable {K : Set (Space n)} (hK : IsClosed K) (hne : K.Nonempty) (hc : Convex ℝ K)
variable (heq : μ = (potentialMeasure V).restrict K)
include hμ hV hκ hs hK hne hc heq

theorem softTarget_first_moment (i : Fin n) :
    Tendsto (fun j => ∫ x : Space n, x i ∂softTargetMeasure V K j) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  letI := strongPotential_isFiniteMeasure (hV.of_le (by simp)) hκ hs
  have hi := strongPotential_coordinate_product_integrable (hV.of_le (by simp)) hκ hs
    (fun _ : Fin 1 => some i)
  have hi' : Integrable (fun x : Space n => x i) (potentialMeasure V) := by
    simpa only [Fin.prod_univ_succ, Fin.prod_univ_zero, coordinateWithConstant, mul_one] using hi
  simpa only [hμ.isotropic.integral_coordinate] using
    tendsto_softTargetMeasure_integral hV.continuous.measurable K hK hne heq hi'

theorem softTarget_second_moment (i j : Fin n) :
    Tendsto (fun k => ∫ x : Space n, x i*x j ∂softTargetMeasure V K k) atTop
      (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) i j)) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  letI := strongPotential_isFiniteMeasure (hV.of_le (by simp)) hκ hs
  have hi := strongPotential_coordinate_product_integrable (hV.of_le (by simp)) hκ hs
    ![some i, some j]
  have hi' : Integrable (fun x : Space n => x i*x j) (potentialMeasure V) := by
    simpa [Fin.prod_univ_succ, coordinateWithConstant] using hi
  simpa only [hμ.isotropic.integral_coordinate_mul, Matrix.one_apply] using
    tendsto_softTargetMeasure_integral hV.continuous.measurable K hK hne heq hi'

theorem softTarget_whitening_coefficients (i : Fin n) (j : Option (Fin n)) :
    Tendsto (fun k =>
      let ν := softTargetMeasure V K k
      let Q := inverseSqrtMatrix (covarianceMatrix ν)
      affineCoordinateCoefficient Q (-matrixAction Q (∫ x, x ∂ν)) i j) atTop
        (𝓝 (affineCoordinateCoefficient 1 0 i j)) := by
  letI := strongPotential_isFiniteMeasure (hV.of_le (by simp)) hκ hs
  letI : ∀ k, IsProbabilityMeasure (softTargetMeasure V K k) :=
    fun k => softTargetMeasure_probability hV.continuous.measurable K k
  exact whiteningCoefficient_tendsto hμ
    (softTargetMeasure_logConcave hV hκ.le hs hK hne hc)
    (softTarget_first_moment hμ hV hκ hs hK hne hc heq)
    (softTarget_second_moment hμ hV hκ hs hK hne hc heq) i j

theorem softTarget_whitening_eventual :
    ∀ᶠ k in atTop,
      admissibleMeasure (whitenedMeasure (softTargetMeasure V K k)) ∧
      (covarianceMatrix (softTargetMeasure V K k)).PosDef ∧
      ‖matrixAction (inverseSqrtMatrix (covarianceMatrix (softTargetMeasure V K k)))‖ ≤ 2 := by
  letI := strongPotential_isFiniteMeasure (hV.of_le (by simp)) hκ hs
  letI : ∀ k, IsProbabilityMeasure (softTargetMeasure V K k) :=
    fun k => softTargetMeasure_probability hV.continuous.measurable K k
  have hν := softTargetMeasure_logConcave hV hκ.le hs hK hne hc
  have h1 := softTarget_first_moment hμ hV hκ hs hK hne hc heq
  have h2 := softTarget_second_moment hμ hV hκ hs hK hne hc heq
  exact (eventually_whitened_admissible hμ hν h1 h2).and
    ((eventually_covarianceMatrix_posDef hμ hν h1 h2).and
      (eventually_whiteningMatrix_norm_le_two hμ hν h1 h2))

theorem tendsto_integral_bounded_affine_softTarget
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {b : ℕ → Space n}
    (hcoeff : ∀ i j, Tendsto (fun k => affineCoordinateCoefficient (A k) (b k) i j)
      atTop (𝓝 (affineCoordinateCoefficient 1 0 i j)))
    {f : Space n → ℝ} (hf : Continuous f) {B : ℝ} (hb : ∀ x, ‖f x‖ ≤ B) :
    Tendsto (fun k => ∫ x, f x ∂affineMatrixMeasure (softTargetMeasure V K k) (A k) (b k))
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  letI := strongPotential_isFiniteMeasure (hV.of_le (by simp)) hκ hs
  letI : ∀ k, IsProbabilityMeasure (softTargetMeasure V K k) :=
    fun k => softTargetMeasure_probability hV.continuous.measurable K k
  have hmap (x : Space n) : Tendsto (fun k => affineMatrixMap (A k) (b k) x) atTop (𝓝 x) :=
    tendsto_affineMatrixMap_of_coefficients hcoeff x
  have ht : Tendsto (fun k => ∫ x,
      f (affineMatrixMap (A k) (b k) x) * softTargetWeight K k x ∂potentialMeasure V) atTop
      (𝓝 (∫ x, f x * K.indicator (fun _ => (1 : ℝ)) x ∂potentialMeasure V)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Space n => B)
    · intro k
      exact (hf.comp (affineMatrixMap (A k) (b k)).continuous).aestronglyMeasurable.mul
        (softTargetWeight_measurable K k).aestronglyMeasurable
    · exact integrable_const _
    · intro k
      exact Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs (softTargetWeight K k x),
          abs_of_nonneg (softTargetWeight_bounds K k x).1]
        exact (mul_le_of_le_one_right (norm_nonneg _) (softTargetWeight_bounds K k x).2).trans (hb _)
    · exact Eventually.of_forall fun x =>
        (hf.continuousAt.tendsto.comp (hmap x)).mul (softTargetWeight_tendsto K hK hne x)
  have htarget : (∫ x, f x * K.indicator (fun _ => (1 : ℝ)) x ∂potentialMeasure V) = ∫ x, f x ∂μ := by
    rw [heq, ← integral_indicator hK.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · simp only [indicator_of_mem hx, mul_one]
      · simp only [indicator_of_notMem hx, mul_zero]
  rw [htarget] at ht
  have hd : Tendsto (softTargetMass V K) atTop (𝓝 1) := by
    have h := tendsto_rawSoftTargetMeasure_integral hV.continuous.measurable K hK hne (integrable_const (1 : ℝ))
    rw [← heq] at h
    change Tendsto (fun j => ∫ _x, (1 : ℝ) ∂rawSoftTargetMeasure V K j) atTop (𝓝 1)
    simpa only [integral_const, probReal_univ, smul_eq_mul, mul_one] using h
  have he (k : ℕ) : (∫ x, f x ∂affineMatrixMeasure (softTargetMeasure V K k) (A k) (b k)) =
      (∫ x, f (affineMatrixMap (A k) (b k) x) * softTargetWeight K k x ∂potentialMeasure V) /
        softTargetMass V K k := by
    rw [affineMatrixMeasure, integral_map (by fun_prop) hf.aestronglyMeasurable,
      softTargetMeasure_integral hV.continuous.measurable,
      rawSoftTargetMeasure_integral hV.continuous.measurable]
  simpa only [he, div_one, Pi.div_def] using ht.div hd one_ne_zero

theorem tendsto_integral_bounded_whitened_softTarget
    {f : Space n → ℝ} (hf : Continuous f) {B : ℝ} (hb : ∀ x, ‖f x‖ ≤ B) :
    Tendsto (fun k => ∫ x, f x ∂whitenedMeasure (softTargetMeasure V K k)) atTop
      (𝓝 (∫ x, f x ∂μ)) :=
  tendsto_integral_bounded_affine_softTarget hμ hV hκ hs hK hne hc heq
    (softTarget_whitening_coefficients hμ hV hκ hs hK hne hc heq) hf hb

theorem softTarget_whitened_coordinate_product_tendsto
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → Fin n) :
    Tendsto (fun k => ∫ x, ∏ a, x (r a) ∂whitenedMeasure (softTargetMeasure V K k)) atTop
      (𝓝 (∫ x, ∏ a, x (r a) ∂μ)) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  letI := strongPotential_isFiniteMeasure (hV.of_le (by simp)) hκ hs
  letI : ∀ k, IsProbabilityMeasure (softTargetMeasure V K k) :=
    fun k => softTargetMeasure_probability hV.continuous.measurable K k
  apply coordinate_moment_whitened_tendsto hμ
    (softTargetMeasure_logConcave hV hκ.le hs hK hne hc)
    (softTarget_first_moment hμ hV hκ hs hK hne hc heq)
    (softTarget_second_moment hμ hV hκ hs hK hne hc heq) r
  intro s
  exact tendsto_softTargetMeasure_integral hV.continuous.measurable K hK hne heq
    (strongPotential_coordinate_product_integrable (hV.of_le (by simp)) hκ hs s)

end KLSConstantImprovement.ActualSoftTargetWhitening405
#print axioms KLSConstantImprovement.ActualSoftTargetWhitening405.softTarget_first_moment
#print axioms KLSConstantImprovement.ActualSoftTargetWhitening405.softTarget_second_moment
#print axioms KLSConstantImprovement.ActualSoftTargetWhitening405.softTarget_whitening_eventual
#print axioms KLSConstantImprovement.ActualSoftTargetWhitening405.tendsto_integral_bounded_whitened_softTarget
#print axioms KLSConstantImprovement.ActualSoftTargetWhitening405.softTarget_whitened_coordinate_product_tendsto
