import KLS.GaussianSmoothingGradient
import KLS.LogTiltCumulants
import KLS.ConvexHessian

/-! The upper Hessian bound for the actual Gaussian convolution potential.
The source is any compactly supported probability measure; no log-concavity,
isotropy, spectral gap, or Hessian bound is assumed. The posterior measure
is the actual normalized exponential tilt of that source. -/

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Metric Matrix
open scoped ENNReal ContDiff Topology RealInnerProductSpace BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ}

def gaussianPosteriorScore (r : ℝ) (x y : Space n) : ℝ :=
  (r⁻¹) ^ 2 * inner ℝ x y - (r⁻¹) ^ 2 / 2 * ‖y‖ ^ 2

lemma scaledGaussianKernel_sub_eq (r : ℝ) (x y : Space n) :
    scaledGaussianKernel n r (x - y) =
      scaledGaussianKernel n r x * Real.exp (gaussianPosteriorScore r x y) := by
  rw [scaledGaussianKernel_eq_norm_sq, scaledGaussianKernel_eq_norm_sq,
    mul_assoc, ← Real.exp_add, norm_sub_sq_real]
  congr 2
  unfold gaussianPosteriorScore
  ring

theorem gaussianSmoothedDensity_eq_kernel_mul_tiltPartition
    (μ : Measure (Space n)) (r : ℝ) (x : Space n) :
    gaussianSmoothedDensity μ r x =
      scaledGaussianKernel n r x * tiltPartition μ (gaussianPosteriorScore r x) := by
  unfold gaussianSmoothedDensity tiltPartition
  simp_rw [scaledGaussianKernel_sub_eq]
  exact integral_const_mul _ _

theorem gaussianSmoothedPotential_eq_quadratic_sub_logPartition
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0) (x : Space n) :
    gaussianSmoothedPotential μ r x =
      (r⁻¹) ^ 2 / 2 * ‖x‖ ^ 2 +
        n * Real.log (Real.sqrt (2 * Real.pi)) - Real.log |(r ^ n)⁻¹| -
        Real.log (tiltPartition μ (gaussianPosteriorScore r x)) := by
  have hq : Continuous (gaussianPosteriorScore r x) := by
    unfold gaussianPosteriorScore
    fun_prop
  rw [gaussianSmoothedPotential, gaussianSmoothedDensity_eq_kernel_mul_tiltPartition,
    Real.log_mul (scaledGaussianKernel_pos hr x).ne' (tiltPartition_pos hc hq).ne',
    scaledGaussianKernel_eq_norm_sq,
    Real.log_mul (abs_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hr))) (Real.exp_ne_zero _),
    Real.log_exp]
  ring

lemma gaussianSmoothedPotential_line_derivative
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0)
    (x v : Space n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => gaussianSmoothedPotential μ r (x + u • v))
      ((r⁻¹) ^ 2 * (inner ℝ v x + t * ‖v‖ ^ 2) -
        tiltAverage μ
          (fun y => gaussianPosteriorScore r x y + t * ((r⁻¹) ^ 2 * inner ℝ v y))
          (fun y => (r⁻¹) ^ 2 * inner ℝ v y)) t := by
  let a : ℝ := (r⁻¹) ^ 2
  let q : Space n → ℝ := gaussianPosteriorScore r x
  let s : Space n → ℝ := fun y => a * inner ℝ v y
  let C : ℝ := a / 2 * ‖x‖ ^ 2 +
    n * Real.log (Real.sqrt (2 * Real.pi)) - Real.log |(r ^ n)⁻¹|
  let Q : ℝ → ℝ := fun u => a * inner ℝ v x * u + a / 2 * ‖v‖ ^ 2 * u ^ 2 + C
  have hq : Continuous q := by
    change Continuous (fun y => (r⁻¹) ^ 2 * inner ℝ x y - (r⁻¹) ^ 2 / 2 * ‖y‖ ^ 2)
    fun_prop
  have hs : Continuous s := by dsimp [s]; fun_prop
  have heq (u : ℝ) : gaussianPosteriorScore r (x + u • v) =
      fun y => q y + u * s y := by
    funext y
    dsimp [gaussianPosteriorScore, q, s, a]
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
    ring
  have hline : (fun u : ℝ => gaussianSmoothedPotential μ r (x + u • v)) =
      fun u => Q u - Real.log (tiltPartition μ (fun y => q y + u * s y)) := by
    funext u
    rw [gaussianSmoothedPotential_eq_quadratic_sub_logPartition hc hr, heq]
    dsimp [Q, C, a]
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      inner_smul_right, real_inner_comm x v]
    ring
  have hQ : HasDerivAt Q (a * (inner ℝ v x + t * ‖v‖ ^ 2)) t := by
    convert! (((hasDerivAt_id t).const_mul (a * inner ℝ v x)).add
      (((hasDerivAt_id t).pow 2).const_mul (a / 2 * ‖v‖ ^ 2))).add_const C using 1
    norm_num
    ring
  rw [hline]
  exact hQ.sub (hasDerivAt_log_tiltPartition hc hq hs t)

/-- The true second derivative equals Gaussian curvature minus the posterior
variance of the score. Compact support discharges all moment conditions. -/
theorem secondFrechet_gaussianSmoothedPotential_eq
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0) (x v : Space n) :
    fderiv ℝ (fderiv ℝ (gaussianSmoothedPotential μ r)) x v v =
      (r⁻¹) ^ 2 * ‖v‖ ^ 2 -
        ProbabilityTheory.variance (fun y => (r⁻¹) ^ 2 * inner ℝ v y)
          (μ.tilted (gaussianPosteriorScore r x)) := by
  let V := gaussianSmoothedPotential μ r
  let a : ℝ := (r⁻¹) ^ 2
  let q : Space n → ℝ := gaussianPosteriorScore r x
  let s : Space n → ℝ := fun y => a * inner ℝ v y
  have hq : Continuous q := by
    change Continuous (fun y => (r⁻¹) ^ 2 * inner ℝ x y - (r⁻¹) ^ 2 / 2 * ‖y‖ ^ 2)
    fun_prop
  have hs : Continuous s := by dsimp [s]; fun_prop
  have hV : ContDiff ℝ 2 V := (gaussianSmoothedPotential_contDiff hc hr).of_le (by simp)
  have hdV : Differentiable ℝ V := hV.differentiable (by norm_num)
  have hddV : Differentiable ℝ (fderiv ℝ V) :=
    (hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hder : (fun t : ℝ => fderiv ℝ V (x + t • v) v) =
      fun t => a * (inner ℝ v x + t * ‖v‖ ^ 2) -
        tiltAverage μ (fun y => q y + t * s y) s := by
    funext t
    have hv : HasFDerivAt V (fderiv ℝ V (x + t • v)) (x + t • v) :=
      (hdV (x + t • v)).hasFDerivAt
    have hd : HasDerivAt (fun u : ℝ => V (x + u • v))
        (fderiv ℝ V (x + t • v) v) t := by
      simpa only [Function.comp_def] using
        hv.comp_hasDerivAt t (hasDerivAt_affine_line x v t)
    exact hd.unique (gaussianSmoothedPotential_line_derivative hc hr x v t)
  have hdmap := (hddV (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_affine_line x v 0)
  have hdmap' : HasDerivAt (fun t : ℝ => fderiv ℝ V (x + t • v))
      (fderiv ℝ (fderiv ℝ V) x v) 0 := by
    convert! hdmap using 1
    simp
  have hactual := hdmap'.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hlinear : HasDerivAt (fun t : ℝ => a * (inner ℝ v x + t * ‖v‖ ^ 2))
      (a * ‖v‖ ^ 2) 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).mul_const (‖v‖ ^ 2)).const_add
      (inner ℝ v x)).const_mul a using 1
    simp
  have hmean := hasDerivAt_tiltAverage hc hq hs
    (integrable_of_continuous_compact_support_measure hc hs) (0 : ℝ)
  have hsecond := hlinear.sub hmean
  have hactual' : HasDerivAt (fun t : ℝ => fderiv ℝ V (x + t • v) v)
      (fderiv ℝ (fderiv ℝ V) x v v) 0 := by simpa using hactual
  rw [hder] at hactual'
  have he := hactual'.unique hsecond
  have := tilted_isProbability_of_compact_support hc hq
  have hvar : ProbabilityTheory.variance s (μ.tilted q) =
      tiltAverage μ q (fun y => s y * s y) - tiltAverage μ q s * tiltAverage μ q s := by
    rw [ProbabilityTheory.variance_eq_sub (memLp_two_continuous_tilted hc hq hs)]
    simp only [tiltAverage, Pi.pow_apply, pow_two]
  change fderiv ℝ (fderiv ℝ V) x v v = a * ‖v‖ ^ 2 -
    ProbabilityTheory.variance s (μ.tilted q)
  rw [hvar]
  simpa only [zero_mul, add_zero] using he

/-- The actual Gaussian-smoothed potential has Hessian at most r⁻² I,
without any convexity hypothesis on the source law. -/
theorem secondFrechet_gaussianSmoothedPotential_le
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0) (x v : Space n) :
    fderiv ℝ (fderiv ℝ (gaussianSmoothedPotential μ r)) x v v ≤
      (r⁻¹) ^ 2 * ‖v‖ ^ 2 := by
  rw [secondFrechet_gaussianSmoothedPotential_eq hc hr]
  exact sub_le_self _ (ProbabilityTheory.variance_nonneg _ _)

/-- The same identity with the Gaussian scale separated from the actual
posterior covariance form. -/
theorem secondFrechet_gaussianSmoothedPotential_eq_variance
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0) (x v : Space n) :
    fderiv ℝ (fderiv ℝ (gaussianSmoothedPotential μ r)) x v v =
      (r⁻¹) ^ 2 * ‖v‖ ^ 2 - ((r⁻¹) ^ 2) ^ 2 *
        ProbabilityTheory.variance (fun y => inner ℝ v y)
          (μ.tilted (gaussianPosteriorScore r x)) := by
  rw [secondFrechet_gaussianSmoothedPotential_eq hc hr, ProbabilityTheory.variance_const_mul]

/-- The upper bound is also stated in the actual coordinate matrix form
used by the released weighted calculus. -/
theorem coordinateHessian_gaussianSmoothedPotential_le
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0)
    (x : Space n) (w : Fin n → ℝ) :
    w ⬝ᵥ (coordinateHessian (gaussianSmoothedPotential μ r) x *ᵥ w) ≤
      (r⁻¹) ^ 2 * (w ⬝ᵥ w) := by
  let v : Space n := WithLp.toLp 2 w
  have heq : w ⬝ᵥ (coordinateHessian (gaussianSmoothedPotential μ r) x *ᵥ w) =
      ∑ i : Fin n, ∑ j : Fin n,
        coordinateHessian (gaussianSmoothedPotential μ r) x i j * v i * v j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change w i * (coordinateHessian (gaussianSmoothedPotential μ r) x i j * w j) =
      coordinateHessian (gaussianSmoothedPotential μ r) x i j * w i * w j
    ring
  have hnorm : ‖v‖ ^ 2 = w ⬝ᵥ w := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, v, pow_two]
  rw [heq, coordinateHessian_quadratic_eq
    ((gaussianSmoothedPotential_contDiff hc hr).of_le (by simp)), ← hnorm]
  exact secondFrechet_gaussianSmoothedPotential_le hc hr x v

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.secondFrechet_gaussianSmoothedPotential_eq
#print axioms KLS.DeterministicBridgeIntegration.secondFrechet_gaussianSmoothedPotential_le
#print axioms KLS.DeterministicBridgeIntegration.coordinateHessian_gaussianSmoothedPotential_le
