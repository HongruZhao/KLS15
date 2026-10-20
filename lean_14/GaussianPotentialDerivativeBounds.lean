import GaussianPotentialHessian
import CompactCumulantBound
import KLS.CumulantAffine

/-! Uniform higher derivative bounds for actual compact-source Gaussian
potentials. The posterior laws retain the original bounded support, and
their actual cumulant tensors control the derivatives. -/

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Metric Matrix
open scoped ENNReal ContDiff Topology RealInnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ}

lemma tiltLogLaplace_tilted
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {q : Space n → ℝ} (hq : Continuous q) (z : Space n) :
    tiltLogLaplace (μ.tilted q) z =
      Real.log (tiltPartition μ (fun y => q y + inner ℝ z y)) -
        Real.log (tiltPartition μ q) := by
  unfold tiltLogLaplace tiltPartition
  rw [integral_exp_tilted]
  simp only [Pi.add_apply]
  exact Real.log_div (tiltPartition_pos hc (q := fun y => q y + inner ℝ z y)
    (by fun_prop)).ne' (tiltPartition_pos hc hq).ne'

/-- The actual translated potential is a quadratic polynomial minus the
log-Laplace transform of its actual bounded-source posterior law. -/
theorem gaussianSmoothedPotential_translate
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0) (x z : Space n) :
    gaussianSmoothedPotential μ r (x + z) =
      gaussianSmoothedPotential μ r x + (r⁻¹) ^ 2 * inner ℝ x z +
        (r⁻¹) ^ 2 / 2 * ‖z‖ ^ 2 -
        tiltLogLaplace (μ.tilted (gaussianPosteriorScore r x)) ((r⁻¹) ^ 2 • z) := by
  have hq : Continuous (gaussianPosteriorScore r x) := by
    unfold gaussianPosteriorScore
    fun_prop
  have he : (fun y => gaussianPosteriorScore r x y + inner ℝ ((r⁻¹) ^ 2 • z) y) =
      gaussianPosteriorScore r (x + z) := by
    funext y
    simp only [gaussianPosteriorScore, inner_add_left, inner_smul_left, RCLike.conj_to_real]
    ring
  rw [tiltLogLaplace_tilted hc hq, he,
    gaussianSmoothedPotential_eq_quadratic_sub_logPartition hc hr,
    gaussianSmoothedPotential_eq_quadratic_sub_logPartition hc hr,
    norm_add_sq_real]
  ring

lemma iteratedFDeriv_norm_sq_eq_zero {m : ℕ} (hm : 3 ≤ m) (x : Space n) :
    iteratedFDeriv ℝ m (fun y : Space n => ‖y‖ ^ 2) x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm 3 k, show k + 3 = (k + 2) + 1 by omega]
  ext h
  rw [iteratedFDeriv_succ_apply_right]
  have hd : fderiv ℝ (fun y : Space n => ‖y‖ ^ 2) =
      ⇑((2 : ℝ) • (innerSL ℝ : Space n →L[ℝ] Space n →L[ℝ] ℝ)) := by
    funext y
    rw [fderiv_norm_sq_apply]
    ext z
    simp
  rw [hd, iteratedFDeriv_clm_eq_zero _ (by omega)]
  rfl

/-- At every target point, all derivatives above the quadratic order are
the actual cumulant tensors of the bounded-source posterior, with scale. -/
theorem iteratedFDeriv_gaussianSmoothedPotential_eq_cumulant
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0)
    {m : ℕ} (hm : 3 ≤ m) (x : Space n) :
    iteratedFDeriv ℝ m (gaussianSmoothedPotential μ r) x =
      -(((r⁻¹) ^ 2) ^ m •
        cumulantTensor (μ.tilted (gaussianPosteriorScore r x)) m) := by
  let V := gaussianSmoothedPotential μ r
  let a : ℝ := (r⁻¹) ^ 2
  let ν := μ.tilted (gaussianPosteriorScore r x)
  let L : Space n →L[ℝ] ℝ := a • innerSL ℝ x
  let Q : Space n → ℝ := fun z => V x + L z + (a / 2) * ‖z‖ ^ 2
  have hq : Continuous (gaussianPosteriorScore r x) := by
    unfold gaussianPosteriorScore
    fun_prop
  have := tilted_isProbability_of_compact_support hc hq
  have hν : IsCompact ν.support := by dsimp [ν]; rwa [tilted_support_eq hc hq]
  have hLap : ContDiff ℝ (⊤ : ℕ∞) (tiltLogLaplace ν) := contDiff_tiltLogLaplace hν
  have hL : ContDiff ℝ m (fun z => V x + L z) := contDiff_const.add L.contDiff
  have hNsmooth : ContDiff ℝ m (fun z : Space n => ‖z‖ ^ 2) :=
    contDiff_norm_sq ℝ
  have hN : ContDiff ℝ m (fun z : Space n => (a / 2) * ‖z‖ ^ 2) :=
    contDiff_const.mul hNsmooth
  have hQ : ContDiff ℝ m Q := hL.add hN
  have hcomp : ContDiff ℝ m (fun z : Space n => tiltLogLaplace ν (a • z)) :=
    (hLap.comp (by fun_prop)).of_le (by simp)
  have hQzero : iteratedFDeriv ℝ m Q 0 = 0 := by
    change iteratedFDeriv ℝ m ((fun z => V x + L z) +
      (fun z : Space n => (a / 2) * ‖z‖ ^ 2)) 0 = 0
    rw [iteratedFDeriv_add_apply hL.contDiffAt hN.contDiffAt,
      fun_iteratedFDeriv_add_apply contDiffAt_const L.contDiff.contDiffAt,
      iteratedFDeriv_const_of_ne (by omega : m ≠ 0),
      iteratedFDeriv_clm_eq_zero L (by omega)]
    simp only [Pi.zero_apply, zero_add]
    have hNs : (fun z : Space n => (a / 2) * ‖z‖ ^ 2) =
        (a / 2) • (fun z : Space n => ‖z‖ ^ 2) := rfl
    rw [hNs, iteratedFDeriv_const_smul_apply hNsmooth.contDiffAt,
      iteratedFDeriv_norm_sq_eq_zero hm, smul_zero]
  have he : (fun z : Space n => V (x + z)) =
      Q - (fun z => tiltLogLaplace ν (a • z)) := by
    funext z
    simpa only [Q, L, V, ν, a, Pi.sub_apply,
      _root_.smul_apply, innerSL_apply_apply, smul_eq_mul] using
      gaussianSmoothedPotential_translate hc hr x z
  have hscale : iteratedFDeriv ℝ m (fun z : Space n => tiltLogLaplace ν (a • z)) 0 =
      a ^ m • cumulantTensor ν m := by
    simpa only [zero_smul, smul_zero, cumulantTensor] using
      congrFun (iteratedFDeriv_comp_const_smul a (hLap.of_le (by simp : (m : ℕ∞ω) ≤ ↑(⊤ : ℕ∞))))
        (0 : Space n)
  change iteratedFDeriv ℝ m V x = -(a ^ m • cumulantTensor ν m)
  calc
    _ = iteratedFDeriv ℝ m (fun z => V (x + z)) 0 := by
      simpa only [add_zero] using (iteratedFDeriv_comp_add_left m x (0 : Space n)).symm
    _ = _ := by
      rw [he, iteratedFDeriv_sub_apply hQ.contDiffAt hcomp.contDiffAt,
        hQzero, hscale, zero_sub]

/-- Higher derivatives are globally uniformly bounded. The constant may
depend on the original support radius, Gaussian scale and derivative order. -/
theorem norm_iteratedFDeriv_gaussianSmoothedPotential_le
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {R : ℝ} (hR : 0 ≤ R)
    (hball : μ.support ⊆ closedBall (0 : Space n) R)
    {r : ℝ} (hr : r ≠ 0) {m : ℕ} (hm : 3 ≤ m) (x : Space n) :
    ‖iteratedFDeriv ℝ m (gaussianSmoothedPotential μ r) x‖ ≤
      ((r⁻¹) ^ 2) ^ m * compactCumulantBound R m := by
  have hq : Continuous (gaussianPosteriorScore r x) := by
    unfold gaussianPosteriorScore
    fun_prop
  rw [iteratedFDeriv_gaussianSmoothedPotential_eq_cumulant hc hr hm,
    norm_neg, norm_smul, Real.norm_of_nonneg (pow_nonneg (sq_nonneg _) _)]
  exact mul_le_mul_of_nonneg_left
    (norm_cumulantTensor_tilted_le_of_support_ball hc hR hball hq m)
    (pow_nonneg (sq_nonneg _) _)

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.gaussianSmoothedPotential_translate
#print axioms KLS.DeterministicBridgeIntegration.iteratedFDeriv_norm_sq_eq_zero
#print axioms KLS.DeterministicBridgeIntegration.iteratedFDeriv_gaussianSmoothedPotential_eq_cumulant
#print axioms KLS.DeterministicBridgeIntegration.norm_iteratedFDeriv_gaussianSmoothedPotential_le
