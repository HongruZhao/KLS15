import KLSConstantImprovement.ActualAnchoredLipschitzCompactness405
import KLS.WeightedCaccioppoli
import KLS.ConvexHessian
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Locally uniform compactness of centered C1,1 source potentials under a
common gradient-Lipschitz bound, with no common bound on their target radii.
The scalar potential is reconstructed from the actual limiting gradients,
so its C1 derivative is proved rather than asserted. -/
noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped Topology BigOperators NNReal Interval
namespace KLSConstantImprovement.ActualC11SourceCompactness405
open KLS ActualAnchoredLipschitzCompactness405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

def radialPrimitive (g : Space n → Space n) (x : Space n) : ℝ :=
  ∫ t : ℝ in (0 : ℝ)..1, inner ℝ x (g (t • x))

theorem radialPrimitive_gradient (f : Space n → ℝ) (hf : ContDiff ℝ 1 f) (h0 : f 0 = 0)
    (x : Space n) : radialPrimitive (gradient f) x = f x := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => f (s • x))
      (inner ℝ x (gradient f (t • x))) t := by
    have h : HasDerivAt (fun s : ℝ => f (s • x))
        (fderiv ℝ f (t • x) x) t :=
      (hf.differentiable (by norm_num) (t • x)).hasFDerivAt.comp_hasDerivAt t
        (by simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const x)
    have he : fderiv ℝ f (t • x) x = inner ℝ x (gradient f (t • x)) := by
      rw [← inner_gradient_left, real_inner_comm]
    rw [he] at h
    exact h
  have hc : Continuous (fun t : ℝ => inner ℝ x (gradient f (t • x))) :=
    continuous_const.inner ((continuous_gradient_of_contDiff hf).comp (by fun_prop))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable 0 1)
  simpa only [radialPrimitive, one_smul, zero_smul, h0, sub_zero] using hi

theorem tendsto_radialPrimitive {L : ℝ≥0} {g : ℕ → Space n → Space n}
    {v : Space n → Space n} (hL : ∀ k, LipschitzWith L (g k)) (h0 : ∀ k, g k 0 = 0)
    (hv : LipschitzWith L v) (hv0 : v 0 = 0)
    (hlim : ∀ x, Tendsto (fun k => g k x) atTop (𝓝 (v x))) (x : Space n) :
    Tendsto (fun k => radialPrimitive (g k) x) atTop (𝓝 (radialPrimitive v x)) := by
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  simp only [radialPrimitive, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (L : ℝ) * ‖x‖ ^ 2)
  · intro k
    exact (continuous_const.inner ((hL k).continuous.comp (by fun_prop))).aestronglyMeasurable
  · exact integrable_const _
  · intro k
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 ≤ t := ht.1.le
    have htn : ‖t • x‖ ≤ ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    calc
      ‖inner ℝ x (g k (t • x))‖ ≤ ‖x‖ * ‖g k (t • x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * ((L : ℝ) * ‖t • x‖) :=
        mul_le_mul_of_nonneg_left (anchored_lipschitz_bound (hL k) (h0 k) _) (norm_nonneg _)
      _ ≤ ‖x‖ * ((L : ℝ) * ‖x‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htn L.coe_nonneg) (norm_nonneg _)
      _ = _ := by ring
  · exact Eventually.of_forall fun t => tendsto_const_nhds.inner (hlim (t • x))

theorem exists_subseq_centered_C11_potentials (L : ℝ≥0) (f : ℕ → Space n → ℝ)
    (hf : ∀ k, ContDiff ℝ 1 (f k))
    (hc : ∀ k, ConvexOn ℝ univ (f k))
    (hf0 : ∀ k, f k 0 = 0)
    (hg0 : ∀ k, gradient (f k) 0 = 0)
    (hL : ∀ k, LipschitzWith L (gradient (f k))) :
    ∃ (φ : Space n → ℝ) (s : ℕ → ℕ),
      StrictMono s ∧ ContDiff ℝ 1 φ ∧ ConvexOn ℝ univ φ ∧ φ 0 = 0 ∧
      gradient φ 0 = 0 ∧ LipschitzWith L (gradient φ) ∧
      (∀ x, Tendsto (fun k => f (s k) x) atTop (𝓝 (φ x))) ∧
      TendstoLocallyUniformly (fun k => gradient (f (s k))) (gradient φ) atTop := by
  obtain ⟨v, s, hs, hv, hv0, hloc, hcomp⟩ :=
    exists_subseq_anchoredLipschitzMaps L (fun k => gradient (f k)) hL hg0
  let φ : Space n → ℝ := radialPrimitive v
  have hvlim (x : Space n) : Tendsto (fun k => gradient (f (s k)) x) atTop (𝓝 (v x)) :=
    hloc.tendstoLocallyUniformlyOn.tendsto_at (mem_univ x)
  have hflim (x : Space n) : Tendsto (fun k => f (s k) x) atTop (𝓝 (φ x)) := by
    have ht := tendsto_radialPrimitive (fun k => hL (s k)) (fun k => hg0 (s k)) hv hv0 hvlim x
    simpa only [radialPrimitive_gradient _ (hf _) (hf0 _)] using ht
  have hdlim : TendstoLocallyUniformly
      (fun k x => fderiv ℝ (f (s k)) x)
      (fun x => (InnerProductSpace.toDual ℝ (Space n)) (v x)) atTop := by
    have ht := (InnerProductSpace.toDual ℝ (Space n)).isometry.uniformContinuous.comp_tendstoLocallyUniformly hloc
    have he (k : ℕ) (x : Space n) :
        (InnerProductSpace.toDual ℝ (Space n)) (gradient (f (s k)) x) =
          fderiv ℝ (f (s k)) x :=
      (InnerProductSpace.toDual ℝ (Space n)).apply_symm_apply _
    simpa only [Function.comp_def, he] using ht
  have hd (x : Space n) : HasFDerivAt φ
      ((InnerProductSpace.toDual ℝ (Space n)) (v x)) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ hdlim.tendstoLocallyUniformlyOn
      (fun k z _ => (hf (s k)).differentiable (by norm_num) z |>.hasFDerivAt)
      (fun z _ => hflim z) (mem_univ x)
  have hφ : ContDiff ℝ 1 φ := contDiff_one_iff_hasFDerivAt.mpr
    ⟨fun x => (InnerProductSpace.toDual ℝ (Space n)) (v x),
      (InnerProductSpace.toDual ℝ (Space n)).continuous.comp hv.continuous, hd⟩
  have hgrad : gradient φ = v := by
    funext x
    simp only [gradient, (hd x).fderiv]
    exact (InnerProductSpace.toDual ℝ (Space n)).symm_apply_apply _
  have hcφ : ConvexOn ℝ univ φ :=
    (isClosed_setOfPred_convexOn (s := (univ : Set (Space n)))).mem_of_tendsto
      (tendsto_pi_nhds.mpr hflim) (Eventually.of_forall fun k => hc (s k))
  have hφ0 : φ 0 = 0 := by simp [φ, radialPrimitive]
  refine ⟨φ, s, hs, hφ, hcφ, hφ0, ?_, ?_, hflim, ?_⟩
  · rw [hgrad]
    exact hv0
  · rw [hgrad]
    exact hv
  · rw [hgrad]
    exact hloc

end KLSConstantImprovement.ActualC11SourceCompactness405
#print axioms KLSConstantImprovement.ActualC11SourceCompactness405.radialPrimitive_gradient
#print axioms KLSConstantImprovement.ActualC11SourceCompactness405.tendsto_radialPrimitive
#print axioms KLSConstantImprovement.ActualC11SourceCompactness405.exists_subseq_centered_C11_potentials
