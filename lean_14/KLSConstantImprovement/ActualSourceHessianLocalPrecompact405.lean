import KLSConstantImprovement.ActualLocalRawH1Precompact405
import KLSConstantImprovement.ActualCenteredFamilyPotentialBound405
import KLSConstantImprovement.ActualSourceUniformLocalIntegrals405

/-! Actual source-Hessian cutoff precompactness.  Every local derivative
budget is paid by the genuine weak third tensor and the actual global
curvature mean, using only a common upper Hessian modulus and centering. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualSourceHessianLocalPrecompact405
open KLS ActualBoundedCanonicalSource ActualBoundedRawTestAlgebra405
open ActualLocalBoundedWeakAlgebra405 ActualLocalRawH1Precompact405
open ActualCenteredFamilyPotentialBound405 ActualSourceUniformLocalIntegrals405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {ρ : ℕ → Measure (Space n)}

theorem actual_hessian_cutoff_precompact
    (d : ∀ k, SourceData (ρ k)) (hiso : ∀ k, IsIsotropic (ρ k))
    {c : ℝ} (hc : 0 < c) (hκ : ∀ k, c ≤ (d k).targetConvexityConstant)
    (hgrad0 : ∀ k, gradient (d k).potential 0 = 0)
    {z : ℝ} (hlim0 : Tendsto (fun k => (d k).potential (0 : Space n)) atTop (𝓝 z))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) (a b : Fin n) :
    ∃ hf : ∀ k, MemLp (fun x => χ x*coordinateHessian (d k).potential x a b) 2
        (volume : Measure (Space n)),
      TotallyBounded (range (fun k =>
        (hf k).toLp (fun x => χ x*coordinateHessian (d k).potential x a b))) := by
  let E := tsupport χ
  have hE : IsCompact E := hχc
  letI : IsFiniteMeasure ((volume : Measure (Space n)).restrict E) :=
    isFiniteMeasure_restrict.mpr hE.measure_ne_top
  obtain ⟨P, hP⟩ := actual_centered_family_compact_potential_upper d hc hκ hgrad0 hlim0 hE.isBounded
  let B : ℝ := 16/c
  have hB (k : ℕ) : 16/(d k).targetConvexityConstant ≤ B :=
    div_le_div_of_nonneg_left (by norm_num) hc (hκ k)
  let f : ℕ → LocalRawTest n := fun k =>
    LocalRawTest.ofBoundedRawTest (BoundedRawTest.hessian (d k) a b)
  have hv (k : ℕ) : (∫ x in E, (f k).value x^2) ≤ B^2*volume.real E := by
    have hb (x : Space n) : ‖(f k).value x‖ ≤ B :=
      (coordinateHessian_entry_bound_of_gradient_lipschitz (d k).gradient_lipschitz x a b).trans (hB k)
    have hBn : 0 ≤ B := by dsimp [B]; positivity
    have hp (x : Space n) : (f k).value x^2 ≤ B^2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        (sq_le_sq₀ (norm_nonneg ((f k).value x)) hBn).mpr (hb x)
    calc
      _ ≤ ∫ _x in E, B^2 := integral_mono ((f k).value_local E hE).integrable_sq
        (integrable_const _) hp
      _ = B^2*volume.real E := by
        rw [integral_const, smul_eq_mul]
        simp only [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter]
        ring
  have hd (k : ℕ) (i : Fin n) : (∫ x in E, (f k).derivative i x^2) ≤ Real.exp P*B^2 :=
    (actual_third_entry_local_square_integral (d k) (hiso k) (hB k)
      hE.measurableSet (hP k) i a b).2
  exact cutoff_localRaw_uniform_precompact f hχ hχc hE (subset_refl _)
    (by positivity : 0 ≤ B^2*volume.real E) (by positivity : 0 ≤ Real.exp P*B^2) hv hd

end KLSConstantImprovement.ActualSourceHessianLocalPrecompact405
#print axioms KLSConstantImprovement.ActualSourceHessianLocalPrecompact405.actual_hessian_cutoff_precompact
