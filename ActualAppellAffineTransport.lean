import ActualAppellFiniteMoments
import KLS.AffineWhitening
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Genuine normalized Laplace expectations and every actual Appell tensor
transport through continuous affine equivalences, without compact support. -/
noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem inner_affineEquiv_transport {n : ℕ} (e : Space n ≃ᴬ[ℝ] Space n)
    (z x : Space n) :
    inner ℝ z (e x) =
      inner ℝ (e.toContinuousAffineMap.contLinear.adjoint z) x+inner ℝ z (e 0) := by
  have he : e x = e.toContinuousAffineMap.contLinear x+e 0 := by
    change e.toContinuousAffineMap x = e.toContinuousAffineMap.contLinear x+e.toContinuousAffineMap 0
    simpa only [zero_add,vadd_eq_add,add_zero] using e.toContinuousAffineMap.map_vadd 0 x
  rw [he,inner_add_right,ContinuousLinearMap.adjoint_inner_left]

 theorem actual_tilt_average_affine_transport {n : ℕ} (μ : Measure (Space n))
    (e : Space n ≃ᴬ[ℝ] Space n) (f : Space n → ℝ) (z : Space n) :
    (∫ y, f (e.symm y) ∂exponentialTilt (μ.map e) z) =
      ∫ x, f x ∂exponentialTilt μ (e.toContinuousAffineMap.contLinear.adjoint z) := by
  change tiltAverage (μ.map e) (fun y => inner ℝ z y) (fun y => f (e.symm y)) =
    tiltAverage μ (fun x => inner ℝ (e.toContinuousAffineMap.contLinear.adjoint z) x) f
  rw [tiltAverage_eq_ratio,tiltAverage_eq_ratio]
  unfold tiltPartition
  have hN : (∫ y, f (e.symm y)*Real.exp (inner ℝ z y) ∂μ.map e) =
      Real.exp (inner ℝ z (e 0))*(∫ x, f x*
        Real.exp (inner ℝ (e.toContinuousAffineMap.contLinear.adjoint z) x) ∂μ) := by
    change (∫ y, f (e.symm y)*Real.exp (inner ℝ z y) ∂μ.map e.toHomeomorph) = _
    rw [e.toHomeomorph.isClosedEmbedding.integral_map]
    change (∫ x, f (e.symm (e x))*Real.exp (inner ℝ z (e x)) ∂μ) = _
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [e.symm_apply_apply,inner_affineEquiv_transport e z x,Real.exp_add]
      ring
  have hZ : (∫ y, Real.exp (inner ℝ z y) ∂μ.map e) =
      Real.exp (inner ℝ z (e 0))*(∫ x,
        Real.exp (inner ℝ (e.toContinuousAffineMap.contLinear.adjoint z) x) ∂μ) := by
    change (∫ y, Real.exp (inner ℝ z y) ∂μ.map e.toHomeomorph) = _
    rw [e.toHomeomorph.isClosedEmbedding.integral_map]
    change (∫ x, Real.exp (inner ℝ z (e x)) ∂μ) = _
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [inner_affineEquiv_transport e z x,Real.exp_add]
      ring
  rw [hN,hZ,mul_div_mul_left _ _ (Real.exp_ne_zero _)]

 theorem actual_affine_L2_energy_transport {n : ℕ} (μ : Measure (Space n))
    (e : Space n ≃ᴬ[ℝ] Space n) (f : Space n → ℝ) :
    (∫ y, (f (e.symm y))^2 ∂μ.map e) = ∫ x, (f x)^2 ∂μ := by
  change (∫ y, (f (e.symm y))^2 ∂μ.map e.toHomeomorph) = _
  rw [e.toHomeomorph.isClosedEmbedding.integral_map]
  change (∫ x, (f (e.symm (e x)))^2 ∂μ) = _
  simp only [e.symm_apply_apply]

 theorem iteratedFDeriv_comp_linear_zero {n d : ℕ} {f : Space n → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f 0) (L : Space n →L[ℝ] Space n)
    (v : Fin d → Space n) :
    iteratedFDeriv ℝ d (f ∘ L) 0 v = iteratedFDeriv ℝ d f 0 (fun i => L (v i)) := by
  obtain ⟨u,hu,h0,hfu⟩ := hf.contDiffOn' (m := (d : ℕ∞)) (by simp) (by simp)
  simp only [insert_eq_of_mem (mem_univ _),univ_inter] at hfu
  have hpre := hu.preimage L.continuous
  have h0pre : (0 : Space n) ∈ L ⁻¹' u := by simpa only [mem_preimage,map_zero] using h0
  have h := L.iteratedFDerivWithin_comp_right (x := (0 : Space n)) (i := d) hfu
    (hu.uniqueDiffOn (𝕜 := ℝ)) (hpre.uniqueDiffOn (𝕜 := ℝ))
    (by simpa only [map_zero] using h0) le_rfl
  rw [iteratedFDerivWithin_of_isOpen d hpre h0pre,
    iteratedFDerivWithin_of_isOpen d hu (by simpa only [map_zero] using h0),map_zero] at h
  have hv := congrArg (fun T => T v) h
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply] using hv

/-- Literal mixed Appell derivatives transform by the adjoint linear part of
an actual common affine change of law and test function. -/
 theorem actualAppell_mixed_affine_transport {n d : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (e : Space n ≃ᴬ[ℝ] Space n) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (v : Fin d → Space n) :
    iteratedFDeriv ℝ d (fun z =>
      ∫ y, f (e.symm y) ∂exponentialTilt (μ.map e) z) 0 v =
      iteratedFDeriv ℝ d (fun z => ∫ x, f x ∂exponentialTilt μ z) 0
        (fun i => e.toContinuousAffineMap.contLinear.adjoint (v i)) := by
  have he : (fun z => ∫ y, f (e.symm y) ∂exponentialTilt (μ.map e) z) =
      (fun z => ∫ x, f x ∂exponentialTilt μ z) ∘
        e.toContinuousAffineMap.contLinear.adjoint := by
    funext z
    exact actual_tilt_average_affine_transport μ e f z
  rw [he]
  exact iteratedFDeriv_comp_linear_zero (contDiffAt_normalized_tilt_average hLC hf) _ v

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_tilt_average_affine_transport
#print axioms KLS.DeterministicBridgeNext.actualAppell_mixed_affine_transport
