import MomentMapTwoSlot
import KLS.WeakMomentTraceSquareBound
import KLS.LocalWeakProduct
import KLS.StrongDensityWeakMomentQuadratic

/-! Genuine cubic integration by parts at the original C1,1 weak moment
regularity, using the old release's raw weak derivative calculus. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Set Filter
open scoped ContDiff BigOperators ENNReal NNReal Matrix.Norms.Elementwise
namespace KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ} {G : ℝ≥0}

theorem memLp_comp_continuous_bounded_gradient [IsFiniteMeasure (potentialMeasure φ)]
    (hgc : Continuous (gradient φ))
    (hb : Bornology.IsBounded (range (gradient φ)))
    {F : Space n → ℝ} (hF : Continuous F) (p : ℝ≥0∞) :
    MemLp (fun x => F (gradient φ x)) p (potentialMeasure φ) := by
  obtain ⟨C, hC⟩ := hb.isCompact_closure.bddAbove_image hF.norm.continuousOn
  apply MemLp.of_bound (hF.comp hgc).aestronglyMeasurable C
  exact .of_forall fun x => hC ⟨gradient φ x, subset_closure ⟨x,rfl⟩,rfl⟩

theorem integral_gradient_cubic_eq_hessian_pairings_C11
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hG : LipschitzWith G (gradient φ))
    (hgrad : Bornology.IsBounded (range (gradient φ))) (i j k : Fin n) :
    (∫ x, gradient φ x i*gradient φ x j*gradient φ x k ∂potentialMeasure φ) =
      (∫ x, coordinateHessian φ x i k*gradient φ x j ∂potentialMeasure φ) +
      ∫ x, coordinateHessian φ x j k*gradient φ x i ∂potentialMeasure φ := by
  have hgi (a : Fin n) : MemLp (coordinateDerivative φ a) 2 (potentialMeasure φ) := by
    rw [show coordinateDerivative φ a = (fun x => gradient φ x a) from
      funext (coordinateDerivative_eq_gradient φ a)]
    exact memLp_comp_continuous_bounded_gradient hG.continuous hgrad
      (by fun_prop : Continuous (fun y : Space n => y a)) 2
  have hhi (a b : Fin n) :=
    memLp_actual_hessian_entry_of_global_gradient_lipschitz (μ := potentialMeasure φ) hG a b 2
  have hloc (a : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (coordinateDerivative φ a) 2 (volume.restrict K) :=
    memLp_continuous_on_compact
      (locallyLipschitz_coordinateDerivative_of_gradient hG.locallyLipschitz a).continuous hK
  have hHloc (a b : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (fun x => coordinateHessian φ x a b) 2 (volume.restrict K) := by
    let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    exact memLp_actual_hessian_entry_of_global_gradient_lipschitz hG a b 2
  have hw := (actual_hessian_hasLocalWeakCoordinateDerivative hG.locallyLipschitz k i).mul
    (actual_hessian_hasLocalWeakCoordinateDerivative hG.locallyLipschitz k j)
    (hloc i) (hloc j) (hHloc k i) (hHloc k j)
  have hf : Integrable (fun x => coordinateDerivative φ i x*coordinateDerivative φ j x)
      (potentialMeasure φ) := by convert (hgi i).integrable_mul (hgi j) using 1
  have hleft : Integrable (fun x => coordinateHessian φ x k i*coordinateDerivative φ j x)
      (potentialMeasure φ) := by convert (hhi k i).integrable_mul (hgi j) using 1
  have hright : Integrable (fun x => coordinateDerivative φ i x*coordinateHessian φ x k j)
      (potentialMeasure φ) := by convert (hgi i).integrable_mul (hhi k j) using 1
  have hfd : Integrable
      (fun x => (coordinateDerivative φ i x*coordinateDerivative φ j x)*coordinateDerivative φ k x)
      (potentialMeasure φ) := by
    simpa only [coordinateDerivative_eq_gradient] using
      (memLp_comp_continuous_bounded_gradient hG.continuous hgrad
        (by fun_prop : Continuous (fun y : Space n => y i*y j*y k)) 1).integrable (by norm_num)
  have hF : Integrable
      (fun x => coordinateHessian φ x k i*coordinateDerivative φ j x+
        coordinateDerivative φ i x*coordinateHessian φ x k j)
      (potentialMeasure φ) := by convert hleft.add hright using 1
  have h := integral_raw_derivative_potential hφ hw hf hF hfd
  rw [integral_add hleft hright] at h
  simp_rw [coordinateDerivative_eq_gradient] at h
  have hs : ∀ᵐ x ∂potentialMeasure φ, (coordinateHessian φ x).IsSymm :=
    (withDensity_absolutelyContinuous volume
      (fun x => ENNReal.ofReal (Real.exp (-φ x)))).ae_le
      (actual_hessian_ae_symmetric_of_locallyLipschitz_gradient hφ.locallyLipschitz hG.locallyLipschitz)
  have hl : (∫ x, coordinateHessian φ x k i*gradient φ x j ∂potentialMeasure φ) =
      ∫ x, coordinateHessian φ x i k*gradient φ x j ∂potentialMeasure φ := by
    apply integral_congr_ae
    filter_upwards [hs] with x hx
    rw [hx.apply i k]
  have hr : (∫ x, gradient φ x i*coordinateHessian φ x k j ∂potentialMeasure φ) =
      ∫ x, coordinateHessian φ x j k*gradient φ x i ∂potentialMeasure φ := by
    apply integral_congr_ae
    filter_upwards [hs] with x hx
    rw [hx.apply j k]
    ring
  rw [hl,hr] at h
  exact h.symm

theorem integral_hessian_mul_gradient_eq_half_cubic_C11
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hG : LipschitzWith G (gradient φ))
    (hgrad : Bornology.IsBounded (range (gradient φ))) (i j k : Fin n) :
    (∫ x, coordinateHessian φ x i j*gradient φ x k ∂potentialMeasure φ) =
      (1/2 : ℝ)*∫ x, gradient φ x i*gradient φ x j*gradient φ x k ∂potentialMeasure φ := by
  have h1 := integral_gradient_cubic_eq_hessian_pairings_C11 hφ hG hgrad i j k
  have h2 := integral_gradient_cubic_eq_hessian_pairings_C11 hφ hG hgrad i k j
  have h3 := integral_gradient_cubic_eq_hessian_pairings_C11 hφ hG hgrad j k i
  have hsym : ∀ᵐ x ∂potentialMeasure φ, (coordinateHessian φ x).IsSymm :=
    (withDensity_absolutelyContinuous volume
      (fun x => ENNReal.ofReal (Real.exp (-φ x)))).ae_le
      (actual_hessian_ae_symmetric_of_locallyLipschitz_gradient hφ.locallyLipschitz hG.locallyLipschitz)
  have hs (a b c : Fin n) :
      (∫ x, coordinateHessian φ x a b*gradient φ x c ∂potentialMeasure φ) =
      ∫ x, coordinateHessian φ x b a*gradient φ x c ∂potentialMeasure φ := by
    apply integral_congr_ae
    filter_upwards [hsym] with x hx
    rw [hx.apply b a]
  rw [hs k j i] at h2
  rw [hs j i k,hs k i j] at h3
  have hc1 : (∫ x, gradient φ x i*gradient φ x k*gradient φ x j ∂potentialMeasure φ) =
      ∫ x, gradient φ x i*gradient φ x j*gradient φ x k ∂potentialMeasure φ := by
    congr 1; funext x; ring
  have hc2 : (∫ x, gradient φ x j*gradient φ x k*gradient φ x i ∂potentialMeasure φ) =
      ∫ x, gradient φ x i*gradient φ x j*gradient φ x k ∂potentialMeasure φ := by
    congr 1; funext x; ring
  rw [hc1] at h2
  rw [hc2] at h3
  linarith

#print axioms integral_gradient_cubic_eq_hessian_pairings_C11
#print axioms integral_hessian_mul_gradient_eq_half_cubic_C11
end KLS.DeterministicBridgeIntegration
