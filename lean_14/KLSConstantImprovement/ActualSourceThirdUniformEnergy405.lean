import KLSConstantImprovement.ActualSourceCurvatureDomains405
import KLSConstantImprovement.ActualCompatibleConnectionBoundary405

/-! The actual connection curvature bounds each genuine weak third entry.
Isotropy pays its global weighted square, uniformly through only the common
upper Hessian modulus. No uniform lower Hessian is used. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology NNReal ContDiff Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceThirdUniformEnergy405
open KLS ActualBoundedCanonicalSource ActualSourceHessianEvolution405
open ActualSourceGlobalCurvature405 ActualSourceCurvatureDomains405
open ActualCompatibleConnectionBoundary405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem symmetric_entry_square_le_inverse_trace
    (H N : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) (hN : N.IsSymm)
    (i j : Fin n) :
    N i j ^ 2 ≤ H i i * H j j * (H⁻¹ * N * H⁻¹ * N).trace := by
  let e (a : Fin n) : Fin n → ℝ := Pi.single a 1
  have hinv : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H
    (isUnit_iff_ne_zero.mpr hH.det_pos.ne')
  have hpair (z : Fin n → ℝ) :
      (H *ᵥ e i) ⬝ᵥ (H⁻¹ *ᵥ z) = z i := by
    rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec H (e i), hH.isHermitian.isSymm.eq,
      Matrix.mulVec_mulVec]
    have hinv' : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H
      (isUnit_iff_ne_zero.mpr hH.det_pos.ne')
    rw [hinv', Matrix.one_mulVec]
    simp [e]
  have h := compatible_connection_boundary_square H N hH hN (H *ᵥ e i) (e j)
  rw [hpair, hpair] at h
  simpa only [e, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply,
    single_one_dotProduct] using h

theorem actual_third_entry_square_bound (d : SourceData μ) {B : ℝ}
    (hB : 16 / d.targetConvexityConstant ≤ B) (k i j : Fin n) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      d.third x k i j ^ 2 ≤ B ^ 2 * sourceConnectionCurvature d x k k := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le] with x hx hN
  let H := coordinateHessian d.potential x
  let N := sourceThirdMatrix d x k
  have hNs : N.IsSymm := Matrix.IsSymm.ext fun a b => (hN k b a).2
  have hh := symmetric_entry_square_le_inverse_trace H N hx.1 hNs i j
  have hgram : 0 ≤ (H⁻¹ * N * H⁻¹ * N).trace :=
    (matrixTraceGram_posSemidef hx.1.posSemidef.inv (sourceThirdMatrix d x)
      (fun a => Matrix.IsSymm.ext fun b c => (hN a c b).2)).diag_nonneg
  have hi : H i i ≤ B :=
    (le_abs_self _).trans ((coordinateHessian_entry_bound_of_gradient_lipschitz
      d.gradient_lipschitz x i i).trans hB)
  have hj : H j j ≤ B :=
    (le_abs_self _).trans ((coordinateHessian_entry_bound_of_gradient_lipschitz
      d.gradient_lipschitz x j j).trans hB)
  have hBn : 0 ≤ B := (hx.1.posSemidef.diag_nonneg : 0 ≤ H i i).trans hi
  have hprod : H i i * H j j ≤ B ^ 2 := by
    simpa only [pow_two] using mul_le_mul hi hj hx.1.posSemidef.diag_nonneg hBn
  have htarget : 0 ≤ (H * coordinateHessian d.targetPotential (gradient d.potential x) * H) k k := by
    have h := (coordinateHessian_posSemidef_of_convex
      (d.target_smooth.of_le (by simp)) d.target_convex_potential (gradient d.potential x)).conjTranspose_mul_mul_same H
    have hHs : Hᴴ = H := hx.1.isHermitian.eq
    simpa only [hHs] using h.diag_nonneg (i := k)
  have hle : (H⁻¹ * N * H⁻¹ * N).trace ≤ sourceConnectionCurvature d x k k := by
    change _ ≤ (H * coordinateHessian d.targetPotential (gradient d.potential x) * H) k k +
      (H⁻¹ * N * H⁻¹ * N).trace
    linarith
  exact hh.trans ((mul_le_mul_of_nonneg_right hprod hgram).trans
    (mul_le_mul_of_nonneg_left hle (sq_nonneg B)))

theorem actual_third_entry_global_square_integral (d : SourceData μ)
    (hiso : IsIsotropic μ) {B : ℝ}
    (hB : 16 / d.targetConvexityConstant ≤ B) (k i j : Fin n) :
    Integrable (fun x => d.third x k i j ^ 2) (potentialMeasure d.potential) ∧
      (∫ x, d.third x k i j ^ 2 ∂potentialMeasure d.potential) ≤ B ^ 2 := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  have hm : AEStronglyMeasurable (fun x => d.third x k i j ^ 2)
      (potentialMeasure d.potential) :=
    ((locallyIntegrable_of_memLp_two_on_compacts
      (d.third_local_L2 k i j)).aestronglyMeasurable.mono_ac hac).pow 2
  have hb := actual_third_entry_square_bound d hB k i j
  have hcurv := actual_connection_curvature_diagonal_integrable d k
  have hi : Integrable (fun x => d.third x k i j ^ 2) (potentialMeasure d.potential) :=
    (hcurv.1.const_mul (B ^ 2)).mono' hm (hb.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (d.third x k i j))]
      exact hx)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, B ^ 2 * sourceConnectionCurvature d x k k ∂potentialMeasure d.potential :=
      integral_mono_ae hi (hcurv.1.const_mul _) hb
    _ = B ^ 2 := by
      rw [integral_const_mul, hcurv.2,
        integral_actual_hessian_entry_eq_one_C11 d.source_C1 d.gradient_lipschitz
          (d.pushforward.symm ▸ hiso) k k]
      simp

end KLSConstantImprovement.ActualSourceThirdUniformEnergy405
#print axioms KLSConstantImprovement.ActualSourceThirdUniformEnergy405.symmetric_entry_square_le_inverse_trace
#print axioms KLSConstantImprovement.ActualSourceThirdUniformEnergy405.actual_third_entry_square_bound
#print axioms KLSConstantImprovement.ActualSourceThirdUniformEnergy405.actual_third_entry_global_square_integral
