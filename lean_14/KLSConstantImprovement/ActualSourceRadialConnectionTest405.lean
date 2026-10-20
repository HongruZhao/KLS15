import KLSConstantImprovement.ActualRadialWeakMatrixTests405
import KLSConstantImprovement.ActualSourceRawHessianEvolution405
import KLSConstantImprovement.ActualBoundedRawMetricDomain

/-! Legitimate compact common-radial tests for the actual weak Hessian
equation. Every weak derivative, local L2 domain, compact support and value
bound is proved before testing. No global metric domain is inferred. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualSourceRadialConnectionTest405
open KLS ActualBoundedCanonicalSource ActualBoundedRawMetricDomain
open ActualRadialMatrixCalculus405 ActualRadialWeakMatrixTests405
open ActualSourceHessianEvolution405 ActualSourceRawHessianEvolution405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def compactRadialMatrixTest (χ : Space n → ℝ) (δ : ℝ)
    (u : Fin n → Space n → ℝ) (i j : Fin n) (x : Space n) : ℝ :=
  χ x ^ 2 * radialMatrixEntry δ i j (fun k => u k x)

def compactRadialMatrixDerivative (χ : Space n → ℝ) (δ : ℝ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    (i j a : Fin n) : Space n → ℝ :=
  rawCutoffDerivative (fun x => χ x ^ 2)
    (fun x => radialMatrixEntry δ i j (fun k => u k x))
    (fun b => radialRawDerivative δ i j u (fun k => Du k b)) a

theorem compactRadialMatrixTest_domains {δ : ℝ} (hδ : 0 < δ)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    {u : Fin n → Space n → ℝ} {Du : Fin n → Fin n → Space n → ℝ}
    (hu : ∀ k E, IsCompact E → MemLp (u k) 2 (volume.restrict E))
    (hDu : ∀ k a E, IsCompact E → MemLp (Du k a) 2 (volume.restrict E))
    (hw : ∀ k a, HasLocalWeakCoordinateDerivative (u k) (Du k a) a) (i j : Fin n) :
    (∀ E, IsCompact E → MemLp (compactRadialMatrixTest χ δ u i j) 2 (volume.restrict E)) ∧
      HasCompactSupport (compactRadialMatrixTest χ δ u i j) ∧
      (∀ a E, IsCompact E → MemLp (compactRadialMatrixDerivative χ δ u Du i j a) 2 (volume.restrict E)) ∧
      ∀ a, HasLocalWeakCoordinateDerivative (compactRadialMatrixTest χ δ u i j)
        (compactRadialMatrixDerivative χ δ u Du i j a) a := by
  have hχ2 : ContDiff ℝ 1 (fun x => χ x ^ 2) := hχ.pow 2
  have hc2 : HasCompactSupport (fun x => χ x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using hc.mul_right (f' := χ)
  have hf (E : Set (Space n)) (hE : IsCompact E) := radial_matrix_value_local_L2 hδ i j hu E hE
  have hF (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :=
    radial_matrix_derivative_local_L2 hδ i j hu (fun k => hDu k a) E hE
  refine ⟨fun E hE => memLp_continuous_mul_on_compact hE (hf E hE) hχ2.continuous, hc2.mul_right, ?_, ?_⟩
  · intro a E hE
    exact (memLp_continuous_mul_on_compact hE (hF a E hE) hχ2.continuous).add
      (memLp_continuous_mul_on_compact hE (hf E hE)
        (contDiff_coordinateDerivative hχ2 (m := 0) (by norm_num) a).continuous)
  · intro a
    have hrad := radial_matrix_weak_derivative hδ i j hu (fun k => hDu k a) (fun k => hw k a)
    obtain ⟨W, hW, hWe⟩ := hrad.compact_mul hf (hF a) hχ2 hc2
    apply (show HasLocalWeakCoordinateDerivative (compactRadialMatrixTest χ δ u i j)
      (fun x => W x) a from hW).congr_ae EventuallyEq.rfl
    exact hWe

theorem compactRadialMatrixTest_bound {δ : ℝ} (hδ : 0 < δ)
    {χ : Space n → ℝ} (hχ : ∀ x, ‖χ x‖ ≤ 1)
    (u : Fin n → Space n → ℝ) (i j : Fin n) (x : Space n) :
    ‖compactRadialMatrixTest χ δ u i j x‖ ≤ δ⁻¹ := by
  have hc : ‖χ x‖ ^ 2 ≤ 1 := by nlinarith [hχ x, norm_nonneg (χ x)]
  have hr : ‖radialMatrixEntry δ i j (fun k => u k x)‖ ≤ δ⁻¹ := by
    simpa only [Real.norm_eq_abs] using radialMatrixEntry_bound hδ i j (fun k => u k x)
  change ‖χ x ^ 2 * radialMatrixEntry δ i j (fun k => u k x)‖ ≤ δ⁻¹
  rw [norm_mul, norm_pow]
  exact (mul_le_mul hc hr (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans (by simp)

theorem actual_compact_radial_hessian_evolution (d : SourceData μ)
    {δ : ℝ} (hδ : 0 < δ) {χ : Space n → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (hb : ∀ x, ‖χ x‖ ≤ 1)
    {u : Fin n → Space n → ℝ} {Du : Fin n → Fin n → Space n → ℝ}
    (hu : ∀ k E, IsCompact E → MemLp (u k) 2 (volume.restrict E))
    (hDu : ∀ k a E, IsCompact E → MemLp (Du k a) 2 (volume.restrict E))
    (hw : ∀ k a, HasLocalWeakCoordinateDerivative (u k) (Du k a) a) (i j : Fin n) :
    (∀ a, Integrable (fun x => ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
      compactRadialMatrixDerivative χ δ u Du i j a x) (potentialMeasure d.potential)) ∧
      Integrable (fun x => (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
        compactRadialMatrixTest χ δ u i j x) (potentialMeasure d.potential) ∧
      -(∑ a : Fin n, ∫ x, ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
        compactRadialMatrixDerivative χ δ u Du i j a x ∂potentialMeasure d.potential) =
        ∫ x, (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
          compactRadialMatrixTest χ δ u i j x ∂potentialMeasure d.potential := by
  obtain ⟨hf, hfc, hF, hW⟩ := compactRadialMatrixTest_domains hδ hχ hc hu hDu hw i j
  exact actual_compact_raw_hessian_evolution d hf hfc
    (Eventually.of_forall (compactRadialMatrixTest_bound hδ hb u i j)) hF hW i j

end KLSConstantImprovement.ActualSourceRadialConnectionTest405
#print axioms KLSConstantImprovement.ActualSourceRadialConnectionTest405.compactRadialMatrixTest_domains
#print axioms KLSConstantImprovement.ActualSourceRadialConnectionTest405.compactRadialMatrixTest_bound
#print axioms KLSConstantImprovement.ActualSourceRadialConnectionTest405.actual_compact_radial_hessian_evolution
