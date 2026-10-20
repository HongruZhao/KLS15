import KLSConstantImprovement.ActualSourceBoundedMassCutoffs405
import KLSConstantImprovement.ActualSourceRawHessianEvolution405
import KLS.LocalWeakProduct

/-! Bounded natural mass pays the untruncated compact u_i*u_j tests.
The mass bound is explicit; all actual weak product and test domains are
derived from it before the genuine source Hessian equation is used. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualSourceBoundedMassConnectionTests405
open KLS ActualBoundedCanonicalSource ActualBoundedRawMetricDomain
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceBoundedMassCutoffs405
open ActualSourceHessianEvolution405 ActualSourceRawHessianEvolution405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

private theorem exists_ae_norm_bound_of_memLp_top {ν : Measure (Space n)} {f : Space n → ℝ}
    (hf : MemLp f ∞ ν) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂ν, ‖f x‖ ≤ B := by
  have he : eLpNormEssSup f ν < ⊤ := eLpNormEssSup_le_eLpNorm_top.trans_lt hf.eLpNorm_lt_top
  obtain ⟨B, hB⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp he
  refine ⟨(B : ℝ), B.2, ?_⟩
  filter_upwards [hB] with x hx
  exact_mod_cast hx

def boundedMassQuadraticTest (χ : Space n → ℝ) (u : Fin n → Space n → ℝ)
    (i j : Fin n) (x : Space n) : ℝ := χ x ^ 2 * (u i x * u j x)

def boundedMassQuadraticDerivative (χ : Space n → ℝ) (u : Fin n → Space n → ℝ)
    (Du : Fin n → Fin n → Space n → ℝ) (i j a : Fin n) : Space n → ℝ :=
  rawCutoffDerivative (fun x => χ x ^ 2) (fun x => u i x * u j x)
    (fun b x => Du i b x * u j x + u i x * Du j b x) a

theorem boundedMassQuadraticTest_memLp_top
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    {u : Fin n → Space n → ℝ}
    (hu : ∀ i E, IsCompact E → MemLp (u i) ∞ (volume.restrict E)) (i j : Fin n) :
    MemLp (boundedMassQuadraticTest χ u i j) ∞ (volume : Measure (Space n)) := by
  have hχc : HasCompactSupport (fun x => χ x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using hc.mul_right (f' := χ)
  have hχTop : MemLp (fun x => χ x ^ 2) ∞ (volume : Measure (Space n)) :=
    (hχ.pow 2).continuous.memLp_of_hasCompactSupport hχc
  have hp : MemLp ((tsupport χ).indicator (fun x => u i x * u j x)) ∞ (volume : Measure (Space n)) :=
    (memLp_indicator_iff_restrict hc.measurableSet.nullMeasurableSet).mpr ((hu i _ hc).mul (hu j _ hc))
  have hm : MemLp (fun x => χ x ^ 2 * (tsupport χ).indicator (fun y => u i y * u j y) x) ∞
      (volume : Measure (Space n)) := hχTop.mul hp
  apply (memLp_congr_ae (Eventually.of_forall fun x => ?_)).mp hm
  by_cases hx : x ∈ tsupport χ
  · rw [indicator_of_mem hx]
    rfl
  · simp only [boundedMassQuadraticTest, image_eq_zero_of_notMem_tsupport hx,
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]

theorem actual_boundedMass_compact_quadratic_hessian_evolution (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential, sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (i j : Fin n) :
    (∀ a, Integrable (fun x => ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
      boundedMassQuadraticDerivative χ (naturalCanonicalFlux d g) Du i j a x) (potentialMeasure d.potential)) ∧
      Integrable (fun x => (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
        boundedMassQuadraticTest χ (naturalCanonicalFlux d g) i j x) (potentialMeasure d.potential) ∧
      -(∑ a : Fin n, ∫ x, ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
        boundedMassQuadraticDerivative χ (naturalCanonicalFlux d g) Du i j a x ∂potentialMeasure d.potential) =
        ∫ x, (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
          boundedMassQuadraticTest χ (naturalCanonicalFlux d g) i j x ∂potentialMeasure d.potential := by
  let u := naturalCanonicalFlux d g
  have huTop (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (u i) ∞ (volume.restrict E) :=
    naturalCanonicalFlux_local_top_of_mass_bound d g hC hM i hE
  have hχ2 : ContDiff ℝ 1 (fun x => χ x ^ 2) := hχ.pow 2
  have hc2 : HasCompactSupport (fun x => χ x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using hc.mul_right (f' := χ)
  have hf (E : Set (Space n)) (hE : IsCompact E) : MemLp (fun x => u i x * u j x) 2 (volume.restrict E) :=
    (huTop i E hE).mul (hu j E hE)
  have hF (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => Du i a x * u j x + u i x * Du j a x) 2 (volume.restrict E) :=
    ((hDu i a E hE).mul (huTop j E hE)).add ((huTop i E hE).mul (hDu j a E hE))
  have hprodW (a : Fin n) := (hw i a).mul (hw j a) (hu i) (hu j) (hDu i a) (hDu j a)
  have htestF (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (boundedMassQuadraticDerivative χ u Du i j a) 2 (volume.restrict E) :=
    (memLp_continuous_mul_on_compact hE (hF a E hE) hχ2.continuous).add
      (memLp_continuous_mul_on_compact hE (hf E hE)
        (contDiff_coordinateDerivative hχ2 (m := 0) (by norm_num) a).continuous)
  have htestW (a : Fin n) : HasLocalWeakCoordinateDerivative (boundedMassQuadraticTest χ u i j)
      (boundedMassQuadraticDerivative χ u Du i j a) a := by
    obtain ⟨W, hW, hWe⟩ := (hprodW a).compact_mul hf (hF a) hχ2 hc2
    exact (show HasLocalWeakCoordinateDerivative (boundedMassQuadraticTest χ u i j) (fun x => W x) a from hW).congr_ae
      EventuallyEq.rfl hWe
  obtain ⟨B, _, hB⟩ := exists_ae_norm_bound_of_memLp_top (boundedMassQuadraticTest_memLp_top hχ hc huTop i j)
  exact actual_compact_raw_hessian_evolution d
    (fun E hE => memLp_continuous_mul_on_compact hE (hf E hE) hχ2.continuous)
    hc2.mul_right hB htestF htestW i j

end KLSConstantImprovement.ActualSourceBoundedMassConnectionTests405
#print axioms KLSConstantImprovement.ActualSourceBoundedMassConnectionTests405.boundedMassQuadraticTest_memLp_top
#print axioms KLSConstantImprovement.ActualSourceBoundedMassConnectionTests405.actual_boundedMass_compact_quadratic_hessian_evolution
