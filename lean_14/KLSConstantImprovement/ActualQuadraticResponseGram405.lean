import KLSConstantImprovement.ActualQuadraticResponseField405
import KLSConstantImprovement.ActualResponseGramBound405

/-! Boundedness and local domains of the actual response Gram, conditional
only on explicitly displayed quadratic-eta mass bounds. This does not
assert that those mass bounds have been discharged. -/
noncomputable section
open Matrix MeasureTheory Filter Set
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualQuadraticResponseGram405
open KLS ActualBoundedCanonicalSource ActualQuadraticResponseField405 ActualResponseGramBound405
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualAffineMatrixTests405 ActualBoundedRawTestAlgebra405 ActualSourceBoundedMassCutoffs405
variable {n : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem quadraticResponseMatrix_aestronglyMeasurable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i a : Fin n) :
    AEStronglyMeasurable (fun x => quadraticResponseMatrix d T x i a) (potentialMeasure d.potential) := by
  have hgrad := d.gradient_lipschitz.continuous
  have hZ : Continuous (fun x => actualAffineMatrix d T x i a) := by
    simp only [actualAffineMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  exact ((naturalCanonicalFlux_aestronglyMeasurable d (quadraticSourceDatum d (T i)) a).const_mul 2).sub
    hZ.aestronglyMeasurable

theorem quadraticResponseGram_aestronglyMeasurable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    AEStronglyMeasurable (fun x => quadraticResponseGram d T x i j) (potentialMeasure d.potential) := by
  simp only [quadraticResponseGram, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.univ.aestronglyMeasurable_fun_sum fun b _ =>
    Finset.univ.aestronglyMeasurable_fun_sum fun a _ =>
      ((quadraticResponseMatrix_aestronglyMeasurable d T i a).mul
        (d.hessian_entry_memLp a b 2).aestronglyMeasurable).mul
          (quadraticResponseMatrix_aestronglyMeasurable d T j b)

theorem quadraticResponseGram_posSemidef_ae (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential, (quadraticResponseGram d T x).PosSemidef := by
  filter_upwards [d.hessian_ae_source] with x hx
  exact row_metric_gram_posSemidef _ _ hx.1.posSemidef

theorem actual_quadratic_response_gram_bounded_of_mass_bound (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i j, ∀ᵐ x ∂potentialMeasure d.potential, ‖quadraticResponseGram d T x i j‖ ≤ B := by
  choose B hB using fun i : Fin n => (affineHessianTest d T i i).bounded
  have hB0 (i : Fin n) : 0 ≤ B i := (norm_nonneg ((affineHessianTest d T i i).value 0)).trans (hB i 0)
  have hBsum : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ => hB0 i
  let D : ℝ := 8 * C + 2 * ∑ i, B i
  refine ⟨2 * D, by dsimp only [D]; positivity, ?_⟩
  intro i j
  filter_upwards [d.hessian_ae_source, ae_all_iff.mpr hM] with x hx hm
  have hz (a : Fin n) : metricRowMass (coordinateHessian d.potential x) (actualAffineMatrix d T x a) ≤
      ∑ k, B k := by
    have he : metricRowMass (coordinateHessian d.potential x) (actualAffineMatrix d T x a) =
        (affineHessianTest d T a a).value x := by
      rw [affineHessianTest_value]
      have hg := row_metric_gram_diagonal (coordinateHessian d.potential x) (actualAffineMatrix d T x) a
      rw [(actualAffineMatrix_symmetric d T hT x).eq] at hg
      exact hg.symm
    rw [he]
    have hb := hB a x
    rw [Real.norm_eq_abs] at hb
    exact ((le_abs_self _).trans hb).trans
      (Finset.single_le_sum (fun k _ => hB0 k) (Finset.mem_univ a))
  have hu (a : Fin n) : metricRowMass (coordinateHessian d.potential x)
      (fun b => quadraticRowFlux d T a b x) ≤ C := by
    have he := (matrix_quadratic_sum_eq_dotProduct (coordinateHessian d.potential x)
      (fun b => quadraticRowFlux d T a b x)).symm
    exact he.le.trans (hm a)
  have hdiag (a : Fin n) : metricRowMass (coordinateHessian d.potential x)
      (quadraticResponseMatrix d T x a) ≤ D := by
    have he := metric_row_mass_two_sub (coordinateHessian d.potential x) hx.1.posSemidef
      (fun b => quadraticRowFlux d T a b x) (actualAffineMatrix d T x a)
    change metricRowMass (coordinateHessian d.potential x)
      (fun b => 2 * quadraticRowFlux d T a b x - actualAffineMatrix d T x a b) ≤ D
    dsimp only [D]
    linarith [hu a, hz a]
  exact row_metric_gram_entry_bound _ _ hx.1.posSemidef D hdiag i j

theorem actual_quadratic_response_gram_memLp_top_of_mass_bound (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i j : Fin n) :
    MemLp (fun x => quadraticResponseGram d T x i j) ∞ (potentialMeasure d.potential) := by
  obtain ⟨B, _, hB⟩ := actual_quadratic_response_gram_bounded_of_mass_bound d T hT hC hM
  exact memLp_top_of_bound (quadraticResponseGram_aestronglyMeasurable d T i j) B (hB i j)

theorem actual_quadratic_response_local_top_of_mass_bound (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i a : Fin n) {E : Set (Space n)} (hE : IsCompact E) :
    MemLp (fun x => quadraticResponseMatrix d T x i a) ∞ (volume.restrict E) := by
  have hu := naturalCanonicalFlux_local_top_of_mass_bound d (quadraticSourceDatum d (T i)) hC (hM i) a hE
  have hz : MemLp (fun x => actualAffineMatrix d T x i a) ∞ (volume.restrict E) :=
    (memLp_congr_ae (Eventually.of_forall (affineSliceTest_value d T i a))).mp
      ((affineSliceTest d T i a).value_local_top E hE)
  exact (hu.const_mul 2).sub hz

end KLSConstantImprovement.ActualQuadraticResponseGram405

#print axioms KLSConstantImprovement.ActualQuadraticResponseGram405.quadraticResponseGram_posSemidef_ae
#print axioms KLSConstantImprovement.ActualQuadraticResponseGram405.actual_quadratic_response_gram_memLp_top_of_mass_bound
#print axioms KLSConstantImprovement.ActualQuadraticResponseGram405.actual_quadratic_response_local_top_of_mass_bound
