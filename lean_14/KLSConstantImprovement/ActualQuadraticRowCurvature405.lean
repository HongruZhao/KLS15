import KLSConstantImprovement.ActualAffineResponseHilbert405
import KLSConstantImprovement.ActualQuadraticResponseGram405
import KLSConstantImprovement.ActualAffineTraceDiscount405

/-! The actual row curvature costs for U, Z and F=2U-Z, with global
domains and the PSD parallelogram bound. Quadratic inverse mass is
explicit; no Gram form-domain or production identity is presumed. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualQuadraticRowCurvature405
open KLS ActualBoundedCanonicalSource ActualSourceHessianEvolution405 ActualSourceCurvatureDomains405
open ActualSourceLocalizedGaffney405 ActualSourceNaturalGaffney405 ActualSourceQuadraticEta405
open ActualQuadraticHilbertMatrix405 ActualQuadraticResponseField405 ActualQuadraticResponseGram405
open ActualResponseGramBound405 ActualAffineMatrixTests405 ActualAffineSourceIdentities405
open ActualAffineTraceDiscount405 ActualAffineResponseHilbert405 ActualSourceDirectCubicBalance405
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def actualQuadraticGram (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  actualQuadraticFluxMatrix d T x * coordinateHessian d.potential x * (actualQuadraticFluxMatrix d T x).transpose

def actualRowCurvature (d : SourceData μ) (A : Space n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  ((A x * coordinateHessian d.potential x * (A x).transpose) * sourceConnectionCurvature d x).trace

theorem actualQuadraticGram_measurable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    AEStronglyMeasurable (fun x => actualQuadraticGram d T x i j) (potentialMeasure d.potential) := by
  simp only [actualQuadraticGram, actualQuadraticFluxMatrix, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
  exact Finset.univ.aestronglyMeasurable_fun_sum fun b _ =>
    Finset.univ.aestronglyMeasurable_fun_sum fun a _ =>
      ((naturalCanonicalFlux_aestronglyMeasurable d (quadraticSourceDatum d (T i)) a).mul
        (d.hessian_entry_memLp a b 2).aestronglyMeasurable).mul
          (naturalCanonicalFlux_aestronglyMeasurable d (quadraticSourceDatum d (T j)) b)

theorem actualQuadraticGram_top_of_mass_bound (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) {C : ℝ}
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i j : Fin n) : MemLp (fun x => actualQuadraticGram d T x i j) ∞ (potentialMeasure d.potential) := by
  apply memLp_top_of_bound (actualQuadraticGram_measurable d T i j) (2 * C)
  filter_upwards [d.hessian_ae_source, ae_all_iff.mpr hM] with x hx hm
  apply row_metric_gram_entry_bound _ _ hx.1.posSemidef C ?_ i j
  intro a
  have he := (matrix_quadratic_sum_eq_dotProduct (coordinateHessian d.potential x)
    (actualQuadraticFluxMatrix d T x a)).symm
  exact he.le.trans (hm a)

theorem curvature_pair_integrable_of_top (d : SourceData μ)
    (A : Space n → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, MemLp (fun x => A x i j) ∞ (potentialMeasure d.potential)) :
    Integrable (fun x => (A x * sourceConnectionCurvature d x).trace) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  change Integrable (fun x => ∑ i, ∑ j, A x i j * sourceConnectionCurvature d x j i)
    (potentialMeasure d.potential)
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  have hm : MemLp (fun x => A x i j * sourceConnectionCurvature d x j i) 1
      (potentialMeasure d.potential) := (hA i j).mul
        (memLp_one_iff_integrable.mpr (actual_connection_curvature_entry_integrable d j i))
  exact hm.integrable le_rfl

theorem actual_quadratic_row_curvature_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) {C : ℝ}
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    Integrable (actualRowCurvature d (actualQuadraticFluxMatrix d T)) (potentialMeasure d.potential) :=
  curvature_pair_integrable_of_top d (actualQuadraticGram d T) (actualQuadraticGram_top_of_mass_bound d T hM)

theorem actual_response_row_curvature_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    Integrable (actualRowCurvature d (quadraticResponseMatrix d T)) (potentialMeasure d.potential) :=
  curvature_pair_integrable_of_top d (quadraticResponseGram d T)
    (actual_quadratic_response_gram_memLp_top_of_mass_bound d T hT hC hM)

theorem actual_affine_row_curvature_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    Integrable (actualRowCurvature d (actualAffineMatrix d T)) (potentialMeasure d.potential) := by
  have hz (i j : Fin n) : MemLp (fun x =>
      (actualAffineMatrix d T x * coordinateHessian d.potential x * (actualAffineMatrix d T x).transpose) i j)
        ∞ (potentialMeasure d.potential) := by
    apply (memLp_congr_ae ?_).mp (affineHessianTest d T i j).value_top
    exact Eventually.of_forall fun x => by
      change (affineHessianTest d T i j).value x =
        (actualAffineMatrix d T x * coordinateHessian d.potential x * (actualAffineMatrix d T x).transpose) i j
      rw [affineHessianTest_value, (actualAffineMatrix_symmetric d T hT x).eq]
  exact curvature_pair_integrable_of_top d _ hz

theorem actual_row_curvature_nonnegative (d : SourceData μ) (A : Space n → Matrix (Fin n) (Fin n) ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ actualRowCurvature d A x := by
  filter_upwards [d.hessian_ae_source, actual_source_connection_curvature_positive d] with x hx hK
  exact trace_mul_nonneg_of_posSemidef (row_metric_gram_posSemidef _ _ hx.1.posSemidef) hK

theorem row_curvature_parallelogram (H K U Z : Matrix (Fin n) (Fin n) ℝ) :
    (((2 : ℝ) • U - Z) * H * ((2 : ℝ) • U - Z).transpose * K).trace +
      (Z * H * Z.transpose * K).trace =
        2 * (U * H * U.transpose * K).trace + 2 * ((U - Z) * H * (U - Z).transpose * K).trace := by
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  ring

theorem actual_quadratic_row_curvature_split (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    2 * (∫ x, actualRowCurvature d (actualQuadraticFluxMatrix d T) x ∂potentialMeasure d.potential) ≤
      (∫ x, actualRowCurvature d (quadraticResponseMatrix d T) x ∂potentialMeasure d.potential) +
        ∫ x, actualRowCurvature d (actualAffineMatrix d T) x ∂potentialMeasure d.potential := by
  have hiu := actual_quadratic_row_curvature_integrable d T hM
  have hif := actual_response_row_curvature_integrable d T hT hC hM
  have hiz := actual_affine_row_curvature_integrable d T hT
  have hp : ∀ᵐ x ∂potentialMeasure d.potential,
      2 * actualRowCurvature d (actualQuadraticFluxMatrix d T) x ≤
        actualRowCurvature d (quadraticResponseMatrix d T) x + actualRowCurvature d (actualAffineMatrix d T) x := by
    filter_upwards [actual_row_curvature_nonnegative d (fun x => actualQuadraticFluxMatrix d T x - actualAffineMatrix d T x)] with x hx
    have hf : quadraticResponseMatrix d T x =
        (2 : ℝ) • actualQuadraticFluxMatrix d T x - actualAffineMatrix d T x := by ext i j; rfl
    have he := row_curvature_parallelogram (coordinateHessian d.potential x) (sourceConnectionCurvature d x)
      (actualQuadraticFluxMatrix d T x) (actualAffineMatrix d T x)
    change 0 ≤ ((actualQuadraticFluxMatrix d T x - actualAffineMatrix d T x) * coordinateHessian d.potential x *
      (actualQuadraticFluxMatrix d T x - actualAffineMatrix d T x).transpose * sourceConnectionCurvature d x).trace at hx
    unfold actualRowCurvature
    rw [hf]
    linarith only [he, hx]
  have hb := integral_mono_ae (hiu.const_mul 2) (hif.add hiz) hp
  simp only [Pi.add_apply] at hb
  rwa [integral_const_mul, integral_add hif hiz] at hb

theorem actual_affine_row_curvature_identity (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    (∫ x, actualRowCurvature d (actualAffineMatrix d T) x ∂potentialMeasure d.potential) =
      ((∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) + 3 * actualAffineDiscount d T -
        2 * ∫ x, actualAffineTarget d T x ∂potentialMeasure d.potential) / 2 := by
  have he : (∫ x, actualRowCurvature d (actualAffineMatrix d T) x ∂potentialMeasure d.potential) =
      (∫ x, actualAffineTarget d T x ∂potentialMeasure d.potential) +
        ∫ x, actualAffineGamma d T x ∂potentialMeasure d.potential := by
    calc
      _ = ∫ x, actualAffineTarget d T x + actualAffineGamma d T x ∂potentialMeasure d.potential := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          rw [actualRowCurvature, (actualAffineMatrix_symmetric d T hT x).eq, actual_affine_curvature_split]
      _ = _ := integral_add (actual_affine_target_integrable d T) (actual_affine_gamma_integrable d T)
  have hw := actual_affine_connection_identity d T hT
  unfold actualAffineDiscount
  linarith only [he, hw]

end KLSConstantImprovement.ActualQuadraticRowCurvature405
#print axioms KLSConstantImprovement.ActualQuadraticRowCurvature405.actualQuadraticGram_top_of_mass_bound
#print axioms KLSConstantImprovement.ActualQuadraticRowCurvature405.actual_quadratic_row_curvature_split
#print axioms KLSConstantImprovement.ActualQuadraticRowCurvature405.actual_affine_row_curvature_identity
