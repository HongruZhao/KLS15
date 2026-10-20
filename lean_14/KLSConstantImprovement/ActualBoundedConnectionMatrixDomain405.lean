import KLSConstantImprovement.ActualWhitenedWeakMatrixDomain405
import KLSConstantImprovement.ActualAffineMatrixTests405

/-! Bounded actual vector coefficients contract the genuine source third
tensor to a globally L2 whitened matrix. The curvature entries' L1
domains were proved from the actual H equation, not supplied here. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualBoundedConnectionMatrixDomain405
open KLS ActualBoundedCanonicalSource ActualSourceHessianEvolution405 ActualSourceCurvatureDomains405
open ActualSourceConnectionFields405 ActualSourceConnectionPointwise405 ActualWhitenedWeakMatrixDomain405
open ActualAffineMatrixTests405 ActualBoundedRawTestAlgebra405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem bounded_sourceThirdAlong_local_L2 (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (hu : ∀ a, MemLp (u a) ∞ (potentialMeasure d.potential))
    (i j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (fun x => sourceThirdAlong d u x i j) 2 (volume.restrict E) := by
  have hm : MemLp (fun x => ∑ a : Fin n, u a x * d.third x a i j) 2 (volume.restrict E) :=
    memLp_finsetSum Finset.univ fun a _ =>
      (KLS.MemLp.restrict_volume_of_potentialMeasure (hu a) d.source_C1.continuous hE).mul
        (d.third_local_L2 a i j E hE)
  simpa only [sourceThirdAlong, sourceThirdMatrix, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul] using hm

theorem bounded_sourceGamma_integrable (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (hu : ∀ a, MemLp (u a) ∞ (potentialMeasure d.potential)) :
    Integrable (sourceConnectionGamma d u) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  have hprod : MemLp (fun x => u i x * u j x) ∞ (potentialMeasure d.potential) :=
    (hu i).mul (hu j)
  have hm : MemLp (fun x => (u i x * u j x) *
      matrixTraceGram (coordinateHessian d.potential x)⁻¹ (sourceThirdMatrix d x) i j)
      1 (potentialMeasure d.potential) :=
    hprod.mul (memLp_one_iff_integrable.mpr (actual_third_gram_entry_integrable d i j))
  exact (hm.integrable le_rfl).congr (Eventually.of_forall fun x => by ring)

theorem bounded_sourceTarget_integrable (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (hu : ∀ a, MemLp (u a) ∞ (potentialMeasure d.potential)) :
    Integrable (sourceConnectionTarget d u) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  have hprod : MemLp (fun x => sourceTargetCurvature d x i j * u i x) ∞
      (potentialMeasure d.potential) :=
    (actual_target_curvature_entry_memLp_top d i j).mul (hu i)
  have hm : MemLp (fun x => sourceTargetCurvature d x i j * u i x * u j x) ∞
      (potentialMeasure d.potential) := hprod.mul (hu j)
  exact hm.integrable (by simp)

theorem bounded_sourceThirdAlong_white_memLp (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (hu : ∀ a, MemLp (u a) ∞ (potentialMeasure d.potential)) (i j : Fin n) :
    MemLp (fun x => sourceWhitenedMatrix d (sourceThirdAlong d u) x i j) 2
      (potentialMeasure d.potential) := by
  have hE : Integrable (fun x => ((coordinateHessian d.potential x)⁻¹ * sourceThirdAlong d u x *
      (coordinateHessian d.potential x)⁻¹ * sourceThirdAlong d u x).trace) (potentialMeasure d.potential) := by
    have he := funext (sourceThirdAlong_trace_square d u)
    rw [he]
    exact bounded_sourceGamma_integrable d u hu
  exact sourceWhitenedMatrix_entry_memLp d (sourceThirdAlong d u)
    (bounded_sourceThirdAlong_local_L2 d u hu) (sourceThirdAlong_isSymm_ae d u) hE i j

theorem actual_affine_row_memLp_top (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i a : Fin n) :
    MemLp (fun x => actualAffineMatrix d T x i a) ∞ (potentialMeasure d.potential) :=
  (memLp_congr_ae (Eventually.of_forall (affineSliceTest_value d T i a))).mp
    ((affineSliceTest d T i a).value_top)

theorem actual_affine_third_white_memLp (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i a b : Fin n) :
    MemLp (fun x => sourceWhitenedMatrix d
      (sourceThirdAlong d (fun r y => actualAffineMatrix d T y i r)) x a b)
      2 (potentialMeasure d.potential) :=
  bounded_sourceThirdAlong_white_memLp d _ (actual_affine_row_memLp_top d T i) a b

end KLSConstantImprovement.ActualBoundedConnectionMatrixDomain405

#print axioms KLSConstantImprovement.ActualBoundedConnectionMatrixDomain405.bounded_sourceGamma_integrable
#print axioms KLSConstantImprovement.ActualBoundedConnectionMatrixDomain405.bounded_sourceThirdAlong_white_memLp
#print axioms KLSConstantImprovement.ActualBoundedConnectionMatrixDomain405.actual_affine_third_white_memLp
