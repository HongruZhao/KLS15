import KLSConstantImprovement.ActualBoundedConnectionMatrixDomain405
import KLSConstantImprovement.ActualSourceResponseProduction405
import KLSConstantImprovement.ActualSourceNaturalTargetCurvatureDomain405

/-! The literal response target-curvature matrix has global L1 entries.
Its domain follows from the actual natural ordinary gradients, without
assuming that the unweighted flux rows themselves are globally L2. -/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualResponseTargetDomain405
open KLS ActualBoundedCanonicalSource ActualQuadraticResponseField405 ActualAffineMatrixTests405
open ActualBoundedConnectionMatrixDomain405 ActualSourceNaturalTargetCurvatureDomain405
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceHessianEvolution405
open ActualSourceCurvatureDomains405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_affine_times_hessian_memLp_top (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    MemLp (fun x => (actualAffineMatrix d T x * coordinateHessian d.potential x) i j) ∞
      (potentialMeasure d.potential) :=
  memLp_matrix_mul_entries (p := ∞) (q := ∞) (r := ∞)
    (actual_affine_row_memLp_top d T) (fun a b => d.hessian_entry_memLp a b ∞) i j

theorem actual_response_times_hessian_memLp (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    MemLp (fun x => (quadraticResponseMatrix d T x * coordinateHessian d.potential x) i j) 2
      (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hm : MemLp (fun x => 2 * naturalCanonicalRawGradient d (quadraticSourceDatum d (T i)) j x -
      (actualAffineMatrix d T x * coordinateHessian d.potential x) i j) 2
      (potentialMeasure d.potential) :=
    ((naturalCanonicalRawGradient_memLp d _ j).const_mul 2).sub
      ((actual_affine_times_hessian_memLp_top d T i j).mono_exponent (by simp))
  apply (memLp_congr_ae ?_).mp hm
  filter_upwards [d.hessian_ae_source, hessian_mul_naturalCanonicalFlux_ae d (quadraticSourceDatum d (T i))] with x hx hp
  have hu : (∑ a, quadraticRowFlux d T i a x * coordinateHessian d.potential x a j) =
      naturalCanonicalRawGradient d (quadraticSourceDatum d (T i)) j x := by
    calc
      _ = ∑ a, coordinateHessian d.potential x j a * quadraticRowFlux d T i a x := by
        exact Finset.sum_congr rfl fun a _ => by rw [hx.1.isHermitian.isSymm.apply a j]; ring
      _ = _ := congrFun hp j
  change _ = ∑ a, (2 * quadraticRowFlux d T i a x - actualAffineMatrix d T x i a) * coordinateHessian d.potential x a j
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  rw [hu]
  rfl

theorem actual_response_target_entry_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Integrable (fun x => (quadraticResponseMatrix d T x * sourceTargetCurvature d x *
      (quadraticResponseMatrix d T x).transpose) i j) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hV2 : ContDiff ℝ 2 d.targetPotential := d.target_smooth.of_le (by simp)
  have hV (a b : Fin n) : MemLp
      (fun x => coordinateHessian d.targetPotential (gradient d.potential x) a b) ∞
      (potentialMeasure d.potential) :=
    d.continuous_comp_gradient_memLp
      (contDiff_coordinateHessian hV2 (m := 0) (by norm_num) a b).continuous ∞
  have hfirst (a b : Fin n) : MemLp (fun x => ((quadraticResponseMatrix d T x *
      coordinateHessian d.potential x) * coordinateHessian d.targetPotential (gradient d.potential x)) a b)
      2 (potentialMeasure d.potential) :=
    memLp_matrix_mul_entries (p := 2) (q := ∞) (r := 2)
      (actual_response_times_hessian_memLp d T) hV a b
  have hlast (a b : Fin n) : MemLp (fun x => (quadraticResponseMatrix d T x *
      coordinateHessian d.potential x).transpose a b) 2 (potentialMeasure d.potential) :=
    actual_response_times_hessian_memLp d T b a
  have hm : MemLp (fun x => ((quadraticResponseMatrix d T x * coordinateHessian d.potential x) *
      coordinateHessian d.targetPotential (gradient d.potential x) *
        (quadraticResponseMatrix d T x * coordinateHessian d.potential x).transpose) i j)
      1 (potentialMeasure d.potential) :=
    memLp_matrix_mul_entries (p := 2) (q := 2) (r := 1) hfirst hlast i j
  apply (hm.integrable le_rfl).congr
  filter_upwards [d.hessian_ae_source] with x hx
  simp only [sourceTargetCurvature, Matrix.transpose_mul, hx.1.isHermitian.isSymm.eq,
    Matrix.mul_assoc]

end KLSConstantImprovement.ActualResponseTargetDomain405

#print axioms KLSConstantImprovement.ActualResponseTargetDomain405.actual_response_times_hessian_memLp
#print axioms KLSConstantImprovement.ActualResponseTargetDomain405.actual_response_target_entry_integrable
