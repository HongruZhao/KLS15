import KLSConstantImprovement.ActualBoundedSourceCalculus
import KLS.SpectralQuadraticTransport
import KLS.TensorCommutatorComparison
import KLS.RawWeakTraceDerivative

/-! The quadratic matrix cap on the actual constructed source, including
signed symmetric coefficients. The absolute spectral transport is constructed
and its pointwise trace comparison is proved; no matrix-cap witness is assumed.
-/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceQuadraticSandwich405
open KLS ActualBoundedCanonicalSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ}

theorem spectral_sandwich_comparison (M A U H : Matrix (Fin n) (Fin n) ℝ)
    (hM : M = A.transpose * U * A) (hU : U.IsSymm)
    (horth : U.transpose * U = 1) (hH : H.IsSymm) :
    (M * H * M * H).trace ≤
      (A.transpose * A * H * (A.transpose * A) * H).trace := by
  let K := A * H * A.transpose
  have hK : K.IsSymm := by
    unfold K
    change (A * H * A.transpose).transpose = A * H * A.transpose
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hH.eq, Matrix.mul_assoc]
  have hO : U * U = 1 := by simpa only [hU.eq] using horth
  have hb := matrix_trace_cross_le_square U K hU hK
  rw [hO, Matrix.one_mul] at hb
  have hleft : (M * H * M * H).trace = ((U * K) * (U * K)).trace := by
    rw [hM]
    calc
      _ = (A.transpose * (U * A * H * A.transpose * U * A * H)).trace := by
        simp only [Matrix.mul_assoc]
      _ = ((U * A * H * A.transpose * U * A * H) * A.transpose).trace :=
        Matrix.trace_mul_comm _ _
      _ = _ := by simp only [K, Matrix.mul_assoc]
  rw [hleft]
  calc
    _ ≤ (K * K).trace := hb
    _ = matrixFrobeniusSq K := (matrixFrobeniusSq_eq_trace_sq hK).symm
    _ = _ := matrixFrobeniusSq_affine_congruence A H hH

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.signed_sandwich_integrable
    {μ : Measure (Space n)} (d : SourceData μ) (M : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => (M * coordinateHessian d.potential x * M *
      coordinateHessian d.potential x).trace) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  exact (rawHessianTraceSquare_memLp_top
    (fun i j => d.hessian_entry_memLp i j ∞) M).integrable (by simp)

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.integral_signed_sandwich_le_two
    {μ : Measure (Space n)} (d : SourceData μ) (hiso : IsIsotropic μ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    (∫ x, (M * coordinateHessian d.potential x * M *
      coordinateHessian d.potential x).trace ∂potentialMeasure d.potential) ≤
        2 * matrixFrobeniusSq M := by
  obtain ⟨A, U, B, _, hU, hB, horth, hAA, hpull, hnorm⟩ :=
    exists_spectral_quadratic_transport M hM
  have hBpos : B.PosSemidef := by
    rw [← hAA]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self A
  have hb := d.integral_trace_square_le hiso hBpos
  rw [← matrixFrobeniusSq_eq_trace_sq hB, hnorm] at hb
  apply le_trans (integral_mono_ae (d.signed_sandwich_integrable M)
    (d.signed_sandwich_integrable B) ?_) hb
  filter_upwards [d.hessian_ae_source] with x hx
  simpa only [rawHessianTraceSquare, hAA] using
    spectral_sandwich_comparison M A U (coordinateHessian d.potential x)
      hpull.symm hU horth hx.1.isHermitian.isSymm

theorem actual_family_sandwich_cap {μ : Measure (Space n)} (d : SourceData μ)
    (hiso : IsIsotropic μ) {κ : Type*} [Fintype κ]
    (T : κ → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    (∫ x, ∑ i, (T i * coordinateHessian d.potential x * T i *
      coordinateHessian d.potential x).trace ∂potentialMeasure d.potential) ≤
      2 * ∑ i, matrixFrobeniusSq (T i) := by
  rw [integral_finset_sum _ (fun i _ => d.signed_sandwich_integrable (T i))]
  calc
    _ ≤ ∑ i, 2 * matrixFrobeniusSq (T i) :=
      Finset.sum_le_sum (fun i _ => d.integral_signed_sandwich_le_two hiso (T i) (hT i))
    _ = _ := by rw [Finset.mul_sum]

end KLSConstantImprovement.ActualSourceQuadraticSandwich405
#print axioms KLSConstantImprovement.ActualSourceQuadraticSandwich405.spectral_sandwich_comparison
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.signed_sandwich_integrable
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.integral_signed_sandwich_le_two
#print axioms KLSConstantImprovement.ActualSourceQuadraticSandwich405.actual_family_sandwich_cap
