import KLSConstantImprovement.ActualCubicHilbertUpper405
import KLSConstantImprovement.ActualAffineMatrixTests405
import KLSConstantImprovement.ActualAffineGlobalBalance405

/-! The actual affine matrix Z and response F=2U-Z in the same weighted
matrix Hilbert space as the cubic factorization. All L2 domains follow
from bounded source roots and the genuine quadratic eta form. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace Filter ProbabilityTheory
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualAffineResponseHilbert405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCubicRepresenter ActualCubicSourceDatum405 ActualSourceNaturalGaffney405
open ActualSourceLocalizedGaffney405 ActualSourceMetricFaithfulness405
open ActualWeakCanonicalMetricOrdinaryGraph ActualSourceLimitFluxDomains405
open ActualQuadraticResponseField405 ActualQuadraticHilbertMatrix405 ActualCubicMatrixFactorization405
open ActualAffineMatrixTests405 ActualAffineGlobalBalance405 ActualCubicHilbertUpper405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def actualAffineWhiteMatrix (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  canonicalMetricUnroot d.potential x * actualAffineMatrix d T x * canonicalMetricUnroot d.potential x

theorem actualAffineWhiteMatrix_memLp (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    MemLp (fun x => actualAffineWhiteMatrix d T x i j) 2 (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hS (a b : Fin n) := actualUnroot_entry_memLp_top d a b
  have hZ (a b : Fin n) : MemLp (fun x => actualAffineMatrix d T x a b) ∞
      (potentialMeasure d.potential) :=
    (memLp_congr_ae (Eventually.of_forall (affineSliceTest_value d T a b))).mp
      (affineSliceTest d T a b).value_top
  have hSZ (a b : Fin n) : MemLp (fun x =>
      (canonicalMetricUnroot d.potential x * actualAffineMatrix d T x) a b) ∞
      (potentialMeasure d.potential) :=
    memLp_matrix_mul_entries (p := ∞) (q := ∞) (r := ∞) hS hZ a b
  have hm : MemLp (fun x => actualAffineWhiteMatrix d T x i j) ∞ (potentialMeasure d.potential) :=
    memLp_matrix_mul_entries (p := ∞) (q := ∞) (r := ∞) hSZ hS i j
  exact hm.mono_exponent (by simp)

def actualAffineWhiteLp (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : Lp ℝ 2 (potentialMeasure d.potential) := (actualAffineWhiteMatrix_memLp d T i j).toLp _

theorem actualAffineWhiteLp_coe (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (actualAffineWhiteLp d T i j : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => actualAffineWhiteMatrix d T x i j := (actualAffineWhiteMatrix_memLp d T i j).coeFn_toLp

def actualResponseWhiteMatrix (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  canonicalMetricUnroot d.potential x * quadraticResponseMatrix d T x * canonicalMetricUnroot d.potential x

theorem actualResponseWhiteMatrix_split (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    actualResponseWhiteMatrix d T x = (2 : ℝ) • actualQuadraticWhiteMatrix d T x - actualAffineWhiteMatrix d T x := by
  have hf : quadraticResponseMatrix d T x =
      (2 : ℝ) • actualQuadraticFluxMatrix d T x - actualAffineMatrix d T x := by
    ext i j
    rfl
  simp only [actualResponseWhiteMatrix, hf, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, actualQuadraticWhiteMatrix, actualAffineWhiteMatrix]

def actualResponseWhiteLp (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : Lp ℝ 2 (potentialMeasure d.potential) :=
  (2 : ℝ) • actualQuadraticWhiteLp d T i j - actualAffineWhiteLp d T i j

theorem actualResponseWhiteLp_coe (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (actualResponseWhiteLp d T i j : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => actualResponseWhiteMatrix d T x i j := by
  filter_upwards [Lp.coeFn_sub ((2 : ℝ) • actualQuadraticWhiteLp d T i j) (actualAffineWhiteLp d T i j),
    Lp.coeFn_smul (2 : ℝ) (actualQuadraticWhiteLp d T i j),
    actualQuadraticWhiteLp_coe d T i j, actualAffineWhiteLp_coe d T i j] with x hs hm hu hz
  change ((2 : ℝ) • actualQuadraticWhiteLp d T i j - actualAffineWhiteLp d T i j) x = _
  rw [hs]
  simp only [Pi.sub_apply, hm, Pi.smul_apply, smul_eq_mul, hu, hz,
    actualResponseWhiteMatrix_split, Matrix.sub_apply, Matrix.smul_apply]

def actualAffineHilbert (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : MatrixL2 d.potential :=
  WithLp.toLp 2 fun i => WithLp.toLp 2 (actualAffineWhiteLp d T i)

def actualResponseHilbert (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : MatrixL2 d.potential :=
  WithLp.toLp 2 fun i => WithLp.toLp 2 (actualResponseWhiteLp d T i)

theorem actual_affine_response_hilbert_split (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    actualAffineHilbert d T + actualResponseHilbert d T = (2 : ℝ) • actualQuadraticHilbert d T := by
  apply WithLp.ofLp_injective
  funext i
  apply WithLp.ofLp_injective
  funext j
  change actualAffineWhiteLp d T i j +
    ((2 : ℝ) • actualQuadraticWhiteLp d T i j - actualAffineWhiteLp d T i j) =
      (2 : ℝ) • actualQuadraticWhiteLp d T i j
  abel

theorem matrixHilbert_norm_integral (d : SourceData μ) (K : MatrixL2 d.potential)
    (A : Space n → Matrix (Fin n) (Fin n) ℝ)
    (hK : ∀ i j, (K i j : Space n → ℝ) =ᵐ[potentialMeasure d.potential] fun x => A x i j) :
    ‖K‖ ^ 2 = ∫ x, matrixFrobeniusSq (A x) ∂potentialMeasure d.potential := by
  simp only [PiLp.norm_sq_eq_of_L2]
  simp_rw [L2.norm_sq_eq_integral_sq]
  have hi (i j : Fin n) : Integrable (fun x => K i j x ^ 2) (potentialMeasure d.potential) :=
    (Lp.memLp _).integrable_sq
  have hrow (i : Fin n) : (∑ j, ∫ x, K i j x ^ 2 ∂potentialMeasure d.potential) =
      ∫ x, ∑ j, K i j x ^ 2 ∂potentialMeasure d.potential :=
    (integral_finsetSum Finset.univ fun j _ => hi i j).symm
  simp_rw [hrow]
  rw [← integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun j _ => hi i j)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hK i j] with x hx
  simp only [hx, matrixFrobeniusSq]

theorem actualAffineHilbert_norm (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    ‖actualAffineHilbert d T‖ ^ 2 =
      ∫ x, actualAffineMainCost d T x ∂potentialMeasure d.potential := by
  rw [matrixHilbert_norm_integral d (actualAffineHilbert d T) (actualAffineWhiteMatrix d T)
    (actualAffineWhiteLp_coe d T)]
  apply integral_congr_ae
  filter_upwards [d.hessian_ae_source] with x hx
  have hS : (canonicalMetricUnroot d.potential x).IsSymm := inverseSqrtMatrix_isSymm _ |>.inv
  have hSS := canonicalMetricUnroot_gram_at hx.1
  rw [hS.eq] at hSS
  rw [actualAffineWhiteMatrix, frobenius_white_matrix _ _ hS, hSS,
    (actualAffineMatrix_symmetric d T hT x).eq]
  change (coordinateHessian d.potential x * actualAffineMatrix d T x *
    coordinateHessian d.potential x * actualAffineMatrix d T x).trace =
      (actualAffineMatrix d T x * coordinateHessian d.potential x *
        actualAffineMatrix d T x * coordinateHessian d.potential x).trace
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (coordinateHessian d.potential x)
    (actualAffineMatrix d T x * coordinateHessian d.potential x * actualAffineMatrix d T x)

def actualResponseMatrixCost (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (coordinateHessian d.potential x * quadraticResponseMatrix d T x *
    coordinateHessian d.potential x * (quadraticResponseMatrix d T x).transpose).trace

theorem actualResponseHilbert_norm (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ‖actualResponseHilbert d T‖ ^ 2 =
      ∫ x, actualResponseMatrixCost d T x ∂potentialMeasure d.potential := by
  rw [matrixHilbert_norm_integral d (actualResponseHilbert d T) (actualResponseWhiteMatrix d T)
    (actualResponseWhiteLp_coe d T)]
  apply integral_congr_ae
  filter_upwards [d.hessian_ae_source] with x hx
  have hS : (canonicalMetricUnroot d.potential x).IsSymm := inverseSqrtMatrix_isSymm _ |>.inv
  have hSS := canonicalMetricUnroot_gram_at hx.1
  rw [hS.eq] at hSS
  rw [actualResponseWhiteMatrix, frobenius_white_matrix _ _ hS, hSS]
  rfl

theorem actual_cubic_variance_split_of_mass_bound (d : SourceData μ)
    (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (actualCubicDatum d T)) x ≤ C) :
    variance (tensorPolynomial μ T) μ ≤
      (72 / 5 : ℝ) * (∫ x, actualAffineMainCost d T x ∂potentialMeasure d.potential) +
        24 * ∫ x, actualResponseMatrixCost d T x ∂potentialMeasure d.potential := by
  obtain ⟨W, hW, hv⟩ := exists_actual_cubic_matrix_pairing_of_mass_bound d hn hμ T hT12 hT23 hC hM
  have hp := six_pairing_split_upper (actualQuadraticHilbert d T) (actualAffineHilbert d T)
    (actualResponseHilbert d T) W hW hv (actual_affine_response_hilbert_split d T)
  rwa [actualAffineHilbert_norm d T (fun i => Matrix.IsSymm.ext fun j k => hT23 i k j),
    actualResponseHilbert_norm] at hp

end KLSConstantImprovement.ActualAffineResponseHilbert405
#print axioms KLSConstantImprovement.ActualAffineResponseHilbert405.actualAffineHilbert_norm
#print axioms KLSConstantImprovement.ActualAffineResponseHilbert405.actualResponseHilbert_norm
#print axioms KLSConstantImprovement.ActualAffineResponseHilbert405.actual_affine_response_hilbert_split
#print axioms KLSConstantImprovement.ActualAffineResponseHilbert405.actual_cubic_variance_split_of_mass_bound
