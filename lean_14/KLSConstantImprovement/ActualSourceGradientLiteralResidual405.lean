import KLSConstantImprovement.ActualSourceGradientCoordinatePair405
import KLSConstantImprovement.ActualSourceGradientCombinedEnergy405
import KLSConstantImprovement.ActualMetricMatrixCongruence405

/-! The Hilbert response is exactly the signed literal source-gradient
response obtained by genuine global integration by parts. In particular
this does not substitute the ordinary-target Poisson Hessian or metric.
-/
noncomputable section
open MeasureTheory Matrix Filter ProbabilityTheory
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualSourceGradientLiteralResidual405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalTargetCurvatureDomain405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricOrdinaryGraph
open ActualSourceNaturalHessian405 ActualSourceNaturalWhitenedHessian405
open ActualCubicSourceDatum405 ActualCubicRepresenter ActualCubicMatrixFactorization405
open ActualAffineResponseHilbert405 ActualAffineMatrixTests405 ActualMetricMatrixCongruence405
open ActualQuarticCompression405 ActualSourceGradientCoordinatePair405
open ActualSourceGradientCombinedEnergy405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_white_pair_main_expansion (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      entryPair (naturalWhitenedHessian d g Du x) (actualAffineWhiteMatrix d T x) =
        ∑ i, ∑ j, ∑ k, T i j k *
          (gradient d.potential x k * naturalCanonicalHessian d g Du x i j) := by
  filter_upwards [d.hessian_ae_source] with x hp
  let R := canonicalMetricRoot d.potential x
  let S := canonicalMetricUnroot d.potential x
  let C := naturalCanonicalHessian d g Du x
  let A := actualAffineMatrix d T x
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm _
  have hS : S.IsSymm := hR.inv
  have hc := entryPair_dual_congruence R S C A (canonicalMetricUnroot_mul_root_at hp.1)
  rw [hR.eq, hS.eq] at hc
  change entryPair (R * C * R) (S * A * S) = _
  rw [hc]
  simp only [entryPair, A, actualAffineMatrix, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [h12 k i j, h23 i k j]
  ring

theorem matrixHilbert_inner_integral (d : SourceData μ)
    (K L : MatrixL2 d.potential)
    (A B : Space n → Matrix (Fin n) (Fin n) ℝ)
    (hK : ∀ i j, (K i j : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => A x i j)
    (hL : ∀ i j, (L i j : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => B x i j) :
    inner ℝ K L = ∫ x, entryPair (A x) (B x) ∂potentialMeasure d.potential := by
  simp only [PiLp.inner_apply]
  simp_rw [L2.real_inner_eq_integral]
  have hi (i j : Fin n) : Integrable (fun x => K i j x * L i j x)
      (potentialMeasure d.potential) := (Lp.memLp _).integrable_mul (Lp.memLp _)
  have hrow (i : Fin n) :
      (∑ j, ∫ x, K i j x * L i j x ∂potentialMeasure d.potential) =
        ∫ x, ∑ j, K i j x * L i j x ∂potentialMeasure d.potential :=
    (integral_finsetSum Finset.univ fun j _ => hi i j).symm
  simp_rw [hrow]
  rw [← integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ fun j _ => hi i j)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hK i j,
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hL i j] with x hk hl
  simp only [hk, hl, entryPair]

theorem actual_source_gradient_main_pair_eq_inner (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hW : ∀ i j, MemLp (fun x => naturalWhitenedHessian d g Du x i j) 2
      (potentialMeasure d.potential))
    (hC : ∀ i j, MemLp (fun x => naturalCanonicalHessian d g Du x i j) 2
      (potentialMeasure d.potential)) :
    actualSourceGradientMainPair d T g Du =
      inner ℝ (naturalWhiteHilbert d g Du hW) (actualAffineHilbert d T) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hi (i j k : Fin n) : Integrable (fun x => T i j k *
      (gradient d.potential x k * naturalCanonicalHessian d g Du x i j))
      (potentialMeasure d.potential) := by
    have hm : MemLp (fun x => gradient d.potential x k *
        naturalCanonicalHessian d g Du x i j) 2 (potentialMeasure d.potential) :=
      (d.continuous_comp_gradient_memLp (EuclideanSpace.proj k).continuous ∞).mul (hC i j)
    exact (hm.integrable (by norm_num)).const_mul _
  calc
    actualSourceGradientMainPair d T g Du =
        ∫ x, ∑ i, ∑ j, ∑ k, T i j k *
          (gradient d.potential x k * naturalCanonicalHessian d g Du x i j)
          ∂potentialMeasure d.potential := by
      symm
      rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
        (fun j _ => integrable_finsetSum Finset.univ (fun k _ => hi i j k)))]
      simp_rw [integral_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun k _ => hi _ j k)),
        integral_finsetSum Finset.univ (fun k _ => hi _ _ k), integral_const_mul]
      rfl
    _ = ∫ x, entryPair (naturalWhitenedHessian d g Du x)
        (actualAffineWhiteMatrix d T x) ∂potentialMeasure d.potential :=
      (integral_congr_ae (actual_white_pair_main_expansion d T h12 h23 g Du)).symm
    _ = inner ℝ (naturalWhiteHilbert d g Du hW) (actualAffineHilbert d T) :=
      (matrixHilbert_inner_integral d (naturalWhiteHilbert d g Du hW) (actualAffineHilbert d T)
        (naturalWhitenedHessian d g Du) (actualAffineWhiteMatrix d T)
        (naturalWhiteLp_coe d g Du hW) (actualAffineWhiteLp_coe d T)).symm

theorem actual_source_gradient_response_eq_inner (d : SourceData μ)
    (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hW : ∀ i j, MemLp (fun x => naturalWhitenedHessian d
      (actualCubicDatum d T) Du x i j) 2 (potentialMeasure d.potential))
    (hC : ∀ i j, MemLp (fun x => naturalCanonicalHessian d
      (actualCubicDatum d T) Du x i j) 2 (potentialMeasure d.potential))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative
      (naturalCanonicalRawGradient d (actualCubicDatum d T) i)
      (fun x => naturalCanonicalHessian d (actualCubicDatum d T) Du x i j) j) :
    actualSourceGradientResponse d T (actualCubicDatum d T) =
      inner ℝ (naturalWhiteHilbert d (actualCubicDatum d T) Du hW)
        (actualResponseHilbert d T) := by
  have hcoord := actual_source_gradient_cubic_pair d hμ T h12 h23 Du hC hw
  rw [actual_source_gradient_main_pair_eq_inner d T h12 h23 _ Du hW hC] at hcoord
  have hfac := actual_cubic_fixed_hessian_factorization d hμ T h12 h23 Du hW hC hw
  have hsplit := congrArg (fun z => inner ℝ
    (naturalWhiteHilbert d (actualCubicDatum d T) Du hW) z)
      (actual_affine_response_hilbert_split d T)
  rw [inner_add_right, inner_smul_right] at hsplit
  have hcomm : inner ℝ (actualQuadraticHilbert d T)
      (naturalWhiteHilbert d (actualCubicDatum d T) Du hW) =
      inner ℝ (naturalWhiteHilbert d (actualCubicDatum d T) Du hW)
        (actualQuadraticHilbert d T) := (real_inner_comm _ _).symm
  linarith

end KLSConstantImprovement.ActualSourceGradientLiteralResidual405
#print axioms KLSConstantImprovement.ActualSourceGradientLiteralResidual405.actual_white_pair_main_expansion
#print axioms KLSConstantImprovement.ActualSourceGradientLiteralResidual405.matrixHilbert_inner_integral
#print axioms KLSConstantImprovement.ActualSourceGradientLiteralResidual405.actual_source_gradient_main_pair_eq_inner
#print axioms KLSConstantImprovement.ActualSourceGradientLiteralResidual405.actual_source_gradient_response_eq_inner
