import KLSConstantImprovement.ActualTensorRowWhite405
import KLSConstantImprovement.ActualQuadraticRowCurvature405
import KLSConstantImprovement.ActualTraceResponse405

/-! The literal whole-row signed cross term. Its global L1 domain is
unconditional: H times the natural flux is the genuine ordinary L2
gradient, and the trace third derivative is L2. The Cauchy bound uses
the same actual row curvature, under the explicit quadratic mass gate. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualQuadraticRowEll405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualWeakCanonicalMetricOrdinaryGraph ActualSourceMetricFaithfulness405
open ActualSourceNaturalTargetCurvatureDomain405 ActualSourceQuadraticEta405
open ActualQuadraticResponseField405 ActualQuadraticHilbertMatrix405 ActualQuadraticRowCurvature405
open ActualSourceHessianEvolution405 ActualSourceCurvatureDomains405 ActualSourceDirectCubicBalance405
open ActualSourceQuarticBinding405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualResponseGramBound405
open ActualTensorRowWhite405 ActualQuarticCongruence405 ActualQuarticThirdWhitening405
open ActualDirectCubicWhitening405 ActualQuarticWhiteFrame405 ActualTraceResponse405
open ActualFullSymmetricTensorOrdering MixedCubicRankSlicing FourthCubicProjectionDefect
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def actualRowWhiteThird (d : SourceData μ) (A : Space n → Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) : Fin n → Fin n → Fin n → ℝ :=
  firstAction (canonicalMetricUnroot d.potential x * A x * canonicalMetricUnroot d.potential x).transpose
    (whiteThirdSlice (canonicalMetricRoot d.potential x) (sourceThirdMatrix d x))

def actualRowEll (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (actualQuadraticFluxMatrix d T x * coordinateHessian d.potential x * crossTraceGram T (sourceThirdMatrix d x)).trace

theorem actualRowWhiteThird_energy_ae (d : SourceData μ)
    (A : Space n → Matrix (Fin n) (Fin n) ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      cubicEnergy (actualRowWhiteThird d A x) =
        ((A x * coordinateHessian d.potential x * (A x).transpose) *
          matrixTraceGram (coordinateHessian d.potential x)⁻¹ (sourceThirdMatrix d x)).trace := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le] with x hx hN
  let Q := canonicalMetricUnroot d.potential x
  let R := canonicalMetricRoot d.potential x
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm _
  have hQ : Q.IsSymm := hR.inv
  have hQR : Q * R = 1 := canonicalMetricUnroot_mul_root_at hx.1
  have hRQ : R * Q = 1 := canonicalMetricRoot_mul_unroot_at hx.1
  have hQQ : Q * Q = coordinateHessian d.potential x := by
    have hh := canonicalMetricUnroot_gram_at hx.1
    rwa [hQ.eq] at hh
  have hRR : R * R = (coordinateHessian d.potential x)⁻¹ := by
    change inverseSqrtMatrix (coordinateHessian d.potential x) * inverseSqrtMatrix (coordinateHessian d.potential x) = _
    unfold inverseSqrtMatrix
    rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self _ hx.1.posSemidef.nonneg]
  have he := white_row_tensor_energy Q R (A x) hQ hR hQR hRQ (sourceThirdMatrix d x)
    (fun i => Matrix.IsSymm.ext fun j k => (hN i k j).2)
  rw [hQQ, hRR, rawGram_eq_matrixTraceGram] at he
  exact he

theorem actualRowEll_white_ae (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      actualRowEll d T x = pairing (whiteThirdSlice (canonicalMetricUnroot d.potential x) T)
        (actualRowWhiteThird d (actualQuadraticFluxMatrix d T) x) := by
  filter_upwards [d.hessian_ae_source] with x hx
  have hR : (canonicalMetricRoot d.potential x).IsSymm := inverseSqrtMatrix_isSymm _
  have hQ : (canonicalMetricUnroot d.potential x).IsSymm := hR.inv
  have hQQ := canonicalMetricUnroot_gram_at hx.1
  rw [hQ.eq] at hQQ
  have he := white_row_tensor_pairing (canonicalMetricUnroot d.potential x) (canonicalMetricRoot d.potential x)
    (actualQuadraticFluxMatrix d T x) hQ hR (canonicalMetricUnroot_mul_root_at hx.1)
      (canonicalMetricRoot_mul_unroot_at hx.1) T (sourceThirdMatrix d x) hT
  rw [hQQ] at he
  exact he.symm

theorem actualRowEll_gradient_ae (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    actualRowEll d T =ᵐ[potentialMeasure d.potential] fun x => ∑ j, ∑ a,
      naturalCanonicalRawGradient d (quadraticSourceDatum d (T j)) a x * (T a * sourceThirdMatrix d x j).trace := by
  filter_upwards [d.hessian_ae_source, ae_all_iff.mpr fun j =>
    hessian_mul_naturalCanonicalFlux_ae d (quadraticSourceDatum d (T j))] with x hx hp
  have hrow (j a : Fin n) :
      (actualQuadraticFluxMatrix d T x * coordinateHessian d.potential x) j a =
        naturalCanonicalRawGradient d (quadraticSourceDatum d (T j)) a x := by
    have he := congrFun (hp j) a
    change (∑ b, quadraticRowFlux d T j b x * coordinateHessian d.potential x b a) = _
    rw [← he]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro b _
    rw [hx.1.isHermitian.isSymm.apply a b]
    unfold quadraticRowFlux
    ring
  change ((actualQuadraticFluxMatrix d T x * coordinateHessian d.potential x) * crossTraceGram T (sourceThirdMatrix d x)).trace = _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, crossTraceGram, Matrix.of_apply, hrow]

theorem trace_third_memLp (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (a j : Fin n) :
    MemLp (fun x => (T a * sourceThirdMatrix d x j).trace) 2 (potentialMeasure d.potential) := by
  convert actual_trace_derivative_memLp d T a j using 1
  funext x
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, sourceThirdMatrix, Matrix.of_apply]

theorem actualRowEll_integrable (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (actualRowEll d T) (potentialMeasure d.potential) := by
  have hi := integrable_finsetSum Finset.univ fun j _ => integrable_finsetSum Finset.univ fun a _ =>
    (naturalCanonicalRawGradient_memLp d (quadraticSourceDatum d (T j)) a).integrable_mul (trace_third_memLp d T a j)
  exact hi.congr (actualRowEll_gradient_ae d T).symm

theorem actualRowEll_integrated_square (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) {C : ℝ}
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    (∫ x, actualRowEll d T x ∂potentialMeasure d.potential) ^ 2 ≤
      (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) *
        ∫ x, actualRowCurvature d (actualQuadraticFluxMatrix d T) x ∂potentialMeasure d.potential := by
  have hW := actual_direct_moment_integrable d T
  have hE := actualRowEll_integrable d T
  have hK := actual_quadratic_row_curvature_integrable d T hM
  have hpoly (t : ℝ) : 0 ≤
      (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) * (t * t) +
        (-2 * ∫ x, actualRowEll d T x ∂potentialMeasure d.potential) * t +
          ∫ x, actualRowCurvature d (actualQuadraticFluxMatrix d T) x ∂potentialMeasure d.potential := by
    have hpoint : ∀ᵐ x ∂potentialMeasure d.potential,
        0 ≤ actualDirectMoment d T x * t ^ 2 - 2 * t * actualRowEll d T x +
          actualRowCurvature d (actualQuadraticFluxMatrix d T) x := by
      filter_upwards [d.hessian_ae_source, actualRowEll_white_ae d T hT,
        actualRowWhiteThird_energy_ae d (actualQuadraticFluxMatrix d T)] with x hx he hn
      let Q := canonicalMetricUnroot d.potential x
      let A := actualQuadraticFluxMatrix d T x
      let N := actualRowWhiteThird d (actualQuadraticFluxMatrix d T) x
      let Tw := whiteThirdSlice Q T
      have hQ : Q.IsSymm := inverseSqrtMatrix_isSymm _ |>.inv
      have hQQ : Q * Q = coordinateHessian d.potential x := by
        have hh := canonicalMetricUnroot_gram_at hx.1
        rwa [hQ.eq] at hh
      have ht : cubicEnergy Tw = actualDirectMoment d T x := by
        rw [cubicEnergy_eq_trace_whiteGram _ (whiteThirdSlice_symmetric Q hQ T hT),
          whiteGram_whiteThirdSlice Q hQ T, Matrix.trace_mul_cycle, hQQ, rawGram_eq_matrixTraceGram]
        rfl
      have hV := coordinateHessian_posSemidef_of_convex (d.target_smooth.of_le (by simp))
        d.target_convex_potential (gradient d.potential x)
      have hP : (sourceTargetCurvature d x).PosSemidef := by
        simpa only [sourceTargetCurvature, hx.1.isHermitian.eq] using
          hV.conjTranspose_mul_mul_same (coordinateHessian d.potential x)
      have hpos := trace_mul_nonneg_of_posSemidef (row_metric_gram_posSemidef _ A hx.1.posSemidef) hP
      have hsplit : actualRowCurvature d (actualQuadraticFluxMatrix d T) x =
          (A * coordinateHessian d.potential x * A.transpose * sourceTargetCurvature d x).trace + cubicEnergy N := by
        change _ = _ + cubicEnergy (actualRowWhiteThird d (actualQuadraticFluxMatrix d T) x)
        rw [hn]
        simp only [actualRowCurvature, sourceConnectionCurvature, sourceTargetCurvature,
          Matrix.mul_add, Matrix.trace_add, A]
      have hs := cubicEnergy_sub_mul N Tw t
      have hnonneg := cubicEnergy_nonneg (fun i j k => N i j k - t * Tw i j k)
      change actualRowEll d T x = pairing Tw N at he
      rw [ht, ← he] at hs
      nlinarith only [hs, hnonneg, hpos, hsplit]
    have hsum : Integrable (fun x => actualDirectMoment d T x * t ^ 2 - 2 * t * actualRowEll d T x)
        (potentialMeasure d.potential) := (hW.mul_const (t ^ 2)).sub (hE.const_mul (2 * t))
    have hp := integral_nonneg_of_ae hpoint
    rw [integral_add hsum hK, integral_sub (hW.mul_const (t ^ 2)) (hE.const_mul (2 * t)),
      integral_mul_const, integral_const_mul] at hp
    nlinarith only [hp]
  have hd := discrim_le_zero hpoly
  simp only [discrim] at hd
  nlinarith only [hd]

end KLSConstantImprovement.ActualQuadraticRowEll405
#print axioms KLSConstantImprovement.ActualQuadraticRowEll405.actualRowWhiteThird_energy_ae
#print axioms KLSConstantImprovement.ActualQuadraticRowEll405.actualRowEll_integrable
#print axioms KLSConstantImprovement.ActualQuadraticRowEll405.actualRowEll_integrated_square
