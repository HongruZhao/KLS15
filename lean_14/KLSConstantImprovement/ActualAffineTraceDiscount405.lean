import KLSConstantImprovement.ActualAffinePointwise405
import KLSConstantImprovement.ActualAffineSourceIdentities405

/-! The affine main discount on one actual weak canonical source.
Full three-slot symmetry, actual integral identities and the literal
projection square discharge every input to the division-free estimate. -/
noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualAffineTraceDiscount405
open KLS ActualBoundedCanonicalSource ActualSourceHessianEvolution405
open ActualAffineMatrixTests405 ActualAffineGlobalBalance405 ActualAffineRawBindings405
open ActualAffineSourceIdentities405 ActualAffinePointwise405
open ActualSourceDirectCubicBalance405 ActualDirectCubicMomentBinding405
open ActualQuarticCongruence405 ActualAffineFiniteExpansion405 ActualSourceQuarticBinding405
variable {n : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def actualAffineDiscount (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (∫ x, actualAffineTarget d T x ∂potentialMeasure d.potential) +
    ((∫ x, actualAffineGamma d T x ∂potentialMeasure d.potential) -
      ∫ x, actualAffineSignedConnection d T x ∂potentialMeasure d.potential) / 3

theorem actual_affine_pointwise_discount_ae (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      actualAffineSignedConnection d T x ≤ actualAffineGamma d T x ∧
      ∀ t : ℝ, 0 ≤ (actualAffineGamma d T x + 2 * actualAffineSignedConnection d T x) / 3 -
        2 * t * actualAffineCross d T x + t ^ 2 * actualDirectMoment d T x := by
  have hTs (a : Fin n) : (T a).IsSymm := Matrix.IsSymm.ext fun i j => hT23 a j i
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le] with x hx hN
  have hp := affine_pointwise_discount (coordinateHessian d.potential x) (actualAffineMatrix d T x)
    hx.1 (actualAffineMatrix_symmetric d T hTs x) T (sourceThirdMatrix d x) hT12 hT23
    (fun i j k => (hN i j k).1) (fun i j k => (hN i j k).2)
  simpa only [actualAffineSignedConnection, actualAffineGamma, actualAffineCross,
    actualDirectMoment, rawGram_eq_matrixTraceGram] using hp

theorem actual_affine_integrated_square (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) (t : ℝ) :
    0 ≤ ((∫ x, actualAffineGamma d T x ∂potentialMeasure d.potential) +
      2 * (∫ x, actualAffineSignedConnection d T x ∂potentialMeasure d.potential)) / 3 -
      2 * t * (∫ x, actualAffineCross d T x ∂potentialMeasure d.potential) +
      t ^ 2 * ∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential := by
  have hTs (a : Fin n) : (T a).IsSymm := Matrix.IsSymm.ext fun i j => hT23 a j i
  have hE := actual_affine_signed_integrable d T hTs
  have hG := actual_affine_gamma_integrable d T
  have hb := actual_affine_cross_integrable d T hTs
  have hW := actual_direct_moment_integrable d T
  have hp : 0 ≤ ∫ x, (actualAffineGamma d T x + 2 * actualAffineSignedConnection d T x) / 3 -
      2 * t * actualAffineCross d T x + t ^ 2 * actualDirectMoment d T x
        ∂potentialMeasure d.potential := by
    apply integral_nonneg_of_ae
    filter_upwards [actual_affine_pointwise_discount_ae d T hT12 hT23] with x hx
    exact hx.2 t
  have hE2 : Integrable (fun x => 2 * actualAffineSignedConnection d T x)
      (potentialMeasure d.potential) := hE.const_mul 2
  have hsum : Integrable (fun x => actualAffineGamma d T x + 2 * actualAffineSignedConnection d T x)
      (potentialMeasure d.potential) := hG.add hE2
  have hhead : Integrable (fun x => (actualAffineGamma d T x + 2 * actualAffineSignedConnection d T x) / 3)
      (potentialMeasure d.potential) := hsum.div_const 3
  have hcross : Integrable (fun x => 2 * t * actualAffineCross d T x)
      (potentialMeasure d.potential) := hb.const_mul (2*t)
  have hdiff : Integrable (fun x => (actualAffineGamma d T x + 2 * actualAffineSignedConnection d T x) / 3 -
      2 * t * actualAffineCross d T x) (potentialMeasure d.potential) := hhead.sub hcross
  have hlast : Integrable (fun x => t^2 * actualDirectMoment d T x)
      (potentialMeasure d.potential) := hW.const_mul (t^2)
  rw [integral_add hdiff hlast, integral_sub hhead hcross,
    integral_div, integral_add hG hE2, integral_const_mul,
    integral_const_mul, integral_const_mul] at hp
  exact hp

theorem actual_affine_discount_bounds (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    0 ≤ actualAffineDiscount d T ∧ actualAffineDiscount d T ≤
      ∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential := by
  have hTs (a : Fin n) : (T a).IsSymm := Matrix.IsSymm.ext fun i j => hT23 a j i
  have hp := actual_affine_target_nonnegative d T hTs
  have he : (∫ x, actualAffineSignedConnection d T x ∂potentialMeasure d.potential) ≤
      ∫ x, actualAffineGamma d T x ∂potentialMeasure d.potential := by
    apply integral_mono_ae (actual_affine_signed_integrable d T hTs) (actual_affine_gamma_integrable d T)
    filter_upwards [actual_affine_pointwise_discount_ae d T hT12 hT23] with x hx
    exact hx.1
  have hw := actual_affine_connection_identity d T hTs
  have hz := actual_affine_integrated_square d T hT12 hT23 0
  unfold actualAffineDiscount
  constructor <;> nlinarith

theorem actual_affine_cross_square_bound (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    2 * (∫ x, actualAffineCross d T x ∂potentialMeasure d.potential) ^ 2 ≤
      (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) *
        ((∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) - actualAffineDiscount d T) := by
  have hTs (a : Fin n) : (T a).IsSymm := Matrix.IsSymm.ext fun i j => hT23 a j i
  have hpoly : ∀ t : ℝ, 0 ≤
      (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) * (t*t) +
      (-2 * ∫ x, actualAffineCross d T x ∂potentialMeasure d.potential) * t +
      ((∫ x, actualAffineGamma d T x ∂potentialMeasure d.potential) +
        2 * (∫ x, actualAffineSignedConnection d T x ∂potentialMeasure d.potential)) / 3 := by
    intro t
    have hp := actual_affine_integrated_square d T hT12 hT23 t
    nlinarith
  have hd := discrim_le_zero hpoly
  simp only [discrim] at hd
  have hw := actual_affine_connection_identity d T hTs
  have heq : (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) - actualAffineDiscount d T =
      2 * (((∫ x, actualAffineGamma d T x ∂potentialMeasure d.potential) +
        2 * (∫ x, actualAffineSignedConnection d T x ∂potentialMeasure d.potential)) / 3) := by
    unfold actualAffineDiscount
    linarith
  rw [heq]
  nlinarith only [hd]

theorem actual_affine_main_discount (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    Real.sqrt 2 * (∫ x, actualAffineMainCost d T x ∂potentialMeasure d.potential) +
      actualAffineDiscount d T ≤
      (Real.sqrt 2 + 2) * ∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential := by
  have hTs (a : Fin n) : (T a).IsSymm := Matrix.IsSymm.ext fun i j => hT23 a j i
  have hmain := actual_affine_main_cross_identity d T hTs
  have hq := actual_affine_discount_bounds d T hT12 hT23
  have hc := actual_affine_cross_square_bound d T hT12 hT23
  have hW : 0 ≤ ∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential := hq.1.trans hq.2
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc' : (Real.sqrt 2 * (∫ x, actualAffineCross d T x ∂potentialMeasure d.potential)) ^ 2 ≤
      (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) *
        ((∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) - actualAffineDiscount d T) := by
    simpa only [mul_pow, hs] using hc
  by_cases hz : (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) = 0
  · rw [hz] at hc hmain hq
    have hb : (∫ x, actualAffineCross d T x ∂potentialMeasure d.potential) = 0 := by nlinarith
    have hJ : (∫ x, actualAffineMainCost d T x ∂potentialMeasure d.potential) = 0 := by
      rw [hb] at hmain
      linarith
    have hq0 : actualAffineDiscount d T = 0 := le_antisymm hq.2 hq.1
    rw [hJ, hq0, hz]
    simp only [mul_zero, zero_add, le_refl]
  · have hp : 0 < ∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential := lt_of_le_of_ne hW (Ne.symm hz)
    have hsq := sq_nonneg (Real.sqrt 2 * (∫ x, actualAffineCross d T x ∂potentialMeasure d.potential) -
      ∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential)
    have hprod : 0 ≤ (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) *
        (2 * (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) -
          2 * Real.sqrt 2 * (∫ x, actualAffineCross d T x ∂potentialMeasure d.potential) -
          actualAffineDiscount d T) := by nlinarith [hc', hsq]
    have hout := (mul_nonneg_iff_of_pos_left hp).mp hprod
    rw [hmain]
    nlinarith only [hout]

end KLSConstantImprovement.ActualAffineTraceDiscount405

#print axioms KLSConstantImprovement.ActualAffineTraceDiscount405.actual_affine_discount_bounds
#print axioms KLSConstantImprovement.ActualAffineTraceDiscount405.actual_affine_cross_square_bound
#print axioms KLSConstantImprovement.ActualAffineTraceDiscount405.actual_affine_main_discount
