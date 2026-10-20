import KLSConstantImprovement.ActualBoundedSourceCalculus
import KLSConstantImprovement.ActualWeakCanonicalMetricOrdinaryGraph
import KLSConstantImprovement.ActualCubicQuadraticDeficit

/-!
Actual quadratic Poisson rows eta=A^{-1}(q_B/2), constructed on the same
bounded-target canonical source. Literal polynomial datum integrability,
its genuine mean, the variational and compact weak equations, and its
energy bound are proved. No Poisson optimizer or row-field realization is
assumed. Second derivatives and the row production PDE remain separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Filter
open scoped BigOperators ContDiff RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceQuadraticEta405
open KLS ActualBoundedCanonicalSource
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricInverse
open ActualWeakCanonicalMetricOrdinaryGraph
open ActualCubicGradientEnergy ActualCubicAffineRegression ActualCubicQuadraticDeficit
open ActualDeficitTensorBounds KLSBelow25.CubicSymmetricNoise
variable {n : ℕ} {μ : Measure (Space n)}

private theorem halfQuadratic_contDiff (B : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ActualCubicGradientEnergy.centeredQuadratic B x / 2) := by
  exact (((contDiff_matrixQuadratic B).sub contDiff_const).div_const 2).of_le (by simp)

def quadraticSourceDatum (d : SourceData μ) (B : Matrix (Fin n) (Fin n) ℝ) :
    Lp ℝ 2 (potentialMeasure d.potential) :=
  (d.continuous_comp_gradient_memLp (halfQuadratic_contDiff B).continuous 2).toLp
    (fun x => ActualCubicGradientEnergy.centeredQuadratic B (gradient d.potential x) / 2)

theorem quadraticSourceDatum_ae (d : SourceData μ) (B : Matrix (Fin n) (Fin n) ℝ) :
    (quadraticSourceDatum d B : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => ActualCubicGradientEnergy.centeredQuadratic B (gradient d.potential x) / 2 :=
  (d.continuous_comp_gradient_memLp (halfQuadratic_contDiff B).continuous 2).coeFn_toLp

theorem quadraticSourceDatum_mean_zero (d : SourceData μ) (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, quadraticSourceDatum d B x ∂potentialMeasure d.potential) = 0 := by
  rw [integral_congr_ae (quadraticSourceDatum_ae d B),
    d.integral_comp_gradient (halfQuadratic_contDiff B).continuous]
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, centeredQuadratic_mean_zero hμ B, zero_mul]

/-- The actual same-source eta row, a completed canonical form element. -/
def quadraticSourceEta (d : SourceData μ) (B : Matrix (Fin n) (Fin n) ℝ) :
    CanonicalMetricH1 d.potential := sourceMetricInverseH1 d (quadraticSourceDatum d B)

theorem quadraticSourceEta_variational (d : SourceData μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (V : CanonicalMetricH1 d.potential) :
    canonicalMetricEnergy d.potential (quadraticSourceEta d B) V =
      inner ℝ (quadraticSourceDatum d B) (canonicalMetricValue d.potential V) :=
  sourceMetricInverse_variational d _ V

/-- The literal datum has zero mean, so the actual eta equation has no
unpaid constant correction even on uncentered compact source tests. -/
theorem quadraticSourceEta_compact_test (d : SourceData μ) (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∫ x, canonicalMetricGradient d.potential i (quadraticSourceEta d B) x *
      canonicalMetricDerivative d.potential ψ i x ∂potentialMeasure d.potential) =
      ∫ x, (ActualCubicGradientEnergy.centeredQuadratic B (gradient d.potential x) / 2) *
        ψ x ∂potentialMeasure d.potential := by
  letI := d.source_probability
  have heq := sourceMetricInverse_compact_test d (quadraticSourceDatum d B) hψ hc
  have hψ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ.continuous hc
  have hprod : Integrable (fun x => quadraticSourceDatum d B x * ψ x)
      (potentialMeasure d.potential) := (Lp.memLp (quadraticSourceDatum d B)).integrable_mul hψ2
  have hconst := ((Lp.memLp (quadraticSourceDatum d B)).integrable (by norm_num)).mul_const
    (∫ y, ψ y ∂potentialMeasure d.potential)
  have hr : (∫ x, quadraticSourceDatum d B x *
      (ψ x - ∫ y, ψ y ∂potentialMeasure d.potential) ∂potentialMeasure d.potential) =
      ∫ x, quadraticSourceDatum d B x * ψ x ∂potentialMeasure d.potential := by
    calc
      _ = ∫ x, quadraticSourceDatum d B x * ψ x - quadraticSourceDatum d B x *
          (∫ y, ψ y ∂potentialMeasure d.potential) ∂potentialMeasure d.potential := by
        apply integral_congr_ae
        exact Eventually.of_forall fun _ => by ring
      _ = _ := by
        rw [integral_sub hprod hconst, integral_mul_const,
          quadraticSourceDatum_mean_zero d hμ B, zero_mul, sub_zero]
  rw [hr] at heq
  exact heq.trans (integral_congr_ae ((quadraticSourceDatum_ae d B).fun_mul EventuallyEq.rfl))

theorem quadraticSourceDatum_norm_sq (d : SourceData μ) (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    ‖quadraticSourceDatum d B‖ ^ 2 =
      ProbabilityTheory.variance (ActualCubicGradientEnergy.centeredQuadratic B) μ / 4 := by
  letI := d.source_probability
  letI := hμ.isProb
  have hq : Continuous (ActualCubicGradientEnergy.centeredQuadratic B) :=
    ((contDiff_matrixQuadratic B).sub contDiff_const).continuous
  have hv : ProbabilityTheory.variance (ActualCubicGradientEnergy.centeredQuadratic B) μ =
      ∫ x, ActualCubicGradientEnergy.centeredQuadratic B x ^ 2 ∂μ := by
    rw [ProbabilityTheory.variance_eq_integral hq.aemeasurable, centeredQuadratic_mean_zero hμ B]
    simp only [sub_zero]
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ x, (ActualCubicGradientEnergy.centeredQuadratic B (gradient d.potential x) / 2) ^ 2
        ∂potentialMeasure d.potential := by
      apply integral_congr_ae
      filter_upwards [quadraticSourceDatum_ae d B] with x hx
      simp only [RCLike.inner_apply, conj_trivial, hx, pow_two]
    _ = ∫ x, (ActualCubicGradientEnergy.centeredQuadratic B x / 2) ^ 2 ∂μ :=
      d.integral_comp_gradient ((halfQuadratic_contDiff B).continuous.pow 2)
    _ = (∫ x, ActualCubicGradientEnergy.centeredQuadratic B x ^ 2 ∂μ) / 4 := by
      simp_rw [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num]
      rw [integral_div]
    _ = _ := by rw [← hv]

/-- The actual source BL inverse pays the row's natural first-order
energy; quadratic8 is an original-law theorem, not a free moment input. -/
theorem quadraticSourceEta_energy_le_two (d : SourceData μ) (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    canonicalMetricEnergy d.potential (quadraticSourceEta d B) (quadraticSourceEta d B) ≤
      2 * matrixFrobeniusSq B := by
  have he := sourceMetricInverse_energy_identity d (quadraticSourceDatum d B)
  have hn := sourceMetricInverse_norm_le d (quadraticSourceDatum d B)
  have hi := real_inner_le_norm (quadraticSourceDatum d B)
    (sourceMetricInverse d (quadraticSourceDatum d B))
  have hb := centeredQuadratic_variance_le_eight hμ B hB
  rw [← canonicalMetricEnergy_self] at he
  change canonicalMetricEnergy d.potential (quadraticSourceEta d B) (quadraticSourceEta d B) = _ at he
  rw [he]
  calc
    _ ≤ ‖quadraticSourceDatum d B‖ * ‖sourceMetricInverse d (quadraticSourceDatum d B)‖ := hi
    _ ≤ ‖quadraticSourceDatum d B‖ ^ 2 := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left hn (norm_nonneg (quadraticSourceDatum d B))
    _ ≤ _ := by rw [quadraticSourceDatum_norm_sq d hμ B]; linarith

theorem quadraticSourceEta_mean_zero (d : SourceData μ) (B : Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, canonicalMetricValue d.potential (quadraticSourceEta d B) x
      ∂potentialMeasure d.potential) = 0 := by
  letI := d.source_probability
  exact canonicalMetricValue_integral_eq_zero d.source_C1.continuous _

end KLSConstantImprovement.ActualSourceQuadraticEta405

#print axioms KLSConstantImprovement.ActualSourceQuadraticEta405.quadraticSourceDatum_mean_zero
#print axioms KLSConstantImprovement.ActualSourceQuadraticEta405.quadraticSourceEta_compact_test
#print axioms KLSConstantImprovement.ActualSourceQuadraticEta405.quadraticSourceDatum_norm_sq
#print axioms KLSConstantImprovement.ActualSourceQuadraticEta405.quadraticSourceEta_energy_le_two
