import KLSConstantImprovement.ActualDirectCubicPointwise405
import KLSConstantImprovement.ActualSourceRawMetricPair405
import KLSConstantImprovement.ActualSourceCurvatureDomains405
import KLSConstantImprovement.ActualSourceHessianPolynomialTests405

/-! Genuine direct cubic source cross energy and its exact positive
commutator remainder. Every integral domain is paid by actual SourceData
H/G metric gradients and the proved L1 third-Gram curvature. -/
noncomputable section
open Matrix MeasureTheory Set Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualSourceDirectCubicEnergy405
open KLS ActualBoundedCanonicalSource ActualCompactRawMetricGraph
open ActualSourceHessianEvolution405 ActualSourceTensorGramMetricBinding
open ActualSourceRawMetricPair405 ActualSourceCurvatureDomains405 ActualSourceHessianPolynomialTests405
open ActualQuarticCongruence405 ActualSourceQuarticBinding405
open ActualDirectCubicWhitening405 ActualDirectCubicCoefficients405 ActualDirectCubicPointwise405
variable {n : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def actualDirectCrossEnergy (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, ∑ r,
    rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
      rawCanonicalMetricDerivative d.potential (sourceTensorGramRawDerivative d.potential d.third T i j) r x

def actualDirectGammaEnergy (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (matrixTraceGram (coordinateHessian d.potential x) T *
    matrixTraceGram (coordinateHessian d.potential x)⁻¹ (sourceThirdMatrix d x)).trace

theorem actual_direct_cross_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (actualDirectCrossEnergy d T) (potentialMeasure d.potential) := by
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  apply integrable_finsetSum Finset.univ
  intro r _
  exact (d.hessian_entry_raw_metric_memLp i j r).integrable_mul (d.tensorGram_raw_metric_memLp T i j r)

private theorem sum4_swap (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ a, ∑ b, f i j a b) = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
  have hs : (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, f p.1 p.2 q.1 q.2) =
      ∑ q : Fin n × Fin n, ∑ p : Fin n × Fin n, f p.1 p.2 q.1 q.2 := Finset.sum_comm
  simpa only [Fintype.sum_prod_type] using hs

theorem actual_direct_cross_raw_binding (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      actualDirectCrossEnergy d T x =
        directCrossEnergy (coordinateHessian d.potential x) T (sourceThirdMatrix d x) := by
  have hp : ∀ᵐ x ∂potentialMeasure d.potential, ∀ i j,
      (∑ r, rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
        rawCanonicalMetricDerivative d.potential (sourceTensorGramRawDerivative d.potential d.third T i j) r x) =
      ∑ a, ∑ b, (coordinateHessian d.potential x)⁻¹ a b * d.third x a i j *
        sourceTensorGramRawDerivative d.potential d.third T i j b x :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
      actual_raw_metric_pair_ae d (fun a y => d.third y a i j)
        (sourceTensorGramRawDerivative d.potential d.third T i j)
  filter_upwards [hp] with x hx
  unfold actualDirectCrossEnergy directCrossEnergy ActualQuarticCompression405.entryPair
  simp_rw [hx]
  simp only [actual_gram_raw_derivative_binding, Finset.mul_sum]
  rw [sum4_swap]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [sourceThirdMatrix, Matrix.of_apply]
  ring

theorem actual_direct_gram_entry_top (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    MemLp (fun x => matrixTraceGram (coordinateHessian d.potential x) T i j) ∞
      (potentialMeasure d.potential) := by
  have hg : Continuous (fun H : Matrix (Fin n) (Fin n) ℝ => matrixTraceGram H T i j) := by
    unfold matrixTraceGram
    fun_prop
  obtain ⟨hm, B, hb⟩ := actual_hessian_polynomial_bounded d _ hg
  exact memLp_top_of_bound hm B (Eventually.of_forall hb)

theorem actual_direct_gamma_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (actualDirectGammaEnergy d T) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  change Integrable (fun x => ∑ i, ∑ j,
    matrixTraceGram (coordinateHessian d.potential x) T i j *
      matrixTraceGram (coordinateHessian d.potential x)⁻¹ (sourceThirdMatrix d x) j i)
        (potentialMeasure d.potential)
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  have hm : MemLp (fun x => matrixTraceGram (coordinateHessian d.potential x) T i j *
      matrixTraceGram (coordinateHessian d.potential x)⁻¹ (sourceThirdMatrix d x) j i) 1
      (potentialMeasure d.potential) :=
    (actual_direct_gram_entry_top d T i j).mul
      (memLp_one_iff_integrable.mpr (actual_third_gram_entry_integrable d j i))
  exact hm.integrable le_rfl

theorem actual_direct_cubic_commutator_square (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      actualDirectGammaEnergy d T x - actualDirectCrossEnergy d T x / 2 =
        (1 / 2 : ℝ) * directCubicCommutatorCharge (coordinateHessian d.potential x) T
          (sourceThirdMatrix d x) := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le,
    actual_direct_cross_raw_binding d T] with x hx hN hp
  have hN12 (i j k : Fin n) : sourceThirdMatrix d x i j k = sourceThirdMatrix d x j i k := (hN i j k).1
  have hN23 (i j k : Fin n) : sourceThirdMatrix d x i j k = sourceThirdMatrix d x i k j := (hN i j k).2
  have hNs (a : Fin n) : (sourceThirdMatrix d x a).IsSymm := Matrix.IsSymm.ext fun i j => hN23 a j i
  have he := direct_cubic_pointwise_commutator_square (coordinateHessian d.potential x) hx.1 T
    (sourceThirdMatrix d x) hT12 hT23 hN12 hN23
  have hc := directCrossEnergy_eq_twice_half (coordinateHessian d.potential x) T (sourceThirdMatrix d x) hNs
  rw [← hp] at hc
  rw [rawGram_eq_matrixTraceGram, rawGram_eq_matrixTraceGram] at he
  change actualDirectGammaEnergy d T x - _ = _ at he
  linarith

theorem actual_direct_cross_energy_bound (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    (∫ x, actualDirectCrossEnergy d T x ∂potentialMeasure d.potential) ≤
      2 * ∫ x, actualDirectGammaEnergy d T x ∂potentialMeasure d.potential := by
  have hp : ∀ᵐ x ∂potentialMeasure d.potential,
      actualDirectCrossEnergy d T x ≤ 2 * actualDirectGammaEnergy d T x := by
    filter_upwards [actual_direct_cubic_commutator_square d T hT12 hT23] with x hx
    have hn := directCubicCommutatorCharge_nonnegative (coordinateHessian d.potential x) T
      (sourceThirdMatrix d x)
    linarith
  have hi := integral_mono_ae (actual_direct_cross_integrable d T)
    ((actual_direct_gamma_integrable d T).const_mul 2) hp
  rwa [integral_const_mul] at hi

theorem actual_direct_cubic_charge_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    Integrable (fun x => directCubicCommutatorCharge (coordinateHessian d.potential x) T
      (sourceThirdMatrix d x)) (potentialMeasure d.potential) := by
  have hi := ((actual_direct_gamma_integrable d T).const_mul 2).sub (actual_direct_cross_integrable d T)
  apply hi.congr
  filter_upwards [actual_direct_cubic_commutator_square d T hT12 hT23] with x hx
  change 2 * actualDirectGammaEnergy d T x - actualDirectCrossEnergy d T x = _
  linarith

end KLSConstantImprovement.ActualSourceDirectCubicEnergy405

#print axioms KLSConstantImprovement.ActualSourceDirectCubicEnergy405.actual_direct_cross_integrable
#print axioms KLSConstantImprovement.ActualSourceDirectCubicEnergy405.actual_direct_cross_raw_binding
#print axioms KLSConstantImprovement.ActualSourceDirectCubicEnergy405.actual_direct_cubic_commutator_square
#print axioms KLSConstantImprovement.ActualSourceDirectCubicEnergy405.actual_direct_cross_energy_bound
#print axioms KLSConstantImprovement.ActualSourceDirectCubicEnergy405.actual_direct_cubic_charge_integrable
