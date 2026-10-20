import KLSConstantImprovement.ActualLocalCompactWeakTests405
import KLSConstantImprovement.ActualSourceVariationalCaccioppoli405
import KLSConstantImprovement.ActualSourceNaturalWhitenedHessian405

/-! Caccioppoli for an actual bounded local weak function and an L1
right-hand side. No global energy/form domain is assumed. -/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualBoundedWeakCaccioppoli405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph ActualCompactRawMetricGraph
open ActualLocalBoundedWeakAlgebra405 ActualLocalCompactWeakTests405 ActualSourceLocalWeakCalculus405
open ActualSourceNaturalWhitenedHessian405 ActualSourceLimitFluxDomains405
open ActualBoundedRawMetricDomain
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem local_raw_metric_derivative_memLp (d : SourceData μ) (f : LocalRawTest n)
    (r : Fin n) {E : Set (Space n)} (hE : IsCompact E) :
    MemLp (rawCanonicalMetricDerivative d.potential f.derivative r) 2 (volume.restrict E) :=
  memLp_finsetSum Finset.univ fun a _ =>
    (actualRoot_entry_top_on_compact d hE r a).mul (f.derivative_local a E hE)

theorem cutoff_raw_metric_derivative_memLp (d : SourceData μ) (f : LocalRawTest n)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (r : Fin n) :
    MemLp (fun x => χ x * rawCanonicalMetricDerivative d.potential f.derivative r x) 2
      (potentialMeasure d.potential) := by
  apply memLp_potentialMeasure_of_compact_localL2 d.source_C1.continuous hc.mul_right
  intro E hE
  exact memLp_continuous_mul_on_compact hE (local_raw_metric_derivative_memLp d f r hE) hχ.continuous

theorem metric_cutoff_square_product (d : SourceData μ) (f : LocalRawTest n)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (r : Fin n) (x : Space n) :
    rawCanonicalMetricDerivative d.potential (cutoffLocalRawTest (hχ.mul hχ) f).derivative r x =
      χ x ^ 2 * rawCanonicalMetricDerivative d.potential f.derivative r x +
        2 * χ x * f.value x * canonicalMetricDerivative d.potential χ r x := by
  simp only [rawCanonicalMetricDerivative, cutoffLocalRawTest, LocalRawTest.mul,
    smoothLocalRawTest, canonicalMetricDerivative,
    coordinateDerivative_mul (hχ.differentiable (by norm_num) x) (hχ.differentiable (by norm_num) x),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem bounded_weak_caccioppoli (d : SourceData μ) (f : LocalRawTest n)
    (b : Space n → ℝ) (hb : Integrable b (potentialMeasure d.potential))
    {B : ℝ} (hB : 0 ≤ B) (hf : MemLp f.value ∞ (potentialMeasure d.potential))
    (hbound : ∀ᵐ x ∂potentialMeasure d.potential, ‖f.value x‖ ≤ B)
    (hweak : ∀ θ : LocalRawTest n, HasCompactSupport θ.value →
      (∑ r, ∫ x, rawCanonicalMetricDerivative d.potential f.derivative r x *
        rawCanonicalMetricDerivative d.potential θ.derivative r x ∂potentialMeasure d.potential) =
          ∫ x, b x * θ.value x ∂potentialMeasure d.potential)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hχb : ∀ x, χ x ∈ Icc (0 : ℝ) 1) :
    (∑ r, ∫ x, (χ x * rawCanonicalMetricDerivative d.potential f.derivative r x) ^ 2
      ∂potentialMeasure d.potential) ≤
        2 * B * (∫ x, |b x| ∂potentialMeasure d.potential) +
          4 * B ^ 2 * ∑ r, ∫ x, canonicalMetricDerivative d.potential χ r x ^ 2
            ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let a : Fin n → Space n → ℝ := fun r x => χ x * rawCanonicalMetricDerivative d.potential f.derivative r x
  let z : Fin n → Space n → ℝ := fun r x => canonicalMetricDerivative d.potential χ r x * f.value x
  have ha (r : Fin n) : MemLp (a r) 2 (potentialMeasure d.potential) := cutoff_raw_metric_derivative_memLp d f hχ hc r
  have hz (r : Fin n) : MemLp (z r) 2 (potentialMeasure d.potential) := (d.metric_derivative_memLp hχ hc r).mul hf
  have haz (r : Fin n) : Integrable (fun x => a r x * z r x) (potentialMeasure d.potential) :=
    (ha r).integrable_mul (hz r)
  let E : ℝ := ∑ r, ∫ x, a r x ^ 2 ∂potentialMeasure d.potential
  let Z : ℝ := ∑ r, ∫ x, z r x ^ 2 ∂potentialMeasure d.potential
  let C : ℝ := ∑ r, ∫ x, a r x * z r x ∂potentialMeasure d.potential
  let θ := cutoffLocalRawTest (hχ.mul hχ) f
  have hχtop : MemLp χ ∞ (potentialMeasure d.potential) := hχ.continuous.memLp_of_hasCompactSupport hc
  have hχsqtop : MemLp (fun x => χ x * χ x) ∞ (potentialMeasure d.potential) := hχtop.mul hχtop
  have hθtop : MemLp θ.value ∞ (potentialMeasure d.potential) :=
    hχsqtop.mul hf
  have hrhs : Integrable (fun x => b x * θ.value x) (potentialMeasure d.potential) := by
    have hm : MemLp (fun x => θ.value x * b x) 1 (potentialMeasure d.potential) :=
      hθtop.mul (memLp_one_iff_integrable.mpr hb)
    exact (hm.integrable le_rfl).congr (Eventually.of_forall fun x => mul_comm _ _)
  have heq : E + 2 * C = ∫ x, b x * θ.value x ∂potentialMeasure d.potential := by
    have he := hweak θ (hc.mul_right.mul_right)
    have hi (r : Fin n) : (∫ x, rawCanonicalMetricDerivative d.potential f.derivative r x *
        rawCanonicalMetricDerivative d.potential θ.derivative r x ∂potentialMeasure d.potential) =
        (∫ x, a r x ^ 2 ∂potentialMeasure d.potential) +
          2 * (∫ x, a r x * z r x ∂potentialMeasure d.potential) := by
      calc
        _ = ∫ x, a r x ^ 2 + 2 * (a r x * z r x) ∂potentialMeasure d.potential := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            change rawCanonicalMetricDerivative d.potential f.derivative r x *
              rawCanonicalMetricDerivative d.potential (cutoffLocalRawTest (hχ.mul hχ) f).derivative r x =
                a r x ^ 2 + 2 * (a r x * z r x)
            rw [metric_cutoff_square_product d f hχ r x]
            dsimp only [a, z]
            ring
        _ = _ := by rw [integral_add (ha r).integrable_sq ((haz r).const_mul 2), integral_const_mul]
    simp_rw [hi] at he
    simpa only [E, C, Finset.sum_add_distrib, Finset.mul_sum] using he
  have hy : -4 * C ≤ E + 4 * Z := by
    have hi (r : Fin n) : -4 * (∫ x, a r x * z r x ∂potentialMeasure d.potential) ≤
        (∫ x, a r x ^ 2 ∂potentialMeasure d.potential) +
          4 * (∫ x, z r x ^ 2 ∂potentialMeasure d.potential) := by
      calc
        _ = ∫ x, -4 * (a r x * z r x) ∂potentialMeasure d.potential := (integral_const_mul _ _).symm
        _ ≤ ∫ x, a r x ^ 2 + 4 * z r x ^ 2 ∂potentialMeasure d.potential := by
          apply integral_mono ((haz r).const_mul (-4)) ((ha r).integrable_sq.add ((hz r).integrable_sq.const_mul 4))
          intro x
          change -4 * (a r x * z r x) ≤ a r x ^ 2 + 4 * z r x ^ 2
          nlinarith only [sq_nonneg (a r x + 2 * z r x)]
        _ = _ := by rw [integral_add (ha r).integrable_sq ((hz r).integrable_sq.const_mul 4), integral_const_mul]
    have hs := Finset.sum_le_sum (s := Finset.univ) fun r _ => hi r
    simpa only [E, C, Z, Finset.sum_add_distrib, ← Finset.mul_sum] using hs
  have hforcing : (∫ x, b x * θ.value x ∂potentialMeasure d.potential) ≤
      B * ∫ x, |b x| ∂potentialMeasure d.potential := by
    have hp : ∀ᵐ x ∂potentialMeasure d.potential, b x * θ.value x ≤ B * |b x| := by
      filter_upwards [hbound] with x hx
      have hfb : |f.value x| ≤ B := by rwa [Real.norm_eq_abs] at hx
      have hχsq : χ x * χ x ≤ 1 := by obtain ⟨h0, h1⟩ := hχb x; nlinarith
      have ht : |θ.value x| ≤ B := by
        change |χ x * χ x * f.value x| ≤ B
        rw [abs_mul, abs_of_nonneg (mul_self_nonneg _)]
        exact (mul_le_mul hχsq hfb (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
      calc
        _ ≤ |b x * θ.value x| := le_abs_self _
        _ = |b x| * |θ.value x| := abs_mul _ _
        _ ≤ |b x| * B := mul_le_mul_of_nonneg_left ht (abs_nonneg _)
        _ = _ := mul_comm _ _
    have hle := integral_mono_ae hrhs (hb.abs.const_mul B) hp
    rwa [integral_const_mul] at hle
  have hZ : Z ≤ B ^ 2 * ∑ r, ∫ x, canonicalMetricDerivative d.potential χ r x ^ 2
      ∂potentialMeasure d.potential := by
    have hi (r : Fin n) : (∫ x, z r x ^ 2 ∂potentialMeasure d.potential) ≤
        B ^ 2 * ∫ x, canonicalMetricDerivative d.potential χ r x ^ 2 ∂potentialMeasure d.potential := by
      have hp : ∀ᵐ x ∂potentialMeasure d.potential,
          z r x ^ 2 ≤ B ^ 2 * canonicalMetricDerivative d.potential χ r x ^ 2 := by
        filter_upwards [hbound] with x hx
        have hs : f.value x ^ 2 ≤ B ^ 2 := by
          simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg (f.value x)) hx 2
        dsimp only [z]
        nlinarith only [mul_nonneg (sq_nonneg (canonicalMetricDerivative d.potential χ r x)) (sub_nonneg.mpr hs)]
      have hle := integral_mono_ae (hz r).integrable_sq
        ((d.metric_derivative_memLp hχ hc r).integrable_sq.const_mul (B ^ 2)) hp
      rwa [integral_const_mul] at hle
    have hs := Finset.sum_le_sum (s := Finset.univ) fun r _ => hi r
    simpa only [Z, Finset.mul_sum] using hs
  change E ≤ _
  nlinarith only [heq, hy, hforcing, hZ]

end KLSConstantImprovement.ActualBoundedWeakCaccioppoli405
#print axioms KLSConstantImprovement.ActualBoundedWeakCaccioppoli405.local_raw_metric_derivative_memLp
#print axioms KLSConstantImprovement.ActualBoundedWeakCaccioppoli405.metric_cutoff_square_product
#print axioms KLSConstantImprovement.ActualBoundedWeakCaccioppoli405.bounded_weak_caccioppoli
