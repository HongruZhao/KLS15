import KLSConstantImprovement.ActualSourceRawHessianEvolution405
import KLSConstantImprovement.ActualSourceRawMetricPair405
import KLSConstantImprovement.ActualSourceMetricCutoffGradient405
import KLSConstantImprovement.ActualSourceCurvatureDomains405
import KLSConstantImprovement.ActualWeightedL2PairingContinuity

/-! Conservative global weak Hessian testing against a bounded genuine
finite-energy raw H1 function. The curvature is only L1, and its product
with the bounded test is integrable. Both boundary errors and the actual
weak gradient pairing are paid before passing to the global identity. -/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ContDiff Topology ENNReal
namespace KLSConstantImprovement.ActualSourceGlobalRawHessianEvolution405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCompactRawMetricGraph ActualBoundedRawMetricDomain
open ActualSourceHessianEvolution405 ActualSourceCurvatureDomains405
open ActualSourceRawHessianEvolution405 ActualSourceRawMetricPair405
open ActualSourceMetricCutoffGradient405 ActualWeightedL2PairingContinuity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_global_bounded_raw_hessian_evolution (d : SourceData μ)
    {f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hf : AEStronglyMeasurable f (potentialMeasure d.potential))
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B)
    (hFl : ∀ a E, IsCompact E → MemLp (F a) 2 (volume.restrict E))
    (hFw : ∀ a, HasLocalWeakCoordinateDerivative f (F a) a)
    (hFm : ∀ r, MemLp (rawCanonicalMetricDerivative d.potential F r) 2
      (potentialMeasure d.potential)) (i j : Fin n) :
    (∫ x, ∑ r,
      rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
        rawCanonicalMetricDerivative d.potential F r x ∂potentialMeasure d.potential) =
      ∫ x, (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        f x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let Hn (r : Fin n) := rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r
  let pair : Space n → ℝ := fun x => ∑ r, Hn r x * rawCanonicalMetricDerivative d.potential F r x
  let rhs : Space n → ℝ := fun x =>
    (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) * f x
  have hN (r : Fin n) : MemLp (Hn r) 2 (potentialMeasure d.potential) :=
    d.hessian_entry_raw_metric_memLp i j r
  have hpair : Integrable pair (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ (fun r _ => (hN r).integrable_mul (hFm r))
  have hfTop : MemLp f ∞ (potentialMeasure d.potential) :=
    memLp_top_of_bound hf B (Eventually.of_forall hB)
  have hf2 : MemLp f 2 (potentialMeasure d.potential) := hfTop.mono_exponent (by simp)
  have hfl (E : Set (Space n)) (hE : IsCompact E) : MemLp f 2 (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure hf2 d.source_C1.continuous hE
  have hrhs : Integrable rhs (potentialMeasure d.potential) := by
    have hHC := ((d.hessian_entry_memLp i j 1).integrable le_rfl).sub
      (actual_connection_curvature_entry_integrable d i j)
    exact (hHC.bdd_mul hf (Eventually.of_forall hB)).congr
      (Eventually.of_forall fun x => mul_comm _ _)
  obtain ⟨χ, hc, hpoint, hχm, hχlim⟩ :=
    exists_actual_cutoffs_with_vanishing_metric_gradient d
  have hχb (k : ℕ) : ∀ᵐ x ∂potentialMeasure d.potential, ‖χ k x‖ ≤ 1 :=
    Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((hc k).2.2 x).1]
      exact ((hc k).2.2 x).2
  have hχmeas (k : ℕ) : AEStronglyMeasurable (χ k) (potentialMeasure d.potential) :=
    (hc k).1.continuous.aestronglyMeasurable
  have hpχ := integral_mul_tendsto_of_ae_bounded_cutoffs hpair hχmeas hχb
    (Eventually.of_forall hpoint)
  have hrχ := integral_mul_tendsto_of_ae_bounded_cutoffs hrhs hχmeas hχb
    (Eventually.of_forall hpoint)
  let Fc (k : ℕ) := rawCutoffDerivative (χ k) f F
  have hFcl (k : ℕ) (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (Fc k a) 2 (volume.restrict E) :=
    (memLp_continuous_mul_on_compact hE (hFl a E hE) (hc k).1.continuous).add
      (memLp_continuous_mul_on_compact hE (hfl E hE)
        (contDiff_coordinateDerivative (hc k).1 (m := 0) (by norm_num) a).continuous)
  have hFcw (k : ℕ) (a : Fin n) :
      HasLocalWeakCoordinateDerivative (fun x => χ k x * f x) (Fc k a) a := by
    obtain ⟨W, hW, hWe⟩ := (hFw a).compact_mul hfl (hFl a) (hc k).1 (hc k).2.1
    apply (show HasLocalWeakCoordinateDerivative (fun x => χ k x * f x)
      (fun x => W x) a from hW).congr_ae EventuallyEq.rfl
    exact hWe
  have hB0 : 0 ≤ B := (norm_nonneg (f 0)).trans (hB 0)
  have htest (k : ℕ) := actual_compact_raw_hessian_evolution d (B := B)
    (fun E hE => memLp_continuous_mul_on_compact hE (hfl E hE) (hc k).1.continuous)
    (hc k).2.1.mul_right
    (Eventually.of_forall fun x => by
      rw [norm_mul]
      have hχnorm : ‖χ k x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg ((hc k).2.2 x).1]
        exact ((hc k).2.2 x).2
      exact (mul_le_mul hχnorm (hB x) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans
        (by simp))
    (hFcl k) (hFcw k) i j
  let err (k : ℕ) : ℝ := ∫ x, ∑ r,
    (f x * Hn r x) * canonicalMetricDerivative d.potential (χ k) r x
      ∂potentialMeasure d.potential
  have heInt (k : ℕ) (r : Fin n) : Integrable (fun x =>
      (f x * Hn r x) * canonicalMetricDerivative d.potential (χ k) r x)
      (potentialMeasure d.potential) := by
    have hfn : MemLp (fun x => f x * Hn r x) 2 (potentialMeasure d.potential) := hfTop.mul (hN r)
    exact hfn.integrable_mul (hχm k r)
  have herr : Tendsto err atTop (𝓝 0) := by
    have each (r : Fin n) : Tendsto (fun k => ∫ x,
        (f x * Hn r x) * canonicalMetricDerivative d.potential (χ k) r x
          ∂potentialMeasure d.potential) atTop (𝓝 0) := by
      have hfn : MemLp (fun x => f x * Hn r x) 2 (potentialMeasure d.potential) := hfTop.mul (hN r)
      have hlim := tendsto_integral_mul_of_weighted_L2 (fun _ => hfn) (fun k => hχm k r)
        hfn (MemLp.zero : MemLp (0 : Space n → ℝ) 2 (potentialMeasure d.potential))
        (by simp) (by simpa only [sub_zero] using hχlim r)
      simpa only [Pi.zero_apply, mul_zero, integral_zero] using hlim
    have hsum := tendsto_finsetSum Finset.univ (fun r _ => each r)
    have he (k : ℕ) : err k = ∑ r, ∫ x,
        (f x * Hn r x) * canonicalMetricDerivative d.potential (χ k) r x
          ∂potentialMeasure d.potential := integral_finsetSum Finset.univ (fun r _ => heInt k r)
    have herr_eq : err = fun k => ∑ r, ∫ x,
        (f x * Hn r x) * canonicalMetricDerivative d.potential (χ k) r x
          ∂potentialMeasure d.potential := funext he
    rw [herr_eq]
    simpa only [Finset.sum_const_zero] using hsum
  have hbalance (k : ℕ) : (∫ x, χ k x * pair x ∂potentialMeasure d.potential) + err k =
      ∫ x, χ k x * rhs x ∂potentialMeasure d.potential := by
    have hleft : (∑ a, ∫ x,
        ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j * Fc k a x
          ∂potentialMeasure d.potential) =
        (∫ x, χ k x * pair x ∂potentialMeasure d.potential) + err k := by
      rw [← integral_finsetSum Finset.univ (fun a _ => (htest k).1 a)]
      calc
        _ = ∫ x, ∑ r, Hn r x * rawCanonicalMetricDerivative d.potential (Fc k) r x
            ∂potentialMeasure d.potential :=
          integral_congr_ae (actual_hessian_flux_metric_pair_ae d (Fc k) i j)
        _ = _ := by
          rw [← integral_add (hpχ.1 k) (integrable_finsetSum Finset.univ (fun r _ => heInt k r))]
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            dsimp only [Fc, pair]
            simp only [rawCanonicalMetricDerivative_cutoff, mul_add, Finset.sum_add_distrib,
              Finset.mul_sum]
            congr 1 <;> apply Finset.sum_congr rfl <;> intro r _ <;> ring
    have hright : (∫ x, (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
        (χ k x * f x) ∂potentialMeasure d.potential) =
        -(∫ x, χ k x * rhs x ∂potentialMeasure d.potential) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [rhs]; ring
    have he := (htest k).2.2
    change -(∑ a, ∫ x,
      ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j * Fc k a x
        ∂potentialMeasure d.potential) =
      ∫ x, (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
        (χ k x * f x) ∂potentialMeasure d.potential at he
    rw [hleft, hright] at he
    linarith
  have hlim : Tendsto (fun k => ∫ x, χ k x * rhs x ∂potentialMeasure d.potential)
      atTop (𝓝 ((∫ x, pair x ∂potentialMeasure d.potential) + 0)) := by
    have ht := hpχ.2.add herr
    simpa only [hbalance] using ht
  simpa only [add_zero] using tendsto_nhds_unique hlim hrχ.2

end KLSConstantImprovement.ActualSourceGlobalRawHessianEvolution405
#print axioms KLSConstantImprovement.ActualSourceGlobalRawHessianEvolution405.actual_global_bounded_raw_hessian_evolution
