import KLSConstantImprovement.ActualSourceLocalWeakCalculus405
import KLS.WeightedResolventWeakEquation

/-!
The actual compact C1 product is an admissible test in the canonical
variational equation. Testing by chi^2 u gives the localized Caccioppoli
estimate with its literal cutoff error. This first-order estimate makes
no second-order or compact strong operator core claim.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceVariationalCaccioppoli405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualSourceLocalWeakCalculus405 ActualWeakCanonicalMetricInverse
open ActualCanonicalMetricResolvent
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem metric_derivative_square (φ χ : Space n → ℝ)
    (hχ : ContDiff ℝ 1 χ) (i : Fin n) (x : Space n) :
    canonicalMetricDerivative φ (fun y => χ y * χ y) i x =
      2 * χ x * canonicalMetricDerivative φ χ i x := by
  unfold canonicalMetricDerivative
  simp_rw [coordinateDerivative_mul (hχ.differentiable (by norm_num) x)
    (hχ.differentiable (by norm_num) x)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A localized energy estimate for each actual variational solution.
All tests and cutoff products are constructed from the actual form graph.
The error is kept as the literal u^2 Gamma(chi) integral. -/
theorem actual_variational_caccioppoli (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) (g : Lp ℝ 2 (potentialMeasure d.potential))
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hU : ∀ V : CanonicalMetricH1 d.potential,
      τ * inner ℝ (canonicalMetricValue d.potential U) (canonicalMetricValue d.potential V) +
        canonicalMetricEnergy d.potential U V =
          inner ℝ g (canonicalMetricValue d.potential V))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    (∑ i : Fin n, ∫ x, (χ x * canonicalMetricGradient d.potential i U x) ^ 2
      ∂potentialMeasure d.potential) ≤
      2 * |∫ x, g x * (χ x ^ 2 * canonicalMetricValue d.potential U x -
        ∫ y, χ y ^ 2 * canonicalMetricValue d.potential U y ∂potentialMeasure d.potential)
          ∂potentialMeasure d.potential| +
      4 * (∑ i : Fin n, ∫ x,
        (canonicalMetricDerivative d.potential χ i x * canonicalMetricValue d.potential U x) ^ 2
          ∂potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let u : Space n → ℝ := canonicalMetricValue d.potential U
  let a : Fin n → Space n → ℝ := fun i x => χ x * canonicalMetricGradient d.potential i U x
  let b : Fin n → Space n → ℝ := fun i x => canonicalMetricDerivative d.potential χ i x * u x
  have hχtop : MemLp χ ∞ (potentialMeasure d.potential) :=
    hχ.continuous.memLp_of_hasCompactSupport hc
  have hu : MemLp u 2 (potentialMeasure d.potential) := Lp.memLp _
  have ha (i : Fin n) : MemLp (a i) 2 (potentialMeasure d.potential) :=
    hχtop.mul (Lp.memLp _)
  have hb (i : Fin n) : MemLp (b i) 2 (potentialMeasure d.potential) :=
    (compact_metric_derivative_top d hχ hc i).mul hu
  have hab (i : Fin n) : Integrable (fun x => a i x * b i x) (potentialMeasure d.potential) :=
    (ha i).integrable_mul (hb i)
  let E : ℝ := ∑ i : Fin n, ∫ x, a i x ^ 2 ∂potentialMeasure d.potential
  let B : ℝ := ∑ i : Fin n, ∫ x, b i x ^ 2 ∂potentialMeasure d.potential
  let C : ℝ := ∑ i : Fin n, ∫ x, a i x * b i x ∂potentialMeasure d.potential
  obtain ⟨V, hv, hd⟩ := exists_metricH1_compact_mul d U (hχ.mul hχ) hc.mul_right
  have hχu2 : MemLp (fun x => χ x * χ x * u x) 2 (potentialMeasure d.potential) :=
    by
      have hχsq : MemLp (fun x => χ x * χ x) ∞ (potentialMeasure d.potential) := hχtop.mul hχtop
      exact hχsq.mul hu
  have hmass : inner ℝ (canonicalMetricValue d.potential U) (canonicalMetricValue d.potential V) =
      ∫ x, (χ x * u x) ^ 2 ∂potentialMeasure d.potential := by
    rw [weighted_inner_centered_test hχu2 hv,
      canonicalMetricValue_integral_eq_zero d.source_C1.continuous U, zero_mul, sub_zero]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp [u]; ring
  have henergy : canonicalMetricEnergy d.potential U V = E + 2 * C := by
    rw [canonicalMetricEnergy_apply]
    have hi (i : Fin n) : inner ℝ (canonicalMetricGradient d.potential i U)
        (canonicalMetricGradient d.potential i V) =
        (∫ x, a i x ^ 2 ∂potentialMeasure d.potential) +
          2 * (∫ x, a i x * b i x ∂potentialMeasure d.potential) := by
      rw [L2.inner_def]
      calc
        _ = ∫ x, a i x ^ 2 + 2 * (a i x * b i x) ∂potentialMeasure d.potential := by
          apply integral_congr_ae
          filter_upwards [hd i] with x hx
          simp only [RCLike.inner_apply, conj_trivial, hx,
            metric_derivative_square d.potential χ hχ i x]
          dsimp [a, b, u]
          ring
        _ = _ := by rw [integral_add (ha i).integrable_sq ((hab i).const_mul 2),
          integral_const_mul]
    simp_rw [hi]
    simp only [E, C, Finset.sum_add_distrib, Finset.mul_sum]
  have hforcing : inner ℝ g (canonicalMetricValue d.potential V) =
      ∫ x, g x * (χ x ^ 2 * u x -
        ∫ y, χ y ^ 2 * u y ∂potentialMeasure d.potential) ∂potentialMeasure d.potential := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    simp only [RCLike.inner_apply, conj_trivial, hx, pow_two]
    ring
  have hyi (i : Fin n) :
      -4 * (∫ x, a i x * b i x ∂potentialMeasure d.potential) ≤
      (∫ x, a i x ^ 2 ∂potentialMeasure d.potential) +
        4 * (∫ x, b i x ^ 2 ∂potentialMeasure d.potential) := by
    calc
      _ = ∫ x, -4 * (a i x * b i x) ∂potentialMeasure d.potential :=
        (integral_const_mul _ _).symm
      _ ≤ ∫ x, a i x ^ 2 + 4 * b i x ^ 2 ∂potentialMeasure d.potential := by
        apply integral_mono ((hab i).const_mul (-4))
          ((ha i).integrable_sq.add ((hb i).integrable_sq.const_mul 4))
        intro x
        change -4 * (a i x * b i x) ≤ a i x ^ 2 + 4 * b i x ^ 2
        nlinarith [sq_nonneg (a i x + 2 * b i x)]
      _ = _ := by rw [integral_add (ha i).integrable_sq ((hb i).integrable_sq.const_mul 4),
        integral_const_mul]
  have hy : -4 * C ≤ E + 4 * B := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hyi i)
    simpa only [E, B, C, Finset.sum_add_distrib, ← Finset.mul_sum] using hs
  have hm : 0 ≤ τ * (∫ x, (χ x * u x) ^ 2 ∂potentialMeasure d.potential) :=
    mul_nonneg hτ (integral_nonneg fun x => sq_nonneg _)
  have he := hU V
  rw [hmass, henergy, hforcing] at he
  have hf := le_abs_self (∫ x, g x * (χ x ^ 2 * u x -
    ∫ y, χ y ^ 2 * u y ∂potentialMeasure d.potential) ∂potentialMeasure d.potential)
  change E ≤ _
  nlinarith

theorem actual_inverse_caccioppoli (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    (∑ i : Fin n, ∫ x, (χ x * canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x) ^ 2
      ∂potentialMeasure d.potential) ≤
      2 * |∫ x, g x * (χ x ^ 2 * sourceMetricInverse d g x -
        ∫ y, χ y ^ 2 * sourceMetricInverse d g y ∂potentialMeasure d.potential)
          ∂potentialMeasure d.potential| +
      4 * (∑ i : Fin n, ∫ x,
        (canonicalMetricDerivative d.potential χ i x * sourceMetricInverse d g x) ^ 2
          ∂potentialMeasure d.potential) := by
  apply actual_variational_caccioppoli d (sourceMetricInverseH1 d g) g (τ := 0) (by norm_num)
  · intro V
    simpa only [zero_mul, zero_add] using sourceMetricInverse_variational d g V
  · exact hχ
  · exact hc

theorem actual_unit_resolvent_caccioppoli (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    (∑ i : Fin n, ∫ x, (χ x * canonicalMetricGradient d.potential i
        (canonicalResolventH1 d.potential (t := 1) zero_lt_one g) x) ^ 2 ∂potentialMeasure d.potential) ≤
      2 * |∫ x, g x * (χ x ^ 2 * canonicalResolvent d.potential (t := 1) zero_lt_one g x -
        ∫ y, χ y ^ 2 * canonicalResolvent d.potential (t := 1) zero_lt_one g y
          ∂potentialMeasure d.potential) ∂potentialMeasure d.potential| +
      4 * (∑ i : Fin n, ∫ x, (canonicalMetricDerivative d.potential χ i x *
        canonicalResolvent d.potential (t := 1) zero_lt_one g x) ^ 2 ∂potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  apply actual_variational_caccioppoli d
    (canonicalResolventH1 d.potential (t := 1) zero_lt_one g) g (τ := 1) (by norm_num)
  · intro V
    simpa only [one_mul, canonicalResolvent, ContinuousLinearMap.comp_apply] using
      canonicalResolvent_variational d.potential (t := 1) zero_lt_one g V
  · exact hχ
  · exact hc

end KLSConstantImprovement.ActualSourceVariationalCaccioppoli405
#print axioms KLSConstantImprovement.ActualSourceVariationalCaccioppoli405.metric_derivative_square
#print axioms KLSConstantImprovement.ActualSourceVariationalCaccioppoli405.actual_variational_caccioppoli
#print axioms KLSConstantImprovement.ActualSourceVariationalCaccioppoli405.actual_inverse_caccioppoli
#print axioms KLSConstantImprovement.ActualSourceVariationalCaccioppoli405.actual_unit_resolvent_caccioppoli
