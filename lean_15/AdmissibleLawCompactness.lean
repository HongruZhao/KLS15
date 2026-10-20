import WeakMomentContinuity
import KLS.ThirdCumulant

/-! Compactness of the literal fixed-dimensional admissible probability laws.
No density, regularity, or maximizer assumption is introduced. Uniform moments
from the released full compact-set class preserve the isotropy identities. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem memLp_two_of_norm_pow_bound {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : Continuous f) (p : ℕ)
    (hb : ∀ x, ‖f x‖ ≤ ‖x‖^p) : MemLp f 2 μ :=
  (hLC.memLp_two_norm_pow p).mono' hf.aestronglyMeasurable (Eventually.of_forall hb)

 theorem integral_sq_le_norm_pow {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : Continuous f) (p : ℕ)
    (hb : ∀ x, ‖f x‖ ≤ ‖x‖^p) :
    (∫ x, f x^2 ∂μ) ≤ ∫ x, ‖x‖^(p*2) ∂μ := by
  apply integral_mono
    ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp
      (memLp_two_of_norm_pow_bound hLC hf p hb)) (hLC.integrable_norm_pow _)
  intro x
  have h := pow_le_pow_left₀ (norm_nonneg (f x)) (hb x) 2
  simpa only [Real.norm_eq_abs,sq_abs,← pow_mul] using h

/-- Weak convergence of genuine admissible laws preserves every continuous
observable bounded by a fixed power of the norm. -/
 theorem tendsto_integral_norm_pow_bounded_observable
    {n : ℕ} {ι : Type*} {l : Filter ι} [NeBot l]
    {ν : ι → ProbabilityMeasure (Space n)} {μ : ProbabilityMeasure (Space n)}
    (hlim : Tendsto ν l (𝓝 μ))
    (hν : ∀ i, admissibleMeasure (ν i : Measure (Space n)))
    {f : Space n → ℝ} (hf : Continuous f) (p : ℕ)
    (hb : ∀ x, ‖f x‖ ≤ ‖x‖^p) :
    Tendsto (fun i => ∫ x, f x ∂(ν i : Measure (Space n))) l
      (𝓝 (∫ x, f x ∂(μ : Measure (Space n)))) := by
  have hLC := measureLogConcave_of_probability_tendsto hlim
    (Eventually.of_forall fun i => (hν i).logConcave)
  apply tendsto_integral_of_uniform_sq_moment hlim hf
    (memLp_two_of_norm_pow_bound hLC hf p hb)
    (fun i => memLp_two_of_norm_pow_bound (hν i).logConcave hf p hb)
    ((isotropicTailRadius n)^(p*2)*geometricNormMomentConstant (p*2))
  exact Eventually.of_forall fun i =>
    (integral_sq_le_norm_pow (hν i).logConcave hf p hb).trans
      ((hν i).logConcave.isotropic_integral_norm_pow_le (hν i).isotropic _)

 theorem admissibleMeasure_of_probability_tendsto
    {n : ℕ} {ι : Type*} {l : Filter ι} [NeBot l]
    {ν : ι → ProbabilityMeasure (Space n)} {μ : ProbabilityMeasure (Space n)}
    (hlim : Tendsto ν l (𝓝 μ))
    (hν : ∀ i, admissibleMeasure (ν i : Measure (Space n))) :
    admissibleMeasure (μ : Measure (Space n)) := by
  have hLC := measureLogConcave_of_probability_tendsto hlim
    (Eventually.of_forall fun i => (hν i).logConcave)
  have hc (j : Fin n) : Continuous (fun x : Space n => x j) := by fun_prop
  have hcb (j : Fin n) (x : Space n) : ‖x j‖ ≤ ‖x‖^1 := by
    simpa only [pow_one] using PiLp.norm_apply_le x j
  have hL2 (j : Fin n) := memLp_two_of_norm_pow_bound hLC (hc j) 1 (hcb j)
  have hmean (j : Fin n) : (∫ x, x j ∂(μ : Measure (Space n))) = 0 := by
    have ht := tendsto_integral_norm_pow_bounded_observable hlim hν (hc j) 1 (hcb j)
    have he : (fun i => ∫ x, x j ∂(ν i : Measure (Space n))) = fun _ => (0 : ℝ) :=
      funext fun i => (hν i).isotropic.integral_coordinate j
    rw [he] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hsecond (j k : Fin n) :
      (∫ x, x j*x k ∂(μ : Measure (Space n))) = if j=k then 1 else 0 := by
    have hb (x : Space n) : ‖x j*x k‖ ≤ ‖x‖^2 := by
      rw [norm_mul,pow_two]
      exact mul_le_mul (PiLp.norm_apply_le x j) (PiLp.norm_apply_le x k)
        (norm_nonneg _) (norm_nonneg _)
    have ht := tendsto_integral_norm_pow_bounded_observable hlim hν
      (by fun_prop : Continuous (fun x : Space n => x j*x k)) 2 hb
    have he : (fun i => ∫ x, x j*x k ∂(ν i : Measure (Space n))) =
        fun _ => (if j=k then (1 : ℝ) else 0) :=
      funext fun i => (hν i).isotropic.integral_coordinate_mul j k
    rw [he] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hm : MemLp (fun x : Space n => x) 2 (μ : Measure (Space n)) :=
    MemLp.of_eval_piLp hL2
  have hi := hm.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨inferInstance,hLC,hi,?_,fun j k => (hL2 j).integrable_mul (hL2 k),?_⟩
  · ext j
    have he := (EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm hi
    change (∫ x : Space n, x j ∂(μ : Measure (Space n))) =
      (∫ x : Space n, x ∂(μ : Measure (Space n))) j at he
    rw [← he,hmean]
    rfl
  · ext j k
    change (∫ x, x j*x k ∂(μ : Measure (Space n))) = _
    rw [hsecond]
    rfl

 theorem isClosed_admissible_probability_laws (n : ℕ) :
    IsClosed (admissibleProbabilityLaws n) := by
  apply IsSeqClosed.isClosed
  intro ν μ hν hlim
  exact admissibleMeasure_of_probability_tendsto hlim hν

/-- The exact fixed-dimensional admissible-law class is weakly compact. -/
 theorem isCompact_admissible_probability_laws (n : ℕ) :
    IsCompact (admissibleProbabilityLaws n) := by
  simpa only [(isClosed_admissible_probability_laws n).closure_eq] using
    (admissible_probability_laws_compact_closure (n := n))

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.admissibleMeasure_of_probability_tendsto
#print axioms KLS.DeterministicBridgeNext.isCompact_admissible_probability_laws
