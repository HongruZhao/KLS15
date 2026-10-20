import KLSConstantImprovement.ActualConvexSoftBarrier405
import KLS.WeightedIntegrationByParts

/-! Genuine growing-ball soft-barrier integrals.  Domination is required only
under the fixed global density exp(-V); this covers bounded continuous tests
and all polynomial moments for a strongly convex V.  It does not assert the
false convergence of every unbounded continuous observable. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualSoftTargetIntegrals405
open KLS ActualConvexSoftBarrier405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

def softTargetPotential (V : Space n → ℝ) (K : Set (Space n)) (j : ℕ) : Space n → ℝ :=
  fun x => V x + convexSoftBarrier K j x

def softTargetWeight (K : Set (Space n)) (j : ℕ) : Space n → ℝ :=
  (ball (0 : Space n) ((j : ℝ)+1)).indicator
    (fun x => Real.exp (-convexSoftBarrier K j x))

def rawSoftTargetMeasure (V : Space n → ℝ) (K : Set (Space n)) (j : ℕ) : Measure (Space n) :=
  (potentialMeasure (softTargetPotential V K j)).restrict (ball 0 ((j : ℝ)+1))

theorem softTargetWeight_measurable (K : Set (Space n)) (j : ℕ) :
    Measurable (softTargetWeight K j) :=
  ((convexSoftBarrier_smooth K j).continuous.measurable.neg.exp).indicator isOpen_ball.measurableSet

theorem softTargetWeight_bounds (K : Set (Space n)) (j : ℕ) (x : Space n) :
    0 ≤ softTargetWeight K j x ∧ softTargetWeight K j x ≤ 1 := by
  by_cases hx : x ∈ ball (0 : Space n) ((j : ℝ)+1)
  · simp only [softTargetWeight, indicator_of_mem hx]
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (convexSoftBarrier_nonneg K j x))⟩
  · simp only [softTargetWeight, indicator_of_notMem hx]
    norm_num

theorem softTargetWeight_tendsto (K : Set (Space n)) (hK : IsClosed K)
    (hne : K.Nonempty) (x : Space n) :
    Tendsto (fun j => softTargetWeight K j x) atTop
      (𝓝 (K.indicator (fun _ => (1 : ℝ)) x)) := by
  have hev : ∀ᶠ j : ℕ in atTop, x ∈ ball (0 : Space n) ((j : ℝ)+1) := by
    have hh : Tendsto (fun j : ℕ => (j : ℝ)+1) atTop atTop :=
      tendsto_atTop_mono (fun j : ℕ => le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
        tendsto_natCast_atTop_atTop
    filter_upwards [hh.eventually (eventually_gt_atTop ‖x‖)] with j hj
    simpa only [mem_ball, dist_zero_right] using hj
  apply (convexSoftBarrier_exp_tendsto K hK hne x).congr'
  filter_upwards [hev] with j hj
  simp only [softTargetWeight, indicator_of_mem hj]

theorem rawSoftTargetMeasure_integral {V : Space n → ℝ} (hV : Measurable V)
    (K : Set (Space n)) (j : ℕ) (f : Space n → ℝ) :
    (∫ x, f x ∂rawSoftTargetMeasure V K j) =
      ∫ x, f x * softTargetWeight K j x ∂potentialMeasure V := by
  have hW : Measurable (softTargetPotential V K j) :=
    hV.add (convexSoftBarrier_smooth K j).continuous.measurable
  unfold rawSoftTargetMeasure
  rw [← integral_indicator isOpen_ball.measurableSet]
  rw [integral_potentialMeasure hW,
    integral_potentialMeasure hV]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ ball (0 : Space n) ((j : ℝ)+1)
    · simp only [indicator_of_mem hx, softTargetWeight, softTargetPotential,
        neg_add, Real.exp_add]
      ring
    · simp only [indicator_of_notMem hx, softTargetWeight, zero_mul, mul_zero]

theorem integrable_rawSoftTargetMeasure {V : Space n → ℝ} (hV : Measurable V)
    (K : Set (Space n)) (j : ℕ) {f : Space n → ℝ}
    (hf : Integrable f (potentialMeasure V)) :
    Integrable f (rawSoftTargetMeasure V K j) := by
  have hw : Integrable (fun x => f x * softTargetWeight K j x) (potentialMeasure V) :=
    hf.mul_bdd (softTargetWeight_measurable K j).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (softTargetWeight_bounds K j x).1] using
          (softTargetWeight_bounds K j x).2)
  have hW : Measurable (softTargetPotential V K j) :=
    hV.add (convexSoftBarrier_smooth K j).continuous.measurable
  change IntegrableOn f (ball (0 : Space n) ((j : ℝ)+1))
    (potentialMeasure (softTargetPotential V K j))
  rw [← integrable_indicator_iff isOpen_ball.measurableSet,
    integrable_potentialMeasure_iff hW]
  rw [integrable_potentialMeasure_iff hV] at hw
  convert hw using 1
  funext x
  by_cases hx : x ∈ ball (0 : Space n) ((j : ℝ)+1)
  · simp only [indicator_of_mem hx, softTargetWeight, softTargetPotential, neg_add, Real.exp_add]
    ring
  · simp only [indicator_of_notMem hx, softTargetWeight, zero_mul, mul_zero]

theorem tendsto_rawSoftTargetMeasure_integral {V : Space n → ℝ} (hV : Measurable V)
    (K : Set (Space n)) (hK : IsClosed K) (hne : K.Nonempty)
    {f : Space n → ℝ} (hf : Integrable f (potentialMeasure V)) :
    Tendsto (fun j => ∫ x, f x ∂rawSoftTargetMeasure V K j) atTop
      (𝓝 (∫ x, f x ∂(potentialMeasure V).restrict K)) := by
  have hh : Tendsto (fun j => ∫ x, f x * softTargetWeight K j x ∂potentialMeasure V) atTop
      (𝓝 (∫ x, f x * K.indicator (fun _ => (1 : ℝ)) x ∂potentialMeasure V)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    · intro j
      exact hf.aestronglyMeasurable.mul (softTargetWeight_measurable K j).aestronglyMeasurable
    · exact hf.norm
    · intro j
      exact Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs (softTargetWeight K j x),
          abs_of_nonneg (softTargetWeight_bounds K j x).1]
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (softTargetWeight_bounds K j x).2 (norm_nonneg (f x))
    · exact Eventually.of_forall fun x =>
        (softTargetWeight_tendsto K hK hne x).const_mul (f x)
  have ht : (∫ x, f x * K.indicator (fun _ => (1 : ℝ)) x ∂potentialMeasure V) =
      ∫ x, f x ∂(potentialMeasure V).restrict K := by
    rw [← integral_indicator hK.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · simp only [indicator_of_mem hx, mul_one]
      · simp only [indicator_of_notMem hx, mul_zero]
  simpa only [← rawSoftTargetMeasure_integral hV K, ht] using hh

end KLSConstantImprovement.ActualSoftTargetIntegrals405
#print axioms KLSConstantImprovement.ActualSoftTargetIntegrals405.softTargetWeight_bounds
#print axioms KLSConstantImprovement.ActualSoftTargetIntegrals405.softTargetWeight_tendsto
#print axioms KLSConstantImprovement.ActualSoftTargetIntegrals405.rawSoftTargetMeasure_integral
#print axioms KLSConstantImprovement.ActualSoftTargetIntegrals405.integrable_rawSoftTargetMeasure
#print axioms KLSConstantImprovement.ActualSoftTargetIntegrals405.tendsto_rawSoftTargetMeasure_integral
