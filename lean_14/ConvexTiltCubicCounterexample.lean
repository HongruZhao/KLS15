import ConvexTiltScalarLaw
import ScalarCovarianceCubicIntegral

/-! Actual log-concave probability laws disprove global nonincreasing
behavior of the covariance-normalized scalar cubic cap under convex tilts.
This theorem does not disprove universal cap six or Poincare four. -/
noncomputable section
open MeasureTheory Set
namespace KLSImprovement.ConvexTiltCounterexample
open KLS (Space measureLogConcave)
open KLSImprovement.ConvexTiltLaw KLSImprovement.ConvexTiltAlgebra
open KLSImprovement.ScalarCovarianceCubic
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

theorem exponential_parameter_positive : 0<Real.exp (-9:ℝ) := Real.exp_pos _
theorem exponential_parameter_lt_one : Real.exp (-9:ℝ)<1 := by
  exact Real.exp_lt_one_iff.mpr (by norm_num)

theorem raw_zero_actual (k : ℕ) : raw (law 0) k=rawZero k := by
  rw [raw,coordinate_moment (by norm_num : (0:ℝ)≤0) k,
    KLSImprovement.TruncatedExponential.moment_at_zero,
    KLSImprovement.TruncatedExponential.moment_at_zero]
  norm_num only [Nat.cast_one,zero_add,one_div,inv_one]
  rfl

theorem raw_nine_actual (k : ℕ) (hk : k≤6) :
    raw (law 9) k=rawNine (Real.exp (-9)) k := by
  rw [raw,coordinate_moment (by norm_num : (0:ℝ)≤9) k,
    KLSImprovement.TruncatedExponential.moment_eq_value 9 (by norm_num) k,
    KLSImprovement.TruncatedExponential.moment_eq_value 9 (by norm_num) 0]
  have hn : Real.exp (-9:ℝ)-10≠0 := by
    have h := exponential_parameter_lt_one
    linarith
  have hn' : 10-Real.exp (-9:ℝ)≠0 := by
    have h := exponential_parameter_lt_one
    linarith
  have hden : 1+KLSImprovement.TruncatedExponential.value 9 (Real.exp (-9)) 0=
      (10-Real.exp (-9))/9 := by
    simp only [KLSImprovement.TruncatedExponential.value]
    ring
  rw [hden]
  interval_cases k <;>
    norm_num only [KLSImprovement.TruncatedExponential.value,rawNine] <;>
    field_simp [hn,hn'] <;> ring

theorem cap_zero_actual : actualCap (law 0)=24166423/5210695 := by
  letI : IsProbabilityMeasure (law 0) := law_isProbability (by norm_num)
  rw [actualCap_eq_momentCap _
    (fun k _ => coordinate_power_integrable (by norm_num : (0:ℝ)≤0) k)]
  have he : raw (law 0)=rawZero := funext raw_zero_actual
  rw [he,cap_zero_exact]

theorem cap_nine_actual :
    actualCap (law 9)=cap (rawNine (Real.exp (-9))) := by
  letI : IsProbabilityMeasure (law 9) := law_isProbability (by norm_num)
  rw [actualCap_eq_momentCap _
    (fun k _ => coordinate_power_integrable (by norm_num : (0:ℝ)≤9) k)]
  unfold cap variance centralThree centralFour centralSix
  rw [raw_nine_actual 1 (by norm_num),raw_nine_actual 2 (by norm_num),
    raw_nine_actual 3 (by norm_num),raw_nine_actual 4 (by norm_num),
    raw_nine_actual 5 (by norm_num),raw_nine_actual 6 (by norm_num)]

theorem variance_zero_actual : variance (raw (law 0))=53/48 := by
  rw [show raw (law 0)=rawZero from funext raw_zero_actual]
  norm_num [variance,rawZero]

theorem variance_nine_actual_positive : 0<variance (raw (law 9)) := by
  unfold variance
  rw [raw_nine_actual 1 (by norm_num),raw_nine_actual 2 (by norm_num)]
  exact variance_nine_positive exponential_parameter_lt_one

theorem actual_convex_tilt_strictly_increases_cubic_cap :
    actualCap (law 0)<actualCap (law 9) := by
  rw [cap_zero_actual,cap_nine_actual,←cap_zero_exact]
  exact strict_cap_increase exponential_parameter_positive.le exponential_parameter_lt_one

/-- A single actual log-concave probability and a further continuous
concave exponential weight violate the proposed global monotonicity. -/
theorem actual_global_monotonicity_counterexample :
    ∃ (μ : Measure (Space 1)) (q : Space 1 → ℝ),
      IsProbabilityMeasure μ ∧ measureLogConcave μ ∧ Continuous q ∧
      ConcaveOn ℝ univ q ∧ IsProbabilityMeasure (μ.tilted q) ∧
      measureLogConcave (μ.tilted q) ∧
      0<variance (raw μ) ∧ 0<variance (raw (μ.tilted q)) ∧
      actualCap μ<actualCap (μ.tilted q) := by
  refine ⟨law 0,(fun x => 9*min (x 0) 0),
    law_isProbability (by norm_num),law_logConcave (by norm_num),?_,?_,?_,?_,?_,?_,?_⟩
  · fun_prop
  · convert potential_concave (by norm_num : (0:ℝ)≤8) using 1
    funext x
    norm_num [potential]
  · rw [law_nine_is_further_convex_tilt]
    exact law_isProbability (by norm_num)
  · rw [law_nine_is_further_convex_tilt]
    exact law_logConcave (by norm_num)
  · rw [variance_zero_actual]
    norm_num
  · rw [law_nine_is_further_convex_tilt]
    exact variance_nine_actual_positive
  · rw [law_nine_is_further_convex_tilt]
    exact actual_convex_tilt_strictly_increases_cubic_cap

end KLSImprovement.ConvexTiltCounterexample
#print axioms KLSImprovement.ConvexTiltCounterexample.raw_zero_actual
#print axioms KLSImprovement.ConvexTiltCounterexample.raw_nine_actual
#print axioms KLSImprovement.ConvexTiltCounterexample.cap_zero_actual
#print axioms KLSImprovement.ConvexTiltCounterexample.variance_nine_actual_positive
#print axioms KLSImprovement.ConvexTiltCounterexample.actual_convex_tilt_strictly_increases_cubic_cap
#print axioms KLSImprovement.ConvexTiltCounterexample.actual_global_monotonicity_counterexample
