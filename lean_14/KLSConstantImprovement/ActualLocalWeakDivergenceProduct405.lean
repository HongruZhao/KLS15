import KLSConstantImprovement.ActualLocalCompactWeakTests405
import KLSConstantImprovement.ActualLocalDivergenceTests405
import KLS.WeakDivergenceMultiplier

/-! A locally bounded raw H1 multiplier obeys the actual weak divergence
product rule. No continuous representative or global metric domain is
assumed: the compact tests are the genuine cutoffs constructed earlier. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualLocalWeakDivergenceProduct405
open KLS ActualLocalBoundedWeakAlgebra405 ActualLocalCompactWeakTests405 ActualLocalDivergenceTests405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ}

theorem localRawTest_mul_locallyIntegrable (f : LocalRawTest n) {b : Space n → ℝ}
    (hb : LocallyIntegrable b volume) : LocallyIntegrable (fun x => f.value x * b x) volume := by
  apply locallyIntegrable_iff.mpr
  intro E hE
  letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
  have hbE : MemLp b 1 (volume.restrict E) :=
    memLp_one_iff_integrable.mpr (locallyIntegrable_iff.mp hb E hE)
  exact ((f.value_local_top E hE).mul hbE).integrable le_rfl

theorem divergence_mul_localRawTest
    {A : Fin n → Space n → ℝ} {b : Space n → ℝ}
    (hA : ∀ i E, IsCompact E → MemLp (A i) 2 (volume.restrict E))
    (hb : LocallyIntegrable b volume)
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∑ i, ∫ x, A i x * coordinateDerivative ψ i x) = ∫ x, b x * ψ x)
    (f : LocalRawTest n) {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∫ x, (f.value x * A i x) * coordinateDerivative ψ i x) =
      ∫ x, (f.value x * b x - ∑ i : Fin n, A i x * f.derivative i x) * ψ x := by
  let t := cutoffLocalRawTest hψ f
  have htc : HasCompactSupport t.value := hc.mul_right
  obtain ⟨C, hC⟩ := compact_localRawTest_bound t htc
  have hh := integral_divergence_of_C3_bounded_compact_H1_test hA hb hdiv
    t.value_local htc hC t.derivative_local t.weak_derivative
  have ha (i : Fin n) : Integrable (fun x => (A i x * f.derivative i x) * ψ x) :=
    integrable_mul_compact_of_locallyIntegrable
      (locallyIntegrable_product_of_localL2 (hA i) (f.derivative_local i)) hψ.continuous hc
  have hc' (i : Fin n) : Integrable (fun x => (f.value x * A i x) * coordinateDerivative ψ i x) :=
    integrable_mul_compact_of_locallyIntegrable
      (locallyIntegrable_of_memLp_two_on_compacts fun E hE => (f.value_local_top E hE).mul (hA i E hE))
      (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous
      (hasCompactSupport_coordinateDerivative hc i)
  have hb' : Integrable (fun x => (f.value x * b x) * ψ x) :=
    integrable_mul_compact_of_locallyIntegrable (localRawTest_mul_locallyIntegrable f hb) hψ.continuous hc
  have he (i : Fin n) : (∫ x, A i x * t.derivative i x) =
      (∫ x, (A i x * f.derivative i x) * ψ x) +
        ∫ x, (f.value x * A i x) * coordinateDerivative ψ i x := by
    rw [← integral_add (ha i) (hc' i)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change A i x * (coordinateDerivative ψ i x * f.value x + ψ x * f.derivative i x) = _
      ring
  have hr : (∫ x, b x * t.value x) = ∫ x, (f.value x * b x) * ψ x :=
    integral_congr_ae (Eventually.of_forall fun x => by change b x * (ψ x * f.value x) = _; ring)
  have hid := hh.2.2
  simp_rw [he] at hid
  rw [Finset.sum_add_distrib, hr] at hid
  have hsum : Integrable (fun x => (∑ i : Fin n, A i x * f.derivative i x) * ψ x) := by
    simpa only [Finset.sum_mul] using integrable_finsetSum Finset.univ (fun i _ => ha i)
  have hrhs : (∫ x, (f.value x * b x - ∑ i : Fin n, A i x * f.derivative i x) * ψ x) =
      (∫ x, (f.value x * b x) * ψ x) - ∑ i : Fin n, ∫ x, (A i x * f.derivative i x) * ψ x := by
    simp only [sub_mul, Finset.sum_mul]
    rw [integral_sub hb' (by simpa only [Finset.sum_mul] using hsum),
      integral_finsetSum Finset.univ (fun i _ => ha i)]
  rw [hrhs]
  linarith

end KLSConstantImprovement.ActualLocalWeakDivergenceProduct405

#print axioms KLSConstantImprovement.ActualLocalWeakDivergenceProduct405.localRawTest_mul_locallyIntegrable
#print axioms KLSConstantImprovement.ActualLocalWeakDivergenceProduct405.divergence_mul_localRawTest
