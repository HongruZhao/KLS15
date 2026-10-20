import KLSConstantImprovement.ActualCompactRawH1Precompact405
import KLSConstantImprovement.ActualLocalCompactWeakTests405

/-! Actual cutoff localization of locally bounded raw-H1 families.  The
displayed weak product derivative and its global square bounds are proved
from local value/derivative estimates on the common cutoff support. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualLocalRawH1Precompact405
open KLS ActualCompactRawH1Precompact405 ActualLocalBoundedWeakAlgebra405
open ActualLocalCompactWeakTests405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem integral_square_eq_restrict_of_zero_off
    {g : Space n → ℝ} {E : Set (Space n)} (hE : MeasurableSet E)
    (hz : ∀ x, x ∉ E → g x = 0) :
    (∫ x, g x^2) = ∫ x in E, g x^2 := by
  rw [← integral_indicator hE]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      change g x^2 = 0
      rw [hz x hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

theorem cutoff_localRaw_uniform_precompact
    (f : ℕ → LocalRawTest n) {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχc : HasCompactSupport χ) {E : Set (Space n)} (hE : IsCompact E)
    (hχE : tsupport χ ⊆ E) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hv : ∀ k, (∫ x in E, (f k).value x ^ 2) ≤ A)
    (hd : ∀ k i, (∫ x in E, (f k).derivative i x ^ 2) ≤ B) :
    ∃ hf : ∀ k, MemLp (fun x => χ x*(f k).value x) 2 (volume : Measure (Space n)),
      TotallyBounded (range (fun k => (hf k).toLp (fun x => χ x*(f k).value x))) := by
  let q (k : ℕ) := cutoffLocalRawTest hχ (f k)
  have hqv (k : ℕ) (x : Space n) : (q k).value x = χ x*(f k).value x := rfl
  have hqD (k : ℕ) (i : Fin n) (x : Space n) : (q k).derivative i x =
      coordinateDerivative χ i x*(f k).value x + χ x*(f k).derivative i x := rfl
  have hqc (k : ℕ) : HasCompactSupport (q k).value := hχc.mul_right
  have hqDc (k : ℕ) (i : Fin n) : HasCompactSupport ((q k).derivative i) := by
    change HasCompactSupport (fun x => coordinateDerivative χ i x*(f k).value x +
      χ x*(f k).derivative i x)
    exact ((hasCompactSupport_coordinateDerivative hχc i).mul_right).add hχc.mul_right
  have hf (k : ℕ) : MemLp (q k).value 2 (volume : Measure (Space n)) :=
    memLp_compact_of_localL2 (q k).value_local (hqc k)
  have hD (k : ℕ) (i : Fin n) : MemLp ((q k).derivative i) 2 (volume : Measure (Space n)) :=
    memLp_compact_of_localL2 ((q k).derivative_local i) (hqDc k i)
  have hz (k : ℕ) (x : Space n) (hx : x ∉ E) : (q k).value x = 0 := by
    rw [hqv, image_eq_zero_of_notMem_tsupport (fun h => hx (hχE h)), zero_mul]
  have hzD (k : ℕ) (i : Fin n) (x : Space n) (hx : x ∉ E) : (q k).derivative i x = 0 := by
    have h0 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hχE h))
    have h1 : coordinateDerivative χ i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (hχE (tsupport_coordinateDerivative_subset χ i h)))
    rw [hqD, h0, h1]
    ring
  obtain ⟨C0, hC0⟩ := hχc.exists_bound_of_continuous hχ.continuous
  obtain ⟨C1, hC1⟩ := (hasCompactSupport_gradient hχc).exists_bound_of_continuous
    (continuous_gradient_of_contDiff hχ)
  have hC0n : 0 ≤ C0 := (norm_nonneg (χ 0)).trans (hC0 0)
  have hC1n : 0 ≤ C1 := (norm_nonneg (gradient χ 0)).trans (hC1 0)
  have hχsq (x : Space n) : χ x^2 ≤ C0^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg (χ x)) hC0n).mpr (hC0 x)
  have hDχsq (i : Fin n) (x : Space n) : coordinateDerivative χ i x^2 ≤ C1^2 := by
    have hb : ‖coordinateDerivative χ i x‖ ≤ C1 := by
      rw [coordinateDerivative_eq_gradient]
      exact (PiLp.norm_apply_le (gradient χ x) i).trans (hC1 x)
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg (coordinateDerivative χ i x)) hC1n).mpr hb
  have hv' (k : ℕ) : (∫ x, (q k).value x^2) ≤ C0^2*A := by
    rw [integral_square_eq_restrict_of_zero_off hE.measurableSet (hz k)]
    have hi : Integrable (fun x => (f k).value x^2) (volume.restrict E) :=
      ((f k).value_local E hE).integrable_sq
    calc
      _ ≤ ∫ x in E, C0^2*((f k).value x^2) :=
        integral_mono ((hf k).restrict E).integrable_sq (hi.const_mul _) (fun x => by
          rw [hqv, mul_pow]
          exact mul_le_mul_of_nonneg_right (hχsq x) (sq_nonneg _))
      _ = C0^2 * ∫ x in E, (f k).value x^2 := integral_const_mul _ _
      _ ≤ C0^2*A := mul_le_mul_of_nonneg_left (hv k) (sq_nonneg _)
  have hd' (k : ℕ) (i : Fin n) :
      (∫ x, (q k).derivative i x^2) ≤ 2*C1^2*A+2*C0^2*B := by
    rw [integral_square_eq_restrict_of_zero_off hE.measurableSet (hzD k i)]
    have hi : Integrable (fun x => (f k).value x^2) (volume.restrict E) :=
      ((f k).value_local E hE).integrable_sq
    have hdi : Integrable (fun x => (f k).derivative i x^2) (volume.restrict E) :=
      ((f k).derivative_local i E hE).integrable_sq
    have hp (x : Space n) : (q k).derivative i x^2 ≤
        (2*C1^2)*(f k).value x^2 + (2*C0^2)*(f k).derivative i x^2 := by
      have h1 := mul_le_mul_of_nonneg_right (hDχsq i x) (sq_nonneg ((f k).value x))
      have h2 := mul_le_mul_of_nonneg_right (hχsq x) (sq_nonneg ((f k).derivative i x))
      rw [hqD]
      nlinarith [sq_nonneg (coordinateDerivative χ i x*(f k).value x - χ x*(f k).derivative i x)]
    calc
      _ ≤ ∫ x in E, (2*C1^2)*(f k).value x^2 + (2*C0^2)*(f k).derivative i x^2 :=
        integral_mono ((hD k i).restrict E).integrable_sq
          ((hi.const_mul _).add (hdi.const_mul _)) hp
      _ = (2*C1^2)*(∫ x in E, (f k).value x^2) +
          (2*C0^2)*(∫ x in E, (f k).derivative i x^2) := by
        rw [integral_add (hi.const_mul _) (hdi.const_mul _), integral_const_mul, integral_const_mul]
      _ ≤ 2*C1^2*A+2*C0^2*B := add_le_add
        (mul_le_mul_of_nonneg_left (hv k) (by positivity))
        (mul_le_mul_of_nonneg_left (hd k i) (by positivity))
  obtain ⟨R, hR, hER⟩ := hE.isBounded.exists_pos_norm_le
  have hs (k : ℕ) : tsupport (q k).value ⊆ closedBall (0 : Space n) R := by
    apply (tsupport_mul_subset_left.trans hχE).trans
    intro x hx
    simpa only [mem_closedBall, dist_zero_right] using hER x hx
  refine ⟨hf, ?_⟩
  exact compact_raw_H1_totallyBounded hf hD (fun k => (q k).weak_derivative)
    (by positivity : 0 ≤ C0^2*A) (by positivity : 0 ≤ 2*C1^2*A+2*C0^2*B) hs hv' hd'

end KLSConstantImprovement.ActualLocalRawH1Precompact405
#print axioms KLSConstantImprovement.ActualLocalRawH1Precompact405.integral_square_eq_restrict_of_zero_off
#print axioms KLSConstantImprovement.ActualLocalRawH1Precompact405.cutoff_localRaw_uniform_precompact
