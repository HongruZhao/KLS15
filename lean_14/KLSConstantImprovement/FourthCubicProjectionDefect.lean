import ActualFourthCumulantSpectralDefect
import KLSConstantImprovement.MixedCubicRankSlicing

/-! An unconditional fourth-cumulant budget for one complete cubic test.
The signed pairing is retained before symmetrizing the output. This is an
input to the mixed-cubic research, not a proof of the mixed 1/26 estimate. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLSConstantImprovement.FourthCubicProjectionDefect
open KLS KLS.DeterministicBridgeIntegration MixedCubicRankSlicing
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]

def pairing (T U : ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, T i j k * U i j k

/-- Cyclic averaging is full symmetrization when the final two input
indices are already symmetric. -/
def cyclicAverage (U : ι → ι → ι → ℝ) : ι → ι → ι → ℝ :=
  fun i j k => (U i j k + U j k i + U k i j) / 3

private theorem sum_cyclic (f : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, f j k i) = ∑ i, ∑ j, ∑ k, f i j k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

theorem cubicEnergy_nonneg (T : ι → ι → ι → ℝ) : 0 ≤ cubicEnergy T := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => sq_nonneg (T i j k)

theorem cubicEnergy_sub_mul (U T : ι → ι → ι → ℝ) (a : ℝ) :
    cubicEnergy (fun i j k => U i j k - a * T i j k) =
      cubicEnergy U - 2*a*pairing T U + a^2*cubicEnergy T := by
  simp only [cubicEnergy, pairing, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem cyclicAverage_energy_le (U : ι → ι → ι → ℝ) :
    cubicEnergy (cyclicAverage U) ≤ cubicEnergy U := by
  have h (i j k : ι) :
      ((U i j k + U j k i + U k i j) / 3)^2 ≤
        ((U i j k)^2 + (U j k i)^2 + (U k i j)^2) / 3 := by
    nlinarith [sq_nonneg (U i j k - U j k i),
      sq_nonneg (U j k i - U k i j), sq_nonneg (U k i j - U i j k)]
  have hh : (∑ i, ∑ j, ∑ k, ((U i j k + U j k i + U k i j) / 3)^2) ≤
      ∑ i, ∑ j, ∑ k, ((U i j k)^2 + (U j k i)^2 + (U k i j)^2) / 3 :=
    Finset.sum_le_sum fun (i : ι) _ =>
      Finset.sum_le_sum fun (j : ι) _ => Finset.sum_le_sum fun (k : ι) _ => h i j k
  have h1 := sum_cyclic (fun i j k => (U i j k)^2)
  have h2 := (sum_cyclic (fun i j k => (U j k i)^2)).trans h1
  simp only [← Finset.sum_div, Finset.sum_add_distrib, h1, h2] at hh
  unfold cubicEnergy cyclicAverage
  linarith

theorem pairing_cyclicAverage (T U : ι → ι → ι → ℝ)
    (hT : ∀ i j k, T i j k = T j k i) :
    pairing T (cyclicAverage U) = pairing T U := by
  have h1 : (∑ i, ∑ j, ∑ k, T i j k * U j k i) = pairing T U := by
    calc
      _ = ∑ i, ∑ j, ∑ k, T j k i * U j k i := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [hT i j k]
      _ = pairing T U := sum_cyclic (fun i j k => T i j k * U i j k)
  have h2 : (∑ i, ∑ j, ∑ k, T i j k * U k i j) = pairing T U := by
    calc
      _ = ∑ i, ∑ j, ∑ k, T k i j * U k i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [hT i j k, hT j k i]
      _ = pairing T U :=
        (sum_cyclic (fun i j k => T j k i * U j k i)).trans
          (sum_cyclic (fun i j k => T i j k * U i j k))
  unfold pairing cyclicAverage
  simp only [mul_div, mul_add, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [h1, h2]
  unfold pairing
  ring

variable {n : ℕ}

def rawFourthAction (μ : Measure (Space n))
    (T : Fin n → Fin n → Fin n → ℝ) : Fin n → Fin n → Fin n → ℝ :=
  fun i j k => actualFourthCumulantFlat μ (T i) j k

def fourthAction (μ : Measure (Space n))
    (T : Fin n → Fin n → Fin n → ℝ) : Fin n → Fin n → Fin n → ℝ :=
  cyclicAverage (rawFourthAction μ T)

def upperDefect (μ : Measure (Space n))
    (T : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  6 * cubicEnergy T - pairing T (rawFourthAction μ T)

theorem actual_rawFourth_energy_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Fin n → Fin n → Fin n → ℝ) :
    cubicEnergy (rawFourthAction μ T) ≤
      4 * pairing T (rawFourthAction μ T) + 12 * cubicEnergy T := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin n) _ =>
    actual_fourth_cumulant_flat_square_le_signed_pairing hμ (T i)
  simpa only [cubicEnergy, pairing, rawFourthAction, matrixFrobeniusSq,
    Finset.sum_add_distrib, ← Finset.mul_sum] using h

theorem actual_fourthAction_energy_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Fin n → Fin n → Fin n → ℝ) :
    cubicEnergy (fourthAction μ T) ≤
      36 * cubicEnergy T - 4 * upperDefect μ T := by
  have hc := cyclicAverage_energy_le (rawFourthAction μ T)
  have hb := actual_rawFourth_energy_le hμ T
  unfold fourthAction upperDefect
  linarith

theorem actual_fourthAction_pairing
    (μ : Measure (Space n)) (T : Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ i j k, T i j k = T j k i) :
    pairing T (fourthAction μ T) = 6 * cubicEnergy T - upperDefect μ T := by
  rw [fourthAction, pairing_cyclicAverage T _ hT]
  unfold upperDefect
  ring

/-- Division-free bound for the component perpendicular to the input cubic.
No unproved mixed-cubic assumption is present. -/
theorem actual_fourthAction_transverse_budget
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ i j k, T i j k = T j k i) :
    cubicEnergy T * cubicEnergy (fourthAction μ T) -
        (pairing T (fourthAction μ T))^2 ≤
      8 * cubicEnergy T * upperDefect μ T - (upperDefect μ T)^2 := by
  have hb := mul_le_mul_of_nonneg_left
    (actual_fourthAction_energy_le hμ T) (cubicEnergy_nonneg T)
  rw [actual_fourthAction_pairing μ T hT]
  nlinarith

/-- The stronger budget before projection also controls the nonsymmetric
part of the fourth action; no cyclic hypothesis on the input is needed. -/
theorem actual_rawFourth_transverse_budget
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Fin n → Fin n → Fin n → ℝ) :
    cubicEnergy T * cubicEnergy (rawFourthAction μ T) -
        (pairing T (rawFourthAction μ T))^2 ≤
      8 * cubicEnergy T * upperDefect μ T - (upperDefect μ T)^2 := by
  have hb := mul_le_mul_of_nonneg_left
    (actual_rawFourth_energy_le hμ T) (cubicEnergy_nonneg T)
  unfold upperDefect
  nlinarith

theorem actual_rawFourth_unit_transverse_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Fin n → Fin n → Fin n → ℝ) (hE : cubicEnergy T = 1) :
    cubicEnergy (fun i j k => rawFourthAction μ T i j k -
        (6 - upperDefect μ T)*T i j k) ≤
      8 * upperDefect μ T - (upperDefect μ T)^2 := by
  rw [cubicEnergy_sub_mul, hE]
  have h := actual_rawFourth_energy_le hμ T
  unfold upperDefect
  rw [hE] at h ⊢
  nlinarith

/-- Orthogonal splitting into the cyclic and complementary components.
This keeps their combined budget instead of allocating it twice. -/
theorem cyclicAverage_residual_split (U T : ι → ι → ι → ℝ)
    (hT : ∀ i j k, T i j k = T j k i) (a : ℝ) :
    cubicEnergy (fun i j k => U i j k - cyclicAverage U i j k) +
      cubicEnergy (fun i j k => cyclicAverage U i j k - a*T i j k) =
        cubicEnergy (fun i j k => U i j k - a*T i j k) := by
  have hc : ∀ i j k, cyclicAverage U i j k = cyclicAverage U j k i := by
    intro i j k
    unfold cyclicAverage
    ring
  have hself : pairing (cyclicAverage U) (cyclicAverage U) =
      cubicEnergy (cyclicAverage U) := by
    simp only [pairing, cubicEnergy, pow_two]
  have hp : pairing (cyclicAverage U) U = cubicEnergy (cyclicAverage U) := by
    rw [← pairing_cyclicAverage (cyclicAverage U) U hc]
    exact hself
  have h1 := cubicEnergy_sub_mul U (cyclicAverage U) 1
  have h2 := cubicEnergy_sub_mul (cyclicAverage U) T a
  have h3 := cubicEnergy_sub_mul U T a
  simp only [one_mul, one_pow, hp] at h1
  rw [pairing_cyclicAverage T U hT] at h2
  linarith

theorem actual_rawFourth_split_transverse_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ i j k, T i j k = T j k i) (hE : cubicEnergy T = 1) :
    cubicEnergy (fun i j k => rawFourthAction μ T i j k - fourthAction μ T i j k) +
      cubicEnergy (fun i j k => fourthAction μ T i j k -
        (6 - upperDefect μ T)*T i j k) ≤
      8 * upperDefect μ T - (upperDefect μ T)^2 := by
  rw [fourthAction, cyclicAverage_residual_split _ T hT]
  exact actual_rawFourth_unit_transverse_le hμ T hE

/-- The distance to the upper endpoint is paid by that same signed defect. -/
theorem actual_rawFourth_upper_distance_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Fin n → Fin n → Fin n → ℝ) :
    cubicEnergy (fun i j k => rawFourthAction μ T i j k - 6*T i j k) ≤
      8 * upperDefect μ T := by
  rw [cubicEnergy_sub_mul]
  have h := actual_rawFourth_energy_le hμ T
  unfold upperDefect
  nlinarith

theorem actual_upperDefect_nonneg
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Fin n → Fin n → Fin n → ℝ) : 0 ≤ upperDefect μ T := by
  have h := actual_rawFourth_upper_distance_le hμ T
  have h0 := cubicEnergy_nonneg (fun i j k => rawFourthAction μ T i j k - 6*T i j k)
  linarith

theorem actual_upperDefect_le_eight
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Fin n → Fin n → Fin n → ℝ) :
    upperDefect μ T ≤ 8 * cubicEnergy T := by
  have h0 := cubicEnergy_nonneg
    (fun i j k => rawFourthAction μ T i j k - (-2)*T i j k)
  rw [cubicEnergy_sub_mul] at h0
  have h := actual_rawFourth_energy_le hμ T
  unfold upperDefect
  nlinarith

private theorem cubicEnergy_eq_zero_entry
    (U : ι → ι → ι → ℝ) (hU : cubicEnergy U ≤ 0) (i j k : ι) : U i j k = 0 := by
  have hk : (U i j k)^2 ≤ ∑ c, (U i j c)^2 :=
    Finset.single_le_sum (fun c _ => sq_nonneg (U i j c)) (Finset.mem_univ k)
  have hj : (∑ c, (U i j c)^2) ≤ ∑ b, ∑ c, (U i b c)^2 :=
    Finset.single_le_sum
      (fun b _ => Finset.sum_nonneg fun c _ => sq_nonneg (U i b c)) (Finset.mem_univ j)
  have hi : (∑ b, ∑ c, (U i b c)^2) ≤ cubicEnergy U :=
    Finset.single_le_sum
      (fun a _ => Finset.sum_nonneg fun b _ =>
        Finset.sum_nonneg fun c _ => sq_nonneg (U a b c)) (Finset.mem_univ i)
  have hs : (U i j k)^2 = 0 := le_antisymm (hk.trans (hj.trans (hi.trans hU))) (sq_nonneg _)
  exact sq_eq_zero_iff.mp hs

/-- Zero upper defect retains all slices, including their common tensor
indices; it forces the actual fourth-cumulant action to equal `6 T`. -/
theorem actual_rawFourth_eq_six_of_zero_defect
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Fin n → Fin n → Fin n → ℝ) (he : upperDefect μ T = 0)
    (i j k : Fin n) : rawFourthAction μ T i j k = 6*T i j k := by
  have h := actual_rawFourth_upper_distance_le hμ T
  rw [he, mul_zero] at h
  exact sub_eq_zero.mp (cubicEnergy_eq_zero_entry _ h i j k)

/-- For a unit cubic the transverse component is the literal orthogonal
residual, and its energy is at most `8 e - e^2`. -/
theorem actual_fourthAction_unit_transverse_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ i j k, T i j k = T j k i) (hE : cubicEnergy T = 1) :
    cubicEnergy (fun i j k => fourthAction μ T i j k -
        (6 - upperDefect μ T)*T i j k) ≤
      8 * upperDefect μ T - (upperDefect μ T)^2 := by
  rw [cubicEnergy_sub_mul, actual_fourthAction_pairing μ T hT, hE]
  have h := actual_fourthAction_energy_le hμ T
  rw [hE] at h
  nlinarith

end KLSConstantImprovement.FourthCubicProjectionDefect
#print axioms KLSConstantImprovement.FourthCubicProjectionDefect.actual_fourthAction_energy_le
#print axioms KLSConstantImprovement.FourthCubicProjectionDefect.actual_fourthAction_transverse_budget
#print axioms KLSConstantImprovement.FourthCubicProjectionDefect.actual_rawFourth_upper_distance_le
#print axioms KLSConstantImprovement.FourthCubicProjectionDefect.actual_upperDefect_nonneg
#print axioms KLSConstantImprovement.FourthCubicProjectionDefect.actual_upperDefect_le_eight
#print axioms KLSConstantImprovement.FourthCubicProjectionDefect.actual_rawFourth_eq_six_of_zero_defect
#print axioms KLSConstantImprovement.FourthCubicProjectionDefect.actual_fourthAction_unit_transverse_le
#print axioms KLSConstantImprovement.FourthCubicProjectionDefect.actual_rawFourth_transverse_budget
#print axioms KLSConstantImprovement.FourthCubicProjectionDefect.actual_rawFourth_unit_transverse_le
#print axioms KLSConstantImprovement.FourthCubicProjectionDefect.actual_rawFourth_split_transverse_le
