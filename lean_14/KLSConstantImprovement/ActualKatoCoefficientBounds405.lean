import KLSConstantImprovement.ActualSmoothKatoRegularizer405

/-! Fixed-parameter coefficient bounds for the actual nonlinear Bochner
passage, and the literal derivative limit at every nonnegative mass. -/
noncomputable section
open Filter
open scoped Topology
namespace KLSConstantImprovement.ActualKatoCoefficientBounds405
open KLS ActualSmoothKatoRegularizer405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem katoFirst_fixed_bound {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) :
    0 ≤ katoFirst ε M ∧ katoFirst ε M ≤ 1 / (2 * Real.sqrt ε) := by
  have hr := katoRho_positive hε M
  have hs := katoRegularizer_positive hε M
  have hmr : M ≤ katoRho ε M := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ε])
  have her : ε ≤ katoRho ε M := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg M])
  have hsq : Real.sqrt ε ≤ katoRegularizer ε M := Real.sqrt_le_sqrt her
  have heq : katoRho ε M / (2 * katoRho ε M * katoRegularizer ε M) =
      1 / (2 * katoRegularizer ε M) := by field_simp [hr.ne', hs.ne']
  refine ⟨(katoRegularizer_coefficient_bounds hε hM).1, ?_⟩
  calc
    katoFirst ε M ≤ katoRho ε M / (2 * katoRho ε M * katoRegularizer ε M) :=
      div_le_div_of_nonneg_right hmr (by positivity)
    _ = 1 / (2 * katoRegularizer ε M) := heq
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) (by nlinarith only [hsq])

theorem katoSecond_mass_fixed_bound {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) :
    |katoSecond ε M| * M ≤ 1 / (2 * Real.sqrt ε) := by
  have hr := katoRho_positive hε M
  have hs := katoRegularizer_positive hε M
  have hr2 := katoRho_square (ε := ε) (t := M)
  have hmr : M ≤ katoRho ε M := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ε])
  have her : ε ≤ katoRho ε M := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg M])
  have hsq : Real.sqrt ε ≤ katoRegularizer ε M := Real.sqrt_le_sqrt her
  have hab : |2 * ε ^ 2 - M ^ 2| ≤ 2 * katoRho ε M ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg M, sq_nonneg ε]
  have hnum : |2 * ε ^ 2 - M ^ 2| * M ≤ 2 * katoRho ε M ^ 3 := by
    have hh := mul_le_mul hab hmr hM (by positivity : 0 ≤ 2 * katoRho ε M ^ 2)
    nlinarith only [hh]
  have hform : |katoSecond ε M| * M =
      (|2 * ε ^ 2 - M ^ 2| * M) / (4 * katoRho ε M ^ 3 * katoRegularizer ε M) := by
    unfold katoSecond
    rw [abs_div, abs_of_pos (by positivity : 0 < 4 * katoRho ε M ^ 3 * katoRegularizer ε M)]
    ring
  rw [hform]
  calc
    _ ≤ (2 * katoRho ε M ^ 3) / (4 * katoRho ε M ^ 3 * katoRegularizer ε M) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = 1 / (2 * katoRegularizer ε M) := by field_simp [hr.ne', hs.ne'] <;> ring
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) (by nlinarith only [hsq])

theorem katoFirst_tendsto {M : ℝ} (hM : 0 ≤ M) :
    Tendsto (fun k => katoFirst (cutoffScale k) M) atTop
      (𝓝 (if M = 0 then 0 else 1 / (2 * Real.sqrt M))) := by
  by_cases hz : M = 0
  · simp only [hz, katoFirst, zero_div, ite_true]
    exact tendsto_const_nhds
  · have hp : 0 < M := lt_of_le_of_ne hM (Ne.symm hz)
    have hr : Tendsto (fun k => katoRho (cutoffScale k) M) atTop (𝓝 M) := by
      have ha := (tendsto_const_nhds (x := M ^ 2)).add (cutoffScale_tendsto_zero.pow 2)
      have ht := Real.continuous_sqrt.continuousAt.tendsto.comp ha
      change Tendsto (fun k => Real.sqrt (M ^ 2 + cutoffScale k ^ 2)) atTop
        (𝓝 (Real.sqrt (M ^ 2 + 0 ^ 2))) at ht
      simpa only [katoRho, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, Real.sqrt_sq hM] using ht
    have hd := (hr.const_mul 2).mul (katoRegularizer_tendsto hM)
    have ht := (tendsto_const_nhds (x := M)).div hd (by positivity : 2 * M * Real.sqrt M ≠ 0)
    have heq : M / (2 * M * Real.sqrt M) = 1 / (2 * Real.sqrt M) := by
      field_simp [hz, (Real.sqrt_pos.mpr hp).ne']
    change Tendsto (fun k => M / (2 * katoRho (cutoffScale k) M * katoRegularizer (cutoffScale k) M))
      atTop (𝓝 (M / (2 * M * Real.sqrt M))) at ht
    simpa only [katoFirst, if_neg hz, heq] using ht

end KLSConstantImprovement.ActualKatoCoefficientBounds405
#print axioms KLSConstantImprovement.ActualKatoCoefficientBounds405.katoFirst_fixed_bound
#print axioms KLSConstantImprovement.ActualKatoCoefficientBounds405.katoSecond_mass_fixed_bound
#print axioms KLSConstantImprovement.ActualKatoCoefficientBounds405.katoFirst_tendsto
