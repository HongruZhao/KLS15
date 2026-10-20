import ActualEnergyQuotientMaximum

/-! Scalar excess contradiction and the faithful lift from an actual uniform
quotient bound back to every actual L² coefficient inequality. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem scalar_coefficient_excess_contradiction
    {α hk hj X u q C D dk dj v : ℝ}
    (hα : 0 < α) (hhk : 0 < hk) (hhj : 0 < hj) (hv : 0 < v)
    (hq : 0 < q) (hdj : 0 ≤ dj) (hX : hj*v < X)
    (hcriterion : q*(α*hj/hk*v-C*u-2*dk/Real.sqrt hk*Real.sqrt u) >
      D+2*dj/Real.sqrt (hj*v))
    (hterminal : q*(α*X/hk-C*u-2*dk/Real.sqrt hk*Real.sqrt u)-
      D-2*dj/Real.sqrt X ≤ 0) : False := by
  have hbase := mul_pos hhj hv
  have hsbase := Real.sqrt_pos.mpr hbase
  have hs : Real.sqrt (hj*v) ≤ Real.sqrt X := Real.sqrt_le_sqrt hX.le
  have hfrac : 2*dj/Real.sqrt X ≤ 2*dj/Real.sqrt (hj*v) :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hdj) hsbase hs
  have hlin : α*hj/hk*v < α*X/hk := by
    have hl := (div_lt_div_iff_of_pos_right hhk).2 (mul_lt_mul_of_pos_left hX hα)
    convert hl using 1 <;> ring
  have hstrict : q*(α*hj/hk*v-C*u-2*dk/Real.sqrt hk*Real.sqrt u) <
      q*(α*X/hk-C*u-2*dk/Real.sqrt hk*Real.sqrt u) := by
    apply mul_lt_mul_of_pos_left _ hq
    linarith
  linarith

 theorem actualAppellEnergy_eq_toLp_norm_sq {n d : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualAppellEnergy μ f d = ‖fullClassAppellTensor d (hf.toLp f)‖^2 := by
  rw [← actualAppellEnergy_eq_norm_sq]
  exact actualAppellEnergy_congr_ae hf.coeFn_toLp.symm

 theorem actual_energy_bound_of_all_quotients_le {n k : ℕ} {h hnext : ℝ}
    (hh : 0 < h) (hnext0 : 0 ≤ hnext) {φ : ℝ → ℝ}
    (hφpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < φ u)
    (hφanti : AntitoneOn φ (Icc (0 : ℝ) 1)) (hφzero : φ 0 ≤ 1)
    (hprevious : ∀ (μ : Measure (Space n)), admissibleMeasure μ → ∀ f : Space n → ℝ,
      MemLp f 2 μ → actualAppellEnergy μ f k ≤ h*(∫ x, (f x)^2 ∂μ))
    (hquot : ∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν : Measure (Space n)))
      (g : Lp ℝ 2 (ν : Measure (Space n))),
      coefficientQuotient (fullClassAppellLinearMap hν.logConcave k)
        (fullClassAppellLinearMap hν.logConcave (k+1)) h φ g ≤ hnext) :
    ∀ (μ : Measure (Space n)), admissibleMeasure μ → ∀ f : Space n → ℝ,
      MemLp f 2 μ → actualAppellEnergy μ f (k+1) ≤ hnext*(∫ x, (f x)^2 ∂μ) := by
  intro μ hμ f hf
  letI : IsProbabilityMeasure μ := hμ.isProb
  let ν : ProbabilityMeasure (Space n) := ⟨μ,hμ.isProb⟩
  let g : Lp ℝ 2 μ := hf.toLp f
  have hn : ‖g‖^2 = ∫ x, (f x)^2 ∂μ := by
    rw [actualLp_norm_sq_eq_integral]
    exact integral_congr_ae (hf.coeFn_toLp.fun_comp (fun t : ℝ => t^2))
  rw [actualAppellEnergy_eq_toLp_norm_sq hf,← hn]
  by_cases hg : g = 0
  · change ‖fullClassAppellLinearMap hμ.logConcave (k+1) g‖^2 ≤ _
    simp only [hg,map_zero,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero,le_refl]
  · have hu := actualAppell_ratio_mem_Icc hμ hh hprevious g hg
    have hp : 0 < φ (‖fullClassAppellTensor k g‖^2/(h*‖g‖^2)) := hφpos _ hu
    have hle : φ (‖fullClassAppellTensor k g‖^2/(h*‖g‖^2)) ≤ 1 :=
      (hφanti (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hu hu.1).trans hφzero
    have hgp : 0 < ‖g‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hg)
    have hb := hquot ν hμ g
    change ‖fullClassAppellTensor (k+1) g‖^2/
      (‖g‖^2*φ (‖fullClassAppellTensor k g‖^2/(h*‖g‖^2))) ≤ hnext at hb
    have hbm := (div_le_iff₀ (mul_pos hgp hp)).mp hb
    have hden : hnext*(‖g‖^2*φ (‖fullClassAppellTensor k g‖^2/(h*‖g‖^2))) ≤
        hnext*‖g‖^2 := by
      exact mul_le_mul_of_nonneg_left
        (by nlinarith [mul_nonneg hgp.le (sub_nonneg.mpr hle)]) hnext0
    exact hbm.trans hden

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.scalar_coefficient_excess_contradiction
#print axioms KLS.DeterministicBridgeNext.actual_energy_bound_of_all_quotients_le
