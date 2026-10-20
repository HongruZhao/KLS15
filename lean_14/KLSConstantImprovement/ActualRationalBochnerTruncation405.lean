import KLS.RawTraceEnergyPassage

/-! Finite Schur completion for the rational intrinsic-mass truncation.
The negative derivative of 1/(1+epsilon*M) can be charged to the already
integrable Gaffney Jacobian square, with a charge tending to zero. This
is an interior algebra/limit lemma; it supplies no global boundary test. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace KLSConstantImprovement.ActualRationalBochnerTruncation405
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

theorem rational_truncation_unnormalized {r E Q : ℝ} (hr : 0 ≤ r)
    (a b : ι → ℝ) (hE : (∑ i, a i ^ 2) ≤ E) (hQ : (∑ i, b i ^ 2) ≤ Q) :
    -r * (1 + r) * Q ≤ (1 + r) * E - r * (∑ i, (a i + b i) ^ 2) := by
  have hs : (∑ i, ((1 + r) * a i ^ 2 - r * (a i + b i) ^ 2 +
      r * (1 + r) * b i ^ 2)) = ∑ i, (a i - r * b i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have hn : 0 ≤ ∑ i, (a i - r * b i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have he := mul_le_mul_of_nonneg_left hE (show 0 ≤ 1 + r by linarith)
  have hq := mul_le_mul_of_nonneg_left hQ (show 0 ≤ r * (1 + r) by positivity)
  linarith

theorem rational_truncation_lower_bound {r E Q : ℝ} (hr : 0 ≤ r)
    (a b : ι → ℝ) (hE : (∑ i, a i ^ 2) ≤ E) (hQ : (∑ i, b i ^ 2) ≤ Q) :
    -(r / (1 + r)) * Q ≤ E / (1 + r) -
      r / (1 + r) ^ 2 * (∑ i, (a i + b i) ^ 2) := by
  have hf : 0 < 1 + r := by linarith
  have hs := div_le_div_of_nonneg_right
    (rational_truncation_unnormalized hr a b hE hQ) (sq_nonneg (1 + r))
  calc
    _ = (-r * (1 + r) * Q) / (1 + r) ^ 2 := by field_simp [hf.ne']
    _ ≤ ((1 + r) * E - r * (∑ i, (a i + b i) ^ 2)) / (1 + r) ^ 2 := hs
    _ = _ := by field_simp [hf.ne']

theorem rational_truncation_coercive_unnormalized {r E Q : ℝ} (hr : 0 ≤ r)
    (a b : ι → ℝ) (hE : (∑ i, a i ^ 2) ≤ E) (hQ : (∑ i, b i ^ 2) ≤ Q) :
    E ≤ 2 * ((1 + r) * E - r * (∑ i, (a i + b i) ^ 2) +
      2 * r * (1 + r) * Q) := by
  have hs : (∑ i, (2 * ((1 + r) * a i ^ 2 - r * (a i + b i) ^ 2 +
      2 * r * (1 + r) * b i ^ 2) - a i ^ 2)) =
      ∑ i, ((a i - 2 * r * b i) ^ 2 + 2 * r * b i ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have hn : 0 ≤ ∑ i, ((a i - 2 * r * b i) ^ 2 + 2 * r * b i ^ 2) :=
    Finset.sum_nonneg fun i _ => add_nonneg (sq_nonneg _) (by positivity)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hn
  have he := mul_le_mul_of_nonneg_left hE (show 0 ≤ 1 + 2 * r by linarith)
  have hq := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 4 * r * (1 + r) by positivity)
  nlinarith

theorem rational_truncation_coercive {r E Q : ℝ} (hr : 0 ≤ r)
    (a b : ι → ℝ) (hE : (∑ i, a i ^ 2) ≤ E) (hQ : (∑ i, b i ^ 2) ≤ Q) :
    E / (2 * (1 + r) ^ 2) ≤ E / (1 + r) -
      r / (1 + r) ^ 2 * (∑ i, (a i + b i) ^ 2) + 2 * (r / (1 + r)) * Q := by
  have hf : 0 < 1 + r := by linarith
  have hs := rational_truncation_coercive_unnormalized hr a b hE hQ
  have hh : E / 2 ≤ (1 + r) * E - r * (∑ i, (a i + b i) ^ 2) +
      2 * r * (1 + r) * Q := by linarith
  calc
    _ = (E / 2) / (1 + r) ^ 2 := by field_simp [hf.ne']
    _ ≤ ((1 + r) * E - r * (∑ i, (a i + b i) ^ 2) +
        2 * r * (1 + r) * Q) / (1 + r) ^ 2 :=
      div_le_div_of_nonneg_right hh (sq_nonneg (1 + r))
    _ = _ := by field_simp [hf.ne']

theorem rational_truncation_charge_bounds {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ r / (1 + r) ∧ r / (1 + r) ≤ 1 := by
  have hf : 0 < 1 + r := by linarith
  exact ⟨div_nonneg hr hf.le, (div_le_one hf).mpr (by linarith)⟩

/-- The interior Jacobian charge is dominated by 2*abs(Q) and vanishes.
No weighted cutoff estimate or natural mass upper bound is an input. -/
theorem integral_rational_jacobian_charge_tendsto_zero
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {M Q : α → ℝ} (hM : AEStronglyMeasurable M ν)
    (hMn : ∀ᵐ x ∂ν, 0 ≤ M x) (hQ : Integrable Q ν)
    {ε : ℕ → ℝ} (hε : ∀ k, 0 ≤ ε k) (hεlim : Tendsto ε atTop (𝓝 0)) :
    (∀ k, Integrable (fun x => 2 * (ε k * M x / (1 + ε k * M x)) * Q x) ν) ∧
      Tendsto (fun k => ∫ x, 2 * (ε k * M x / (1 + ε k * M x)) * Q x ∂ν)
        atTop (𝓝 0) := by
  have hm (k : ℕ) : AEStronglyMeasurable
      (fun x => ε k * M x / (1 + ε k * M x)) ν :=
    ((hM.const_mul (ε k)).aemeasurable.div
      (aemeasurable_const.add (hM.const_mul (ε k)).aemeasurable)).aestronglyMeasurable
  have hb (k : ℕ) : ∀ᵐ x ∂ν, ‖ε k * M x / (1 + ε k * M x)‖ ≤ 1 := by
    filter_upwards [hMn] with x hx
    obtain ⟨hlo, hhi⟩ := rational_truncation_charge_bounds (mul_nonneg (hε k) hx)
    rwa [Real.norm_of_nonneg hlo]
  have hi (k : ℕ) : Integrable
      (fun x => 2 * (ε k * M x / (1 + ε k * M x)) * Q x) ν := by
    have ht := (hQ.bdd_mul (hm k) (hb k)).const_mul 2
    simpa only [mul_assoc] using ht
  refine ⟨hi, ?_⟩
  have ht : Tendsto
      (fun k => ∫ x, 2 * (ε k * M x / (1 + ε k * M x)) * Q x ∂ν)
      atTop (𝓝 (∫ x, (0 : ℝ) ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => 2 * ‖Q x‖)
      (fun k => (hi k).aestronglyMeasurable) (hQ.norm.const_mul 2)
    · intro k
      filter_upwards [hb k] with x hx
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        _ ≤ 2 * 1 * ‖Q x‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 2)) (norm_nonneg _)
        _ = _ := by ring
    · exact Eventually.of_forall fun x => by
        have hs : Tendsto (fun k => ε k * M x / (1 + ε k * M x)) atTop (𝓝 0) := by
          have hn : Tendsto (fun k => ε k * M x) atTop (𝓝 0) := by
            simpa only [zero_mul] using hεlim.mul_const (M x)
          have hd : Tendsto (fun k => 1 + ε k * M x) atTop (𝓝 1) := by
            simpa only [add_zero] using tendsto_const_nhds.add hn
          have hh := hn.div hd (by norm_num : (1 : ℝ) ≠ 0)
          change Tendsto (fun k => ε k * M x / (1 + ε k * M x)) atTop (𝓝 (0 / 1 : ℝ)) at hh
          simpa only [zero_div] using hh
        simpa only [zero_mul, mul_zero] using (hs.const_mul 2).mul_const (Q x)
  simpa only [integral_zero] using ht

end KLSConstantImprovement.ActualRationalBochnerTruncation405
#print axioms KLSConstantImprovement.ActualRationalBochnerTruncation405.rational_truncation_unnormalized
#print axioms KLSConstantImprovement.ActualRationalBochnerTruncation405.rational_truncation_lower_bound
#print axioms KLSConstantImprovement.ActualRationalBochnerTruncation405.rational_truncation_coercive_unnormalized
#print axioms KLSConstantImprovement.ActualRationalBochnerTruncation405.rational_truncation_coercive
#print axioms KLSConstantImprovement.ActualRationalBochnerTruncation405.rational_truncation_charge_bounds
#print axioms KLSConstantImprovement.ActualRationalBochnerTruncation405.integral_rational_jacobian_charge_tendsto_zero
