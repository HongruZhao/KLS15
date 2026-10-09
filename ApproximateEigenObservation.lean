import Mathlib

/-! The fixed-power observation step in manuscript Lemma 7.1.
The approximate eigenvector hypothesis is genuine; no spectral conclusion
or actual-law observation bound is assumed as an axiom. -/
noncomputable section
open Filter Topology
namespace ApproximateEigenObservation

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem power_residual_step (T : H →L[ℂ] H) (z : ℂ) (v : H) (m : ℕ) :
    (T ^ (m + 1)) v - z ^ (m + 1) • v =
      T ((T ^ m) v - z ^ m • v) + z ^ m • (T v - z • v) := by
  rw [pow_succ', ContinuousLinearMap.mul_apply]
  simp only [map_sub, map_smul, smul_sub, smul_smul, pow_succ]
  abel

theorem power_residual_tendsto (T : H →L[ℂ] H) (z : ℂ) (v : ℕ → H)
    (h : Tendsto (fun n => T (v n) - z • v n) atTop (𝓝 0)) (m : ℕ) :
    Tendsto (fun n => (T ^ m) (v n) - z ^ m • v n) atTop (𝓝 0) := by
  induction m with
  | zero => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : H)) atTop (𝓝 0))
  | succ m ih =>
      have hT : Tendsto (fun n => T ((T ^ m) (v n) - z ^ m • v n))
          atTop (𝓝 0) := by
        simpa [Function.comp_def] using (T.continuous.tendsto 0).comp ih
      have hz : Tendsto (fun n => z ^ m • (T (v n) - z • v n))
          atTop (𝓝 0) := by
        simpa using h.const_smul (z ^ m)
      simpa only [power_residual_step, add_zero] using hT.add hz

theorem observation_residual_tendsto (T : H →L[ℂ] H) (L : H →L[ℂ] E)
    (z : ℂ) (v : ℕ → H)
    (h : Tendsto (fun n => T (v n) - z • v n) atTop (𝓝 0)) (m : ℕ) :
    Tendsto (fun n => L ((T ^ m) (v n)) - z ^ m • L (v n)) atTop (𝓝 0) := by
  have hp := power_residual_tendsto T z v h m
  simpa only [Function.comp_def, map_sub, map_smul, map_zero] using
    (L.continuous.tendsto 0).comp hp

theorem observation_norm_bound (T : H →L[ℂ] H) (L : H →L[ℂ] E)
    (z : ℂ) (v : H) (m : ℕ) :
    ‖z‖ ^ m * ‖L v‖ ≤ ‖L.comp (T ^ m)‖ * ‖v‖ +
      ‖L ((T ^ m) v) - z ^ m • L v‖ := by
  have htriangle := norm_le_norm_add_norm_sub (L ((T ^ m) v)) (z ^ m • L v)
  have hoperator := (L.comp (T ^ m)).le_opNorm v
  simp only [norm_smul, norm_pow] at htriangle
  simp only [ContinuousLinearMap.comp_apply] at hoperator
  linarith

/-- Passing the fixed-power observations to an approximate eigenvector
sequence. This is the unsquared form of manuscript (7.4)'s observation step. -/
theorem observation_limit_bound (T : H →L[ℂ] H) (L : H →L[ℂ] E)
    (z : ℂ) (v : ℕ → H) (p : ℝ)
    (hunit : ∀ n, ‖v n‖ = 1)
    (hresidual : Tendsto (fun n => T (v n) - z • v n) atTop (𝓝 0))
    (hp : Tendsto (fun n => ‖L (v n)‖) atTop (𝓝 p)) (m : ℕ) :
    ‖z‖ ^ m * p ≤ ‖L.comp (T ^ m)‖ := by
  have he := (observation_residual_tendsto T L z v hresidual m).norm
  have hleft : Tendsto (fun n => ‖z‖ ^ m * ‖L (v n)‖) atTop (𝓝 (‖z‖ ^ m * p)) :=
    hp.const_mul _
  have hright : Tendsto (fun n => ‖L.comp (T ^ m)‖ +
      ‖L ((T ^ m) (v n)) - z ^ m • L (v n)‖) atTop (𝓝 ‖L.comp (T ^ m)‖) := by
    simpa using tendsto_const_nhds.add he
  apply le_of_tendsto_of_tendsto' hleft hright
  intro n
  simpa only [hunit n, mul_one] using observation_norm_bound T L z (v n) m

theorem positive_geometric_observation_le {p C s K : ℝ} (hp : 0 < p)
    (hK : 0 < K) (m₀ : ℕ)
    (hobs : ∀ m, m₀ ≤ m → s ^ m * p ≤ C * K ^ m) : s ≤ K := by
  by_contra hn
  have hKs : K < s := not_le.mp hn
  have hs : 0 < s := lt_trans hK hKs
  have hratio : K / s < 1 := (div_lt_one hs).mpr hKs
  have hlim : Tendsto (fun m : ℕ => C * (K / s) ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg hK.le hs.le) hratio).const_mul C
  have hev : ∀ᶠ m : ℕ in atTop, p ≤ C * (K / s) ^ m := by
    filter_upwards [eventually_ge_atTop m₀] with m hm
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hs m)).mpr
    simpa only [mul_comm] using hobs m hm
  have hpzero : p ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hev
  linarith

/-- A positive limiting observation rules out an approximate eigenvalue
whose squared modulus exceeds the geometric observation exponent. -/
theorem approximate_eigenvalue_sq_le (T : H →L[ℂ] H) (L : H →L[ℂ] E)
    (z : ℂ) (v : ℕ → H) (p C K : ℝ) (m₀ : ℕ)
    (hp : 0 < p) (hK : 0 < K)
    (hunit : ∀ n, ‖v n‖ = 1)
    (hresidual : Tendsto (fun n => T (v n) - z • v n) atTop (𝓝 0))
    (hplimit : Tendsto (fun n => ‖L (v n)‖) atTop (𝓝 p))
    (hobs : ∀ m, m₀ ≤ m → ‖L.comp (T ^ m)‖ ^ 2 ≤ C * K ^ m) :
    ‖z‖ ^ 2 ≤ K := by
  apply positive_geometric_observation_le (sq_pos_of_pos hp) hK m₀
  intro m hm
  have hb := observation_limit_bound T L z v p hunit hresidual hplimit m
  have hsq : (‖z‖ ^ m * p) ^ 2 ≤ ‖L.comp (T ^ m)‖ ^ 2 := by
    nlinarith [norm_nonneg (L.comp (T ^ m)),
      mul_nonneg (pow_nonneg (norm_nonneg z) m) hp.le]
  have heq : (‖z‖ ^ m * p) ^ 2 = (‖z‖ ^ 2) ^ m * p ^ 2 := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
    congr 2
    omega
  rw [heq] at hsq
  exact hsq.trans (hobs m hm)

/-- The positive mass supplied by the nonlinear curvature comparison,
once its scalar limit inequality has been derived. -/
theorem curvature_limit_positive {a s p : ℝ} (ha : 0 < a) (hs : 0 < s)
    (hp : 0 ≤ p) (h : s ≤ (s + p) / (1 + a * (s + p))) :
    0 < p ∧ a * s < 1 ∧ a * s ^ 2 / (1 - a * s) ≤ p := by
  have hsum : 0 < s + p := by linarith
  have hden : 0 < 1 + a * (s + p) := by positivity
  have hc := (le_div_iff₀ hden).mp h
  have hprod : 0 < a * s * (s + p) := by positivity
  have hpos : 0 < p := by nlinarith
  have has : a * s < 1 := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hsum.le
    nlinarith
  refine ⟨hpos, has, ?_⟩
  apply (div_le_iff₀ (by linarith : 0 < 1 - a * s)).mpr
  nlinarith

#print axioms power_residual_tendsto
#print axioms observation_residual_tendsto
#print axioms observation_limit_bound
#print axioms approximate_eigenvalue_sq_le
#print axioms curvature_limit_positive
end ApproximateEigenObservation
