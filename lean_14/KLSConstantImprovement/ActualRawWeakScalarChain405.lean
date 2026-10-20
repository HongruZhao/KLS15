import KLS.CompactRawWeakDerivative
import KLS.LocalWeakProduct
import KLS.LocalWeakAlgebra
import KLS.HessianMetricComposition
import KLSConstantImprovement.ActualWeightedL2PairingContinuity

/-!
An actual scalar weak chain rule for raw local H1 functions. The proof
uses strong mollifier convergence and Lipschitz composition on genuine
L2 spaces. It does not identify a classical derivative of the original
function. This supplies the bounded value truncations needed for maximal
canonical metric form membership.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter InnerProductSpace
open scoped BigOperators ContDiff Topology ENNReal NNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualRawWeakScalarChain405
open KLS ActualWeightedL2PairingContinuity
variable {n : ℕ}

private theorem lipschitz_comp_toLp {ρ : Measure (Space n)} {η : ℝ → ℝ} {L : ℝ≥0}
    (hη : LipschitzWith L η) (hη0 : η 0 = 0) {f : Space n → ℝ} (hf : MemLp f 2 ρ) :
    (hη.comp_memLp hη0 hf).toLp (η ∘ f) = hη.compLp hη0 (hf.toLp f) := by
  apply Lp.ext
  filter_upwards [(hη.comp_memLp hη0 hf).coeFn_toLp,
    hη.coeFn_compLp hη0 (hf.toLp f), hf.coeFn_toLp] with x hx hy hz
  change (hη.comp_memLp hη0 hf).toLp (η ∘ f) x = hη.compLp hη0 (hf.toLp f) x
  rw [hx, hy]
  change η (f x) = η ((hf.toLp f) x)
  rw [hz]

theorem lipschitz_comp_strong_L2 {ρ : Measure (Space n)} {η : ℝ → ℝ} {L : ℝ≥0}
    (hη : LipschitzWith L η) (hη0 : η 0 = 0)
    {f : ℕ → Space n → ℝ} {u : Space n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 ρ) (hu : MemLp u 2 ρ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 ρ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm ((η ∘ f k) - (η ∘ u)) 2 ρ) atTop (𝓝 0) := by
  have hF := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hconv
  have ht := (hη.continuous_compLp hη0).continuousAt.tendsto.comp hF
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k => η ∘ f k)
    (fun k => hη.comp_memLp hη0 (hf k)) (η ∘ u) (hη.comp_memLp hη0 hu)).mp
  have hseq : (fun k => (hη.comp_memLp hη0 (hf k)).toLp (η ∘ f k)) =
      hη.compLp hη0 ∘ (fun k => (hf k).toLp (f k)) := by
    funext k
    exact lipschitz_comp_toLp hη hη0 (hf k)
  rw [hseq, lipschitz_comp_toLp hη hη0 hu]
  exact ht

/-- Global genuine L2 weak derivatives obey the scalar chain rule. The
derivative of eta is Lipschitz; no differentiability of f is assumed. -/
theorem scalar_chain_of_global_L2_weak {f : Space n → ℝ} {i : Fin n}
    {F : Lp ℝ 2 (volume : Measure (Space n))}
    (hf : MemLp f 2 volume) (hF : HasWeakCoordinateDerivative f i F)
    {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) (hη0 : η 0 = 0)
    {L D : ℝ≥0} (hLip : LipschitzWith L η) (hDLip : LipschitzWith D (deriv η)) :
    HasLocalWeakCoordinateDerivative (η ∘ f) (fun x => deriv η (f x) * F x) i := by
  intro ψ hψ hc
  let δ : ℝ → ℝ := fun t => deriv η t - deriv η 0
  have hδ : LipschitzWith D δ := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [dist_eq_norm, dist_eq_norm]
    have he : δ s - δ t = deriv η s - deriv η t := by dsimp [δ]; ring
    rw [he]
    exact hDLip.norm_sub_le s t
  have hδ0 : δ 0 = 0 := sub_self _
  let fm (k : ℕ) := mollify k f
  let Fm (k : ℕ) := coordinateDerivative (mollify k f) i
  have hfm (k : ℕ) : MemLp (fm k) 2 volume := memLp_mollify hf k
  have hFm (k : ℕ) : MemLp (Fm k) 2 volume := by
    dsimp only [Fm]
    rw [hF.mollify_eq hf]
    exact memLp_mollify (Lp.memLp F) k
  have hfv : Tendsto (fun k => eLpNorm (fm k - f) 2 volume) atTop (𝓝 0) :=
    eLpNorm_mollify_sub_tendsto_zero hf
  have hFd : Tendsto (fun k => eLpNorm (Fm k - (F : Space n → ℝ)) 2 volume) atTop (𝓝 0) :=
    hF.eLpNorm_mollify_derivative_sub_tendsto_zero hf
  have hηfm (k : ℕ) : MemLp (η ∘ fm k) 2 volume := hLip.comp_memLp hη0 (hfm k)
  have hηf : MemLp (η ∘ f) 2 volume := hLip.comp_memLp hη0 hf
  have hδfm (k : ℕ) : MemLp (δ ∘ fm k) 2 volume := hδ.comp_memLp hδ0 (hfm k)
  have hδf : MemLp (δ ∘ f) 2 volume := hδ.comp_memLp hδ0 hf
  have hψtop : MemLp ψ ∞ volume := hψ.continuous.memLp_top_of_hasCompactSupport hc volume
  have hψ2 : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hc
  have hdψ2 : MemLp (coordinateDerivative ψ i) 2 volume :=
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hc i)
  let Bm (k : ℕ) (x : Space n) := ψ x * δ (fm k x)
  let B (x : Space n) := ψ x * δ (f x)
  have hBm (k : ℕ) : MemLp (Bm k) 2 volume := hψtop.mul (hδfm k)
  have hB : MemLp B 2 volume := hψtop.mul hδf
  have hBlim : Tendsto (fun k => eLpNorm (Bm k - B) 2 volume) atTop (𝓝 0) :=
    weighted_L2_bounded_mul_tendsto hψtop hδfm hδf
      (lipschitz_comp_strong_L2 hδ hδ0 hfm hf hfv)
  have hleft := tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero hηfm hηf hdψ2
    (lipschitz_comp_strong_L2 hLip hη0 hfm hf hfv)
  have hright₁ := tendsto_integral_mul_of_weighted_L2 hBm hFm hB (Lp.memLp F) hBlim hFd
  have hright₂ := tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero hFm (Lp.memLp F) hψ2 hFd
  have he (k : ℕ) : (∫ x, coordinateDerivative ψ i x * η (fm k x)) =
      -((∫ x, Bm k x * Fm k x) + deriv η 0 * ∫ x, ψ x * Fm k x) := by
    have hmk : ContDiff ℝ 1 (fm k) :=
      (mollify_contDiff (hf.locallyIntegrable (by norm_num)) k).of_le (by simp)
    have hw := hasLocalWeakCoordinateDerivative_of_contDiff (hη.comp hmk) i ψ hψ hc
    have hchain : coordinateDerivative (η ∘ fm k) i = fun x => deriv η (fm k x) * Fm k x := by
      funext x
      exact coordinateDerivative_scalar_comp (hη.differentiable one_ne_zero _)
        (hmk.differentiable one_ne_zero _) i
    rw [hchain] at hw
    have hleftEq : (∫ x, (η ∘ fm k) x * coordinateDerivative ψ i x) =
        ∫ x, coordinateDerivative ψ i x * η (fm k x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by change η (fm k x) * _ = _; ring
    have hrightEq : (∫ x, (deriv η (fm k x) * Fm k x) * ψ x) =
        (∫ x, Bm k x * Fm k x) + deriv η 0 * ∫ x, ψ x * Fm k x := by
      have ha : Integrable (fun x => Bm k x * Fm k x) volume := (hBm k).integrable_mul (hFm k)
      have hb : Integrable (fun x => ψ x * Fm k x) volume := hψ2.integrable_mul (hFm k)
      rw [← integral_const_mul, ← integral_add ha (hb.const_mul (deriv η 0))]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [Bm, δ]; ring
    rwa [hleftEq, hrightEq] at hw
  have hfinal := tendsto_nhds_unique hleft
    ((hright₁.add (hright₂.const_mul (deriv η 0))).neg.congr (fun k => (he k).symm))
  have hl : (∫ x, coordinateDerivative ψ i x * (η ∘ f) x) =
      ∫ x, (η ∘ f) x * coordinateDerivative ψ i x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  have hr : (∫ x, B x * F x) + deriv η 0 * ∫ x, ψ x * F x =
      ∫ x, (deriv η (f x) * F x) * ψ x := by
    have ha : Integrable (fun x => B x * F x) volume := hB.integrable_mul (Lp.memLp F)
    have hb : Integrable (fun x => ψ x * F x) volume := hψ2.integrable_mul (Lp.memLp F)
    rw [← integral_const_mul, ← integral_add ha (hb.const_mul (deriv η 0))]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only [B, δ]; ring
  rwa [hl, hr] at hfinal

end KLSConstantImprovement.ActualRawWeakScalarChain405

#print axioms KLSConstantImprovement.ActualRawWeakScalarChain405.lipschitz_comp_strong_L2
#print axioms KLSConstantImprovement.ActualRawWeakScalarChain405.scalar_chain_of_global_L2_weak
