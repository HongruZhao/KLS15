import KLSConstantImprovement.ActualSourceUpperTest405
import KLS.WeightedResolventWeakEquation

/-!
Order of the actual full conservative unit resolvent. Compact scalar
approximation is used only in the canonical form norm. Smooth companion
tests have uniformly bounded form norm, so the resolvent pairing passes
to the natural variational solution. No compact strong operator core,
operator-range density or semigroup order premise is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter InnerProductSpace
open scoped BigOperators ContDiff Topology RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceResolventOrder405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCanonicalMetricResolvent ActualWeakCanonicalMetricInverse
open ActualSourceConservativeResolvent405 ActualSourceFormCompanions405 ActualSourceUpperTest405
variable {n : ℕ} {μ : Measure (Space n)}

theorem canonicalMetricEnergy_sub_left (φ : Space n → ℝ)
    (U W V : CanonicalMetricH1 φ) :
    canonicalMetricEnergy φ (U - W) V =
      canonicalMetricEnergy φ U V - canonicalMetricEnergy φ W V := by
  have hmap : canonicalMetricEnergy φ (U - W) =
      canonicalMetricEnergy φ U - canonicalMetricEnergy φ W :=
    (canonicalMetricEnergy φ).map_sub U W
  exact congrArg (fun L : CanonicalMetricH1 φ →L[ℝ] ℝ => L V) hmap

/-- A direct finite-coordinate bound avoids any choice of norm on a
curried bilinear-map space. The graph Hilbert norm controls each genuine
metric-gradient coordinate. -/
theorem canonicalMetricEnergy_norm_le_dimension (φ : Space n → ℝ)
    (U V : CanonicalMetricH1 φ) :
    ‖canonicalMetricEnergy φ U V‖ ≤ (n : ℝ) * ‖U‖ * ‖V‖ := by
  have hcoord (Z : CanonicalMetricH1 φ) (i : Fin n) :
      ‖canonicalMetricGradient φ i Z‖ ≤ ‖Z‖ :=
    PiLp.norm_apply_le (Z : WeightedEnergyAmbient φ) i.succ
  rw [canonicalMetricEnergy_apply]
  calc
    _ ≤ ∑ i : Fin n, ‖inner ℝ (canonicalMetricGradient φ i U)
        (canonicalMetricGradient φ i V)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖U‖ * ‖V‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_inner_le_norm _ _).trans (mul_le_mul (hcoord U i) (hcoord V i)
        (norm_nonneg _) (norm_nonneg _))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_assoc]

/-- The actual variational resolvent pays the smooth upper-test pairing.
All test-domain and limiting assertions are conclusions of form density
and the companion bounds. -/
theorem sourceConservativeResolvent_upper_test_pairing (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (M : ℝ) :
    inner ℝ (sourceConservativeResolvent d (t := 1) zero_lt_one g - g)
      (sourceUpperTestLp d M (sourceConservativeResolvent d (t := 1) zero_lt_one g)) ≤ 0 := by
  letI := d.source_probability
  let U := canonicalResolventH1 d.potential (t := 1) zero_lt_one g
  let u := sourceConservativeResolvent d (t := 1) zero_lt_one g
  let w := u - g
  let m := ∫ x, g x ∂potentialMeasure d.potential
  let mLp : Lp ℝ 2 (potentialMeasure d.potential) :=
    m • CenteredL2.oneLp (potentialMeasure d.potential)
  have hu : u = mLp + canonicalMetricValue d.potential U := by
    dsimp only [u]
    rw [sourceConservativeResolvent_apply, weightedMassProjection_apply]
    rfl
  have hwmean : (∫ x, w x ∂potentialMeasure d.potential) = 0 := by
    change (∫ x, (u - g) x ∂potentialMeasure d.potential) = 0
    rw [integral_congr_ae (Lp.coeFn_sub u g)]
    change (∫ x, u x - g x ∂potentialMeasure d.potential) = 0
    rw [integral_sub ((Lp.memLp u).integrable (by norm_num)) ((Lp.memLp g).integrable (by norm_num))]
    exact sub_eq_zero.mpr (sourceConservativeResolvent_integral d zero_lt_one g)
  have hvariational (V : CanonicalMetricH1 d.potential) :
      inner ℝ w (canonicalMetricValue d.potential V) = -canonicalMetricEnergy d.potential U V := by
    have hv := canonicalResolvent_variational d.potential (t := 1) zero_lt_one g V
    change inner ℝ (canonicalMetricValue d.potential U) (canonicalMetricValue d.potential V) +
      1 * canonicalMetricEnergy d.potential U V = inner ℝ g (canonicalMetricValue d.potential V) at hv
    have hmV : inner ℝ mLp (canonicalMetricValue d.potential V) = 0 := by
      change inner ℝ (m • CenteredL2.oneLp (potentialMeasure d.potential))
        (canonicalMetricValue d.potential V) = 0
      rw [inner_smul_left, CenteredL2.inner_oneLp,
        canonicalMetricValue_integral_eq_zero d.source_C1.continuous V, mul_zero]
    change inner ℝ (u - g) (canonicalMetricValue d.potential V) = _
    rw [inner_sub_left, hu, inner_add_left, hmV, zero_add]
    linarith
  obtain ⟨f, W, hW, hWlim⟩ := exists_actual_compact_form_approximation d U
  let c (k : ℕ) : ℝ := (∫ x, f k x ∂potentialMeasure d.potential) - m + M
  let uk (k : ℕ) := mLp + canonicalMetricValue d.potential (W k)
  have huk (k : ℕ) : (uk k : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => m + f k x - ∫ y, f k y ∂potentialMeasure d.potential := by
    filter_upwards [Lp.coeFn_add mLp (canonicalMetricValue d.potential (W k)),
      Lp.coeFn_smul m (CenteredL2.oneLp (potentialMeasure d.potential)),
      CenteredL2.oneLp_ae (potentialMeasure d.potential), (hW k).2.2.1]
      with x hx hm hx1 hval
    change (mLp + canonicalMetricValue d.potential (W k)) x = _
    rw [hx, Pi.add_apply, hm, Pi.smul_apply, hx1, smul_eq_mul, mul_one, hval]
    ring
  have huklim : Tendsto uk atTop (𝓝 u) := by
    rw [hu]
    exact tendsto_const_nhds.add
      ((canonicalMetricValue d.potential).continuous.continuousAt.tendsto.comp hWlim)
  obtain ⟨B, hB, hηB⟩ := exists_deriv_smoothTransition_bound
  choose V hVval hVgrad hVcross hVE hVnorm using fun k =>
    exists_actual_smooth_form_companion d (hW k).1 (hW k).2.1 (W k) (hW k).2.2.2
      (Real.smoothTransition.contDiff (n := 3)) (c k) hB
      (fun s => (hηB s).1) (fun s => (hηB s).2)
  have hpair (k : ℕ) : inner ℝ w (canonicalMetricValue d.potential (V k)) =
      inner ℝ w (sourceUpperTestLp d M (uk k)) := by
    have hκ : MemLp (compactScalarCompose Real.smoothTransition (c k) (f k))
        2 (potentialMeasure d.potential) := memLp_of_continuous_hasCompactSupport d.source_C1.continuous
      (compactScalarCompose_contDiff (Real.smoothTransition.contDiff (n := 3)) (hW k).1 (c k)).continuous
      (compactScalarCompose_hasCompactSupport Real.smoothTransition (c k) (hW k).2.1)
    rw [weighted_inner_centered_test hκ (hVval k) w, hwmean, zero_mul, sub_zero]
    have hprod : Integrable (fun x => w x * sourceUpperTestLp d M (uk k) x)
        (potentialMeasure d.potential) :=
      (Lp.memLp w).integrable_mul (Lp.memLp (sourceUpperTestLp d M (uk k)))
    have hconst := ((Lp.memLp w).integrable (by norm_num)).mul_const (Real.smoothTransition (-(c k)))
    calc
      _ = ∫ x, w x * sourceUpperTestLp d M (uk k) x -
          w x * Real.smoothTransition (-(c k)) ∂potentialMeasure d.potential := by
        apply integral_congr_ae
        filter_upwards [huk k, sourceUpperTestLp_ae d M (uk k)] with x hx ht
        rw [ht, hx]
        have hc : f k x - c k = (m + f k x - ∫ y, f k y ∂potentialMeasure d.potential) - M := by
          dsimp only [c]
          ring
        dsimp only [compactScalarCompose]
        rw [hc]
        ring
      _ = _ := by
        rw [integral_sub hprod hconst, integral_mul_const, hwmean, zero_mul, sub_zero, L2.inner_def]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simp only [RCLike.inner_apply, conj_trivial]
          ring
  have hbound (k : ℕ) : inner ℝ w (sourceUpperTestLp d M (uk k)) ≤
      (n : ℝ) * ‖U - W k‖ * ((2 * (B + 1)) * ‖W k‖) := by
    have he : canonicalMetricEnergy d.potential (U - W k) (V k) =
        canonicalMetricEnergy d.potential U (V k) - canonicalMetricEnergy d.potential (W k) (V k) := by
      exact canonicalMetricEnergy_sub_left d.potential U (W k) (V k)
    have hn : -canonicalMetricEnergy d.potential (U - W k) (V k) ≤
        ‖canonicalMetricEnergy d.potential (U - W k) (V k)‖ := by
      simpa only [Real.norm_eq_abs] using neg_le_abs (canonicalMetricEnergy d.potential (U - W k) (V k))
    have hfirst : inner ℝ w (sourceUpperTestLp d M (uk k)) ≤
        ‖canonicalMetricEnergy d.potential (U - W k) (V k)‖ := by
      rw [← hpair k, hvariational]
      linarith [hVcross k]
    have hmul := mul_le_mul_of_nonneg_left (hVnorm k)
      (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg (U - W k)))
    exact hfirst.trans ((canonicalMetricEnergy_norm_le_dimension d.potential (U - W k) (V k)).trans hmul)
  have hleft : Tendsto (fun k => inner ℝ w (sourceUpperTestLp d M (uk k))) atTop
      (𝓝 (inner ℝ w (sourceUpperTestLp d M u))) :=
    tendsto_const_nhds.inner ((sourceUpperTestLp_continuous d M).continuousAt.tendsto.comp huklim)
  have hdiff : Tendsto (fun k => ‖U - W k‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => U) atTop (𝓝 U)).sub hWlim).norm
  have herr : Tendsto (fun k => (n : ℝ) * ‖U - W k‖ *
      ((2 * (B + 1)) * ‖W k‖)) atTop (𝓝 (0 : ℝ)) := by
    have h1 : Tendsto (fun k => (n : ℝ) * ‖U - W k‖)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hdiff.const_mul (n : ℝ)
    simpa only [zero_mul] using h1.mul (hWlim.norm.const_mul (2 * (B + 1)))
  exact le_of_tendsto_of_tendsto hleft herr (Eventually.of_forall hbound)

theorem sourceConservativeResolvent_upper_bound (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (M : ℝ)
    (hg : ∀ᵐ x ∂potentialMeasure d.potential, g x ≤ M) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      sourceConservativeResolvent d (t := 1) zero_lt_one g x ≤ M :=
  ae_upper_bound_of_upper_test d _ g M hg (sourceConservativeResolvent_upper_test_pairing d g M)

/-- Positivity belongs to the actual full conservative unit resolvent. -/
theorem sourceConservativeResolvent_nonneg (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ g x) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      0 ≤ sourceConservativeResolvent d (t := 1) zero_lt_one g x := by
  have hneg : ∀ᵐ x ∂potentialMeasure d.potential, (-g) x ≤ (0 : ℝ) := by
    filter_upwards [Lp.coeFn_neg g, hg] with x hx hy
    rw [hx, Pi.neg_apply]
    linarith
  have hu := sourceConservativeResolvent_upper_bound d (-g) 0 hneg
  rw [map_neg] at hu
  filter_upwards [hu, Lp.coeFn_neg (sourceConservativeResolvent d (t := 1) zero_lt_one g)] with x hx hy
  rw [hy, Pi.neg_apply] at hx
  linarith

theorem sourceConservativeResolvent_order (d : SourceData μ)
    (f g : Lp ℝ 2 (potentialMeasure d.potential))
    (hfg : ∀ᵐ x ∂potentialMeasure d.potential, f x ≤ g x) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      sourceConservativeResolvent d (t := 1) zero_lt_one f x ≤
        sourceConservativeResolvent d (t := 1) zero_lt_one g x := by
  have hpos : ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ (g - f) x := by
    filter_upwards [Lp.coeFn_sub g f, hfg] with x hx hy
    rw [hx, Pi.sub_apply]
    exact sub_nonneg.mpr hy
  have hu := sourceConservativeResolvent_nonneg d (g - f) hpos
  rw [map_sub] at hu
  filter_upwards [hu, Lp.coeFn_sub (sourceConservativeResolvent d (t := 1) zero_lt_one g)
    (sourceConservativeResolvent d (t := 1) zero_lt_one f)] with x hx hy
  rw [hy, Pi.sub_apply] at hx
  exact sub_nonneg.mp hx

end KLSConstantImprovement.ActualSourceResolventOrder405

#print axioms KLSConstantImprovement.ActualSourceResolventOrder405.sourceConservativeResolvent_upper_test_pairing
#print axioms KLSConstantImprovement.ActualSourceResolventOrder405.sourceConservativeResolvent_upper_bound
#print axioms KLSConstantImprovement.ActualSourceResolventOrder405.sourceConservativeResolvent_nonneg
#print axioms KLSConstantImprovement.ActualSourceResolventOrder405.sourceConservativeResolvent_order
