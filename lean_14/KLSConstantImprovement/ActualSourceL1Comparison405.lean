import KLSConstantImprovement.ActualSourceResolventOrder405

/-!
The natural canonical form maximum principle with merely L1 forcing.
Each compact smooth companion differs from a nonnegative bounded test
by a constant. The actual mean identity restores that constant, so the
forcing pairing has the correct sign before taking a limit. Only the L2
test pairing and the form error pass to the limit. Neither an L2 forcing
domain nor a compact strong operator core is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter InnerProductSpace
open scoped BigOperators ContDiff Topology RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceL1Comparison405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualSourceFormCompanions405 ActualSourceUpperTest405 ActualSourceResolventOrder405
variable {n : ℕ} {μ : Measure (Space n)}

/-- Genuine compact weak equations with L1 nonpositive forcing imply an
AE nonpositive natural form solution. All approximation and bounded-test
domains are proved here. The equation and scalar representative are bound
to the actual Hessian resolvent in the next source leaf. -/
theorem ae_nonpos_of_actual_L1_compact_equation (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential)
    (r : Lp ℝ 2 (potentialMeasure d.potential)) (s : Space n → ℝ)
    (hs : Integrable s (potentialMeasure d.potential))
    (hsign : ∀ᵐ x ∂potentialMeasure d.potential, s x ≤ 0)
    (hmean : (∫ x, s x ∂potentialMeasure d.potential) =
      ∫ x, r x ∂potentialMeasure d.potential)
    (hrepresent : r = letI := d.source_probability
      (∫ x, r x ∂potentialMeasure d.potential) • CenteredL2.oneLp (potentialMeasure d.potential) +
        canonicalMetricValue d.potential U)
    (hweak : ∀ (ψ : Space n → ℝ), ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      ∀ V : CanonicalMetricH1 d.potential,
        (canonicalMetricValue d.potential V : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
          (fun x => ψ x - ∫ y, ψ y ∂potentialMeasure d.potential) →
        (∀ i : Fin n, (canonicalMetricGradient d.potential i V : Space n → ℝ)
          =ᵐ[potentialMeasure d.potential] canonicalMetricDerivative d.potential ψ i) →
        canonicalMetricEnergy d.potential U V =
          ∫ x, (s x - r x) * ψ x ∂potentialMeasure d.potential) :
    ∀ᵐ x ∂potentialMeasure d.potential, r x ≤ 0 := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let m := ∫ x, r x ∂potentialMeasure d.potential
  let mLp : Lp ℝ 2 (potentialMeasure d.potential) :=
    m • CenteredL2.oneLp (potentialMeasure d.potential)
  have hr : Integrable (r : Space n → ℝ) (potentialMeasure d.potential) :=
    (Lp.memLp r).integrable (by norm_num)
  have hsr : Integrable (fun x => s x - r x) (potentialMeasure d.potential) := hs.sub hr
  have hsrmean : (∫ x, s x - r x ∂potentialMeasure d.potential) = 0 := by
    rw [integral_sub hs hr, hmean, sub_self]
  have hrep : r = mLp + canonicalMetricValue d.potential U := hrepresent
  obtain ⟨f, W, hW, hWlim⟩ := exists_actual_compact_form_approximation d U
  let c (k : ℕ) : ℝ := (∫ x, f k x ∂potentialMeasure d.potential) - m
  let uk (k : ℕ) := mLp + canonicalMetricValue d.potential (W k)
  let κ (k : ℕ) := sourceUpperTestLp d 0 (uk k)
  let ψ (k : ℕ) := compactScalarCompose Real.smoothTransition (c k) (f k)
  let a (k : ℕ) := Real.smoothTransition (-(c k))
  have huk (k : ℕ) : (uk k : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => m + f k x - ∫ y, f k y ∂potentialMeasure d.potential := by
    filter_upwards [Lp.coeFn_add mLp (canonicalMetricValue d.potential (W k)),
      Lp.coeFn_smul m (CenteredL2.oneLp (potentialMeasure d.potential)),
      CenteredL2.oneLp_ae (potentialMeasure d.potential), (hW k).2.2.1]
      with x hx hm hx1 hval
    change (mLp + canonicalMetricValue d.potential (W k)) x = _
    rw [hx, Pi.add_apply, hm, Pi.smul_apply, hx1, smul_eq_mul, mul_one, hval]
    ring
  have huklim : Tendsto uk atTop (𝓝 r) := by
    rw [hrep]
    exact tendsto_const_nhds.add
      ((canonicalMetricValue d.potential).continuous.continuousAt.tendsto.comp hWlim)
  have hψκ (k : ℕ) : ψ k =ᵐ[potentialMeasure d.potential]
      fun x => κ k x - a k := by
    filter_upwards [huk k, sourceUpperTestLp_ae d 0 (uk k)] with x hx hκ
    change compactScalarCompose Real.smoothTransition (c k) (f k) x =
      sourceUpperTestLp d 0 (uk k) x - Real.smoothTransition (-(c k))
    rw [hκ, hx]
    have harg : f k x - c k =
        (m + f k x - ∫ y, f k y ∂potentialMeasure d.potential) - 0 := by
      dsimp only [c]
      ring
    dsimp only [compactScalarCompose]
    rw [harg]
  have hκnonneg (k : ℕ) : ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ κ k x := by
    filter_upwards [sourceUpperTestLp_ae d 0 (uk k)] with x hx
    rw [show κ k x = sourceUpperTestLp d 0 (uk k) x from rfl, hx]
    exact Real.smoothTransition.nonneg _
  have hκbound (k : ℕ) : ∀ᵐ x ∂potentialMeasure d.potential, ‖κ k x‖ ≤ 1 := by
    filter_upwards [sourceUpperTestLp_ae d 0 (uk k)] with x hx
    rw [show κ k x = sourceUpperTestLp d 0 (uk k) x from rfl, hx,
      Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  obtain ⟨B, hB, hηB⟩ := exists_deriv_smoothTransition_bound
  choose V hVval hVgrad hVcross hVE hVnorm using fun k =>
    exists_actual_smooth_form_companion d (hW k).1 (hW k).2.1 (W k) (hW k).2.2.2
      (Real.smoothTransition.contDiff (n := 3)) (c k) hB
      (fun t => (hηB t).1) (fun t => (hηB t).2)
  have hVexact (k : ℕ) (i : Fin n) :
      (canonicalMetricGradient d.potential i (V k) : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential] canonicalMetricDerivative d.potential (ψ k) i := by
    filter_upwards [hVgrad k i, (hW k).2.2.2 i] with x hx hy
    change canonicalMetricGradient d.potential i (V k) x =
      canonicalMetricDerivative d.potential (compactScalarCompose Real.smoothTransition (c k) (f k)) i x
    rw [hx, hy, compactScalarCompose_metric_derivative d.potential
      (Real.smoothTransition.contDiff (n := 1)) ((hW k).1.of_le (by norm_num))]
  have hpaired (k : ℕ) : inner ℝ r (κ k) +
      canonicalMetricEnergy d.potential U (V k) ≤ 0 := by
    have hsκ : Integrable (fun x => s x * κ k x) (potentialMeasure d.potential) :=
      hs.mul_bdd (Lp.aestronglyMeasurable (κ k)) (hκbound k)
    have hrκ : Integrable (fun x => r x * κ k x) (potentialMeasure d.potential) :=
      (Lp.memLp r).integrable_mul (Lp.memLp (κ k))
    have hsrκ : Integrable (fun x => (s x - r x) * κ k x) (potentialMeasure d.potential) :=
      hsr.mul_bdd (Lp.aestronglyMeasurable (κ k)) (hκbound k)
    have hrestored : (∫ x, (s x - r x) * ψ k x ∂potentialMeasure d.potential) =
        ∫ x, (s x - r x) * κ k x ∂potentialMeasure d.potential := by
      calc
        _ = ∫ x, (s x - r x) * κ k x - (s x - r x) * a k
            ∂potentialMeasure d.potential := by
          apply integral_congr_ae
          filter_upwards [hψκ k] with x hx
          rw [hx]
          ring
        _ = (∫ x, (s x - r x) * κ k x ∂potentialMeasure d.potential) -
            (∫ x, s x - r x ∂potentialMeasure d.potential) * a k := by
          rw [integral_sub hsrκ (hsr.mul_const _), integral_mul_const]
        _ = _ := by rw [hsrmean, zero_mul, sub_zero]
    have hpair : inner ℝ r (κ k) = ∫ x, r x * κ k x ∂potentialMeasure d.potential := by
      rw [L2.inner_def]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [RCLike.inner_apply, conj_trivial]
        ring
    have he := hweak (ψ k)
      (compactScalarCompose_contDiff (Real.smoothTransition.contDiff (n := 3)) (hW k).1 (c k))
      (compactScalarCompose_hasCompactSupport Real.smoothTransition (c k) (hW k).2.1)
      (V k) (hVval k) (hVexact k)
    rw [hrestored] at he
    have hsplit : (∫ x, (s x - r x) * κ k x ∂potentialMeasure d.potential) =
        (∫ x, s x * κ k x ∂potentialMeasure d.potential) - inner ℝ r (κ k) := by
      rw [hpair, ← integral_sub hsκ hrκ]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    rw [hsplit] at he
    have hnonpos : (∫ x, s x * κ k x ∂potentialMeasure d.potential) ≤ 0 := by
      apply integral_nonpos_of_ae
      filter_upwards [hsign, hκnonneg k] with x hx hy
      exact mul_nonpos_of_nonpos_of_nonneg hx hy
    linarith
  have hbound (k : ℕ) : inner ℝ r (κ k) ≤
      (n : ℝ) * ‖U - W k‖ * ((2 * (B + 1)) * ‖W k‖) := by
    have he : canonicalMetricEnergy d.potential (U - W k) (V k) =
        canonicalMetricEnergy d.potential U (V k) - canonicalMetricEnergy d.potential (W k) (V k) := by
      exact canonicalMetricEnergy_sub_left d.potential U (W k) (V k)
    have hn : -canonicalMetricEnergy d.potential (U - W k) (V k) ≤
        ‖canonicalMetricEnergy d.potential (U - W k) (V k)‖ := by
      simpa only [Real.norm_eq_abs] using neg_le_abs (canonicalMetricEnergy d.potential (U - W k) (V k))
    have hfirst : inner ℝ r (κ k) ≤ ‖canonicalMetricEnergy d.potential (U - W k) (V k)‖ := by
      linarith [hpaired k, hVcross k]
    have hmul := mul_le_mul_of_nonneg_left (hVnorm k)
      (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg (U - W k)))
    exact hfirst.trans ((canonicalMetricEnergy_norm_le_dimension d.potential (U - W k) (V k)).trans hmul)
  have hleft : Tendsto (fun k => inner ℝ r (κ k)) atTop
      (𝓝 (inner ℝ r (sourceUpperTestLp d 0 r))) :=
    tendsto_const_nhds.inner ((sourceUpperTestLp_continuous d 0).continuousAt.tendsto.comp huklim)
  have hdiff : Tendsto (fun k => ‖U - W k‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => U) atTop (𝓝 U)).sub hWlim).norm
  have herr : Tendsto (fun k => (n : ℝ) * ‖U - W k‖ *
      ((2 * (B + 1)) * ‖W k‖)) atTop (𝓝 (0 : ℝ)) := by
    have h1 : Tendsto (fun k => (n : ℝ) * ‖U - W k‖) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hdiff.const_mul (n : ℝ)
    simpa only [zero_mul] using h1.mul (hWlim.norm.const_mul (2 * (B + 1)))
  have hp : inner ℝ r (sourceUpperTestLp d 0 r) ≤ 0 :=
    le_of_tendsto_of_tendsto hleft herr (Eventually.of_forall hbound)
  have hzero : ∀ᵐ x ∂potentialMeasure d.potential,
      (0 : Lp ℝ 2 (potentialMeasure d.potential)) x ≤ (0 : ℝ) :=
    (Lp.coeFn_zero ℝ 2 (potentialMeasure d.potential)).mono fun _ hx => hx.le
  apply ae_upper_bound_of_upper_test d r 0 0 hzero
  simpa only [sub_zero] using hp

end KLSConstantImprovement.ActualSourceL1Comparison405

#print axioms KLSConstantImprovement.ActualSourceL1Comparison405.ae_nonpos_of_actual_L1_compact_equation
