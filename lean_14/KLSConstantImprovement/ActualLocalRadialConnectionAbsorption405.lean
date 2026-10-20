import KLSConstantImprovement.ActualSourceRadialConnectionBalance405
import KLSConstantImprovement.ActualSourceCompactCutoffBound405

/-! Uniform radial connection absorption on each fixed compact source set.
Actual M,Q are only L1. The compact condition number is finite, so no global
mass upper bound or global condition bound is needed. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualLocalRadialConnectionAbsorption405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualSourceConnectionFields405 ActualSourceConnectionPointwise405
open ActualSourceRadialConnectionDomains405 ActualSourceRadialConnectionBalance405
open ActualSourceCompactMetricCondition405 ActualSourceCompactCutoffBound405
open ActualSourceCompactConnectionAbsorption405 ActualRadialMatrixCalculus405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem radial_connection_absorption_scalar {Γ P M Q e X Y B c f χ : ℝ}
    (hΓ : 0 ≤ Γ) (hP : 0 ≤ P) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (he : 0 ≤ e)
    (hc : 0 ≤ c) (hf : 1 ≤ f)
    (hX : |X| ≤ Γ / 4 + 4 * Q)
    (hY : |Y| ≤ Γ / (4 * f) + 4 * c * Q / f)
    (hB : |2 * (χ * B)| ≤ χ ^ 2 * Γ / 4 + 4 * (M * e)) :
    χ ^ 2 * Γ / (4 * f) ≤ χ ^ 2 * (P + Γ) / f + χ ^ 2 * X / f - χ ^ 2 * Y +
      2 * (χ * B) / f + 4 * (1 + c) * (χ ^ 2 * Q) + 4 * (M * e) := by
  have hfp : 0 < f := by linarith
  have h1 := mul_le_mul_of_nonneg_left (abs_le.mp hX).1
    (div_nonneg (sq_nonneg χ) hfp.le)
  have h2 := mul_le_mul_of_nonneg_left (abs_le.mp hY).2 (sq_nonneg χ)
  have h3 := div_le_div_of_nonneg_right (abs_le.mp hB).1 hfp.le
  have h4 : χ ^ 2 * Q / f ≤ χ ^ 2 * Q := div_le_self (mul_nonneg (sq_nonneg χ) hQ) hf
  have h5 : M * e / f ≤ M * e := div_le_self (mul_nonneg hM he) hf
  have h6 : 0 ≤ χ ^ 2 * P / f := div_nonneg (mul_nonneg (sq_nonneg χ) hP) hfp.le
  have hx : -(χ ^ 2 * Γ / (4 * f)) - 4 * (χ ^ 2 * Q / f) ≤ χ ^ 2 * X / f := by
    convert h1 using 1 <;> ring
  have hy : χ ^ 2 * Y ≤ χ ^ 2 * Γ / (4 * f) + 4 * c * (χ ^ 2 * Q / f) := by
    convert h2 using 1 <;> ring
  have hb : -(χ ^ 2 * Γ / (4 * f)) - 4 * (M * e / f) ≤ 2 * (χ * B) / f := by
    convert h3 using 1 <;> ring
  have h7 := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 4 * (1 + c))
  have h8 := mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ 4)
  have hp : χ ^ 2 * (P + Γ) / f = χ ^ 2 * P / f + 4 * (χ ^ 2 * Γ / (4 * f)) := by ring
  rw [hp]
  nlinarith only [hx, hy, hb, h7, h8, h6]

theorem actual_uniform_compact_radial_connection_absorption (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (hQi : Integrable (sourceVectorJacobianEnergy Du) (potentialMeasure d.potential))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hb : ∀ x, ‖χ x‖ ≤ 1) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ δ : ℝ, 0 < δ →
      (∫ x, χ x ^ 2 * sourceConnectionGamma d (naturalCanonicalFlux d g) x /
        radialDenom δ (fun a => naturalCanonicalFlux d g a x) ∂potentialMeasure d.potential) ≤
      4 * (∫ x, χ x ^ 2 * sourceVectorMass d.potential (naturalCanonicalFlux d g) x ∂potentialMeasure d.potential) +
      16 * (1 + c) * (∫ x, χ x ^ 2 * sourceVectorJacobianEnergy Du x ∂potentialMeasure d.potential) +
      16 * (∫ x, sourceVectorMass d.potential (naturalCanonicalFlux d g) x *
        inverseHessianGradientForm d.potential χ x ∂potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let ν := potentialMeasure d.potential
  let u := naturalCanonicalFlux d g
  obtain ⟨c, hc0, hextra⟩ := exists_actual_compact_radial_extra_bound d g Du hcomp (tsupport χ) hc
  refine ⟨c, hc0, ?_⟩
  intro δ hδ
  let f (x : Space n) := radialDenom δ (fun a => u a x)
  let P (x : Space n) := χ x ^ 2 * (sourceConnectionTarget d u x + sourceConnectionGamma d u x) / f x
  let X (x : Space n) := χ x ^ 2 * sourceConnectionCross d u Du x / f x
  let E (x : Space n) := χ x ^ 2 * sourceRadialExtra d u Du x / f x ^ 2
  let B (x : Space n) := χ x * sourceConnectionBoundary d χ u x / f x
  let G (x : Space n) := χ x ^ 2 * sourceConnectionGamma d u x / f x
  let M (x : Space n) := χ x ^ 2 * sourceVectorMass d.potential u x
  let Q (x : Space n) := χ x ^ 2 * sourceVectorJacobianEnergy Du x
  let Z (x : Space n) := sourceVectorMass d.potential u x * inverseHessianGradientForm d.potential χ x
  obtain ⟨hX, hE, hB, hMr, hPr, hG⟩ :=
    actual_compact_radial_connection_fields_integrable d g hδ Du hDu hχ hc
  change Integrable X ν at hX
  change Integrable E ν at hE
  change Integrable B ν at hB
  change Integrable G ν at hG
  have hP : Integrable P ν := by
    apply (hPr.add hG).congr
    exact Eventually.of_forall fun x => by dsimp only [Pi.add_apply, P, G]; ring
  have hχtop : MemLp χ ∞ ν := hχ.continuous.memLp_of_hasCompactSupport hc
  have hχsq : MemLp (fun x => χ x ^ 2) ∞ ν := by
    have hm : MemLp (χ * χ) ∞ ν := hχtop.mul hχtop
    change MemLp (fun x => χ x * χ x) ∞ ν at hm
    simpa only [pow_two] using hm
  have hM : Integrable M ν := hMi.mul_of_top_right hχsq
  have hQ : Integrable Q ν := hQi.mul_of_top_right hχsq
  have hZ : Integrable Z ν := actual_compact_mass_cutoff_integrable d g hMi hχ hc
  have hpoint : ∀ᵐ x ∂ν, (1/4 : ℝ) * G x ≤
      ((P x + X x) - (2 * δ) * E x + 2 * B x) + 4 * (1 + c) * Q x + 4 * Z x := by
    have he := (ae_restrict_iff' hc.measurableSet).mp (hextra δ hδ.le)
    filter_upwards [d.hessian_ae_source, sourceConnectionGamma_nonnegative_ae d u,
      sourceConnectionTarget_nonnegative_ae d u, sourceVectorMass_nonnegative_ae d u,
      sourceVectorJacobianEnergy_nonnegative_ae d Du hcomp,
      sourceConnectionCross_abs_le_ae d u Du hcomp,
      sourceConnectionBoundary_abs_le_ae d u χ, he] with x hp hgn hpn hmn hqn hxn hbn hen
    have hfn : 1 ≤ f x := by
      dsimp only [f, radialDenom]
      exact le_add_of_nonneg_right (mul_nonneg hδ.le (radialSquare_nonnegative _))
    by_cases hx : x ∈ tsupport χ
    · have hxn' : |sourceConnectionCross d u Du x| ≤
          sourceConnectionGamma d u x / 4 + 4 * sourceVectorJacobianEnergy Du x := by
        convert hxn using 1 <;> ring
      have hscalar := radial_connection_absorption_scalar hgn hpn hmn hqn
        (inverseHessianGradientForm_nonneg_at χ hp.1) hc0 hfn hxn' (hen hx)
        (show |2 * (χ x * sourceConnectionBoundary d χ u x)| ≤
          χ x ^ 2 * sourceConnectionGamma d u x / 4 +
            4 * (sourceVectorMass d.potential u x * inverseHessianGradientForm d.potential χ x) from by
          convert hbn using 1 <;> ring)
      convert hscalar using 1 <;> dsimp only [P, X, E, B, G, Q, Z] <;> ring
    · have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      dsimp only [P, X, E, B, G, Q, Z]
      rw [hz]
      simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, zero_div, zero_add,
        add_zero, sub_zero, mul_zero]
      exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
        (mul_nonneg hmn (inverseHessianGradientForm_nonneg_at χ hp.1))
  have hmid : Integrable (fun x => (P x + X x) - (2 * δ) * E x + 2 * B x) ν :=
    ((hP.add hX).sub (hE.const_mul (2 * δ))).add (hB.const_mul 2)
  have hright : Integrable (fun x =>
      (((P x + X x) - (2 * δ) * E x + 2 * B x) + 4 * (1 + c) * Q x) + 4 * Z x) ν :=
    (hmid.add (hQ.const_mul (4 * (1 + c)))).add (hZ.const_mul 4)
  have hcmp := integral_mono_ae (hG.const_mul (1/4 : ℝ)) hright hpoint
  have hBal := actual_compact_radial_connection_balance d g hδ Du hDu hw hχ hc hb
  change (∫ x, P x ∂ν) = (∫ x, χ x ^ 2 * sourceVectorMass d.potential u x / f x ∂ν) -
    (∫ x, X x ∂ν) + (2 * δ) * (∫ x, E x ∂ν) - 2 * (∫ x, B x ∂ν) at hBal
  have hi : (∫ x, (P x + X x) - (2 * δ) * E x + 2 * B x ∂ν) =
      ∫ x, χ x ^ 2 * sourceVectorMass d.potential u x / f x ∂ν := by
    have hPX : Integrable (fun x => P x + X x) ν := hP.add hX
    have hsub : Integrable (fun x => (P x + X x) - (2 * δ) * E x) ν := hPX.sub (hE.const_mul (2 * δ))
    rw [integral_add hsub (hB.const_mul 2),
      integral_sub hPX (hE.const_mul (2 * δ)), integral_add hP hX,
      integral_const_mul, integral_const_mul]
    linarith
  have hmidQ : Integrable (fun x => ((P x + X x) - (2 * δ) * E x + 2 * B x) +
      4 * (1 + c) * Q x) ν := hmid.add (hQ.const_mul (4 * (1 + c)))
  rw [integral_const_mul, integral_add hmidQ (hZ.const_mul 4),
    integral_add hmid (hQ.const_mul (4 * (1 + c))), integral_const_mul, integral_const_mul, hi] at hcmp
  have hmle : (∫ x, χ x ^ 2 * sourceVectorMass d.potential u x / f x ∂ν) ≤ ∫ x, M x ∂ν := by
    apply integral_mono_ae hMr hM
    filter_upwards [sourceVectorMass_nonnegative_ae d u] with x hx
    exact div_le_self (mul_nonneg (sq_nonneg (χ x)) hx)
      (le_add_of_nonneg_right (mul_nonneg hδ.le (radialSquare_nonnegative _)))
  change (∫ x, G x ∂ν) ≤ 4 * (∫ x, M x ∂ν) +
    16 * (1 + c) * (∫ x, Q x ∂ν) + 16 * (∫ x, Z x ∂ν)
  linarith

end KLSConstantImprovement.ActualLocalRadialConnectionAbsorption405
#print axioms KLSConstantImprovement.ActualLocalRadialConnectionAbsorption405.radial_connection_absorption_scalar
#print axioms KLSConstantImprovement.ActualLocalRadialConnectionAbsorption405.actual_uniform_compact_radial_connection_absorption
