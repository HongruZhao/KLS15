import KLSConstantImprovement.ActualCompactRawExcessTest405
import KLSConstantImprovement.ActualWeakKatoExcessAlgebra405
import KLSConstantImprovement.ActualNaturalCovariantEnergy405

/-! The full uncapped positive-part test gives the compact excess estimate
for the actual inverse Hessian metric. Local raw-H1 positive-part domains
are explicit here and are supplied by the separate weak chain theorem.
There is no mass bound, classical Hessian derivative or boundary limit. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Topology ENNReal ContDiff BigOperators
namespace KLSConstantImprovement.ActualWeakKatoCompactExcess405
open KLS ActualBoundedCanonicalSource ActualSourceHessianEvolution405
open ActualCompactRawExcessTest405 ActualCompactRawSubsolutionTests405 ActualWeakKatoExcessAlgebra405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {n : ℕ} {μ : Measure (Space n)}

def rawKatoFlux (d : SourceData μ) (Dw : Fin n → Space n → ℝ)
    (i : Fin n) (x : Space n) : ℝ :=
  ∑ j : Fin n, (coordinateHessian d.potential x)⁻¹ i j * Dw j x

def rawCutoffSquare (d : SourceData μ) (Dχ : Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  (fun i => Dχ i x) ⬝ᵥ ((coordinateHessian d.potential x)⁻¹ *ᵥ (fun i => Dχ i x))

theorem compact_excess_of_actual_weak_Kato_and_positive_part_domains
    (d : SourceData μ) {w χ : Space n → ℝ} {Dw Dχ : Fin n → Space n → ℝ}
    {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ E, IsCompact E → MemLp w 2 (volume.restrict E))
    (hDw : ∀ i E, IsCompact E → MemLp (Dw i) 2 (volume.restrict E))
    (hwn : ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ w x)
    (hweak : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∀ x, 0 ≤ ψ x) →
      (∑ i, ∫ x, rawKatoFlux d Dw i x * coordinateDerivative ψ i x ∂potentialMeasure d.potential) ≤
        ∫ x, (B-w x/2)*ψ x ∂potentialMeasure d.potential)
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hDχ : ∀ i E, IsCompact E → MemLp (Dχ i) ∞ (volume.restrict E))
    (hwχ : ∀ i, HasLocalWeakCoordinateDerivative χ (Dχ i) i)
    (he : ∀ E, IsCompact E → MemLp (fun x => max (w x-2*B) 0) 2 (volume.restrict E))
    (hDe : ∀ i E, IsCompact E → MemLp (fun x => excessSlope (w x-2*B)*Dw i x) 2 (volume.restrict E))
    (hwe : ∀ i, HasLocalWeakCoordinateDerivative (fun x => max (w x-2*B) 0)
      (fun x => excessSlope (w x-2*B)*Dw i x) i)
    (herror : Integrable (fun x => w x^2*rawCutoffSquare d Dχ x) (potentialMeasure d.potential)) :
    Integrable (fun x => χ x^2*max (w x-2*B) 0 ^ 2) (potentialMeasure d.potential) ∧
      (∫ x, χ x^2*max (w x-2*B) 0 ^ 2 ∂potentialMeasure d.potential) ≤
        4*(∫ x, w x^2*rawCutoffSquare d Dχ x ∂potentialMeasure d.potential) := by
  let e : Space n → ℝ := fun x => max (w x-2*B) 0
  let De : Fin n → Space n → ℝ := fun i x => excessSlope (w x-2*B)*Dw i x
  let f := rawExcessTest χ e
  let F := rawExcessTestDerivative χ e Dχ De
  have htest := rawExcessTest_domains hχ hc hDχ hwχ he hDe hwe
  obtain ⟨hJ, _hDJ, _hwJ⟩ := actual_mongeAmpere_inverse_hasLocalWeakDerivative
    (T := sourceThirdMatrix d) d.source_C1 (d.target_smooth.of_le (by simp))
    d.gradient_lipschitz (d.hessian_ae.mono fun _ hx => hx.2.1)
    d.third_local_L2 d.third_weak_derivative
  have hflux (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (rawKatoFlux d Dw i) 2 (volume.restrict E) :=
    memLp_finsetSum Finset.univ fun j _ => (hJ i j E hE).mul (hDw j E hE)
  have hb (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => B-w x/2) 2 (volume.restrict E) := by
    letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
    have hcB : MemLp (fun _ : Space n => B) 2 (volume.restrict E) := memLp_const B
    have hh := hcB.sub ((hw E hE).const_mul (1/2 : ℝ))
    change MemLp (fun x => B-(1/2 : ℝ)*w x) 2 (volume.restrict E) at hh
    convert hh using 1
    funext x
    ring
  have hnonneg (x : Space n) : 0 ≤ f x := mul_nonneg (sq_nonneg _) (le_max_right _ _)
  obtain ⟨hIF, hbf, hineq⟩ := potential_compact_nonnegative_raw_H1_subsolution_test d
    hflux hb hweak htest.2.1 htest.1 hnonneg htest.2.2.1 htest.2.2.2
  have hEint : Integrable (fun x => χ x^2*e x^2) (potentialMeasure d.potential) := by
    apply (hbf.const_mul (-2)).congr
    exact Eventually.of_forall fun x => by
      have heq := excess_rhs_identity (w x) B (χ x)
      change -2*((B-w x/2)*(χ x^2*e x)) = χ x^2*e x^2
      change (B-w x/2)*(χ x^2*e x) = -(1/2 : ℝ)*(χ x^2*e x^2) at heq
      linarith
  have hbf_eq : (∫ x, (B-w x/2)*f x ∂potentialMeasure d.potential) =
      -(1/2 : ℝ)*(∫ x, χ x^2*e x^2 ∂potentialMeasure d.potential) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => excess_rhs_identity (w x) B (χ x))
  have hL : Integrable (fun x => ∑ i : Fin n, rawKatoFlux d Dw i x*F i x)
      (potentialMeasure d.potential) := integrable_finsetSum Finset.univ fun i _ => hIF i
  have hpoint : ∀ᵐ x ∂potentialMeasure d.potential,
      -(w x^2*rawCutoffSquare d Dχ x) ≤ ∑ i : Fin n, rawKatoFlux d Dw i x*F i x := by
    filter_upwards [d.hessian_ae_source, hwn] with x hH hn
    have hh := full_excess_test_pointwise (coordinateHessian d.potential x)⁻¹ hH.1.inv.posSemidef
      (fun i => Dw i x) (fun i => Dχ i x) hn hB (χ x)
    simpa only [rawCutoffSquare, rawKatoFlux, F, rawExcessTestDerivative, e, De,
      Matrix.mulVec, dotProduct, neg_mul, mul_assoc] using hh
  have hlower := integral_mono_ae herror.neg hL hpoint
  change (∫ x, -(w x^2*rawCutoffSquare d Dχ x) ∂potentialMeasure d.potential) ≤
    ∫ x, ∑ i : Fin n, rawKatoFlux d Dw i x*F i x ∂potentialMeasure d.potential at hlower
  rw [integral_neg, integral_finsetSum _ (fun i _ => hIF i)] at hlower
  change (∑ i, ∫ x, rawKatoFlux d Dw i x*F i x ∂potentialMeasure d.potential) ≤
    ∫ x, (B-w x/2)*f x ∂potentialMeasure d.potential at hineq
  rw [hbf_eq] at hineq
  have herror_nonneg : 0 ≤ ∫ x, w x^2*rawCutoffSquare d Dχ x ∂potentialMeasure d.potential := by
    apply integral_nonneg_of_ae
    filter_upwards [d.hessian_ae_source] with x hH
    have hn : 0 ≤ rawCutoffSquare d Dχ x := by
      change 0 ≤ (fun i => Dχ i x) ⬝ᵥ ((coordinateHessian d.potential x)⁻¹ *ᵥ (fun i => Dχ i x))
      simpa only [star_trivial] using hH.1.inv.posSemidef.dotProduct_mulVec_nonneg (fun i => Dχ i x)
    exact mul_nonneg (sq_nonneg _) hn
  refine ⟨hEint, ?_⟩
  linarith

end KLSConstantImprovement.ActualWeakKatoCompactExcess405
#print axioms KLSConstantImprovement.ActualWeakKatoCompactExcess405.compact_excess_of_actual_weak_Kato_and_positive_part_domains
