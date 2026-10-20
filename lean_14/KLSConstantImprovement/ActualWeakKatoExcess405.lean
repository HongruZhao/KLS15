import KLSConstantImprovement.ActualWeakKatoCompactExcess405
import KLSConstantImprovement.ActualLocalWeakPositivePart405

/-! Close the genuine positive-part test domains internally. The only
subsolution premise is the actual weak Kato inequality; its solution and
cutoff have ordinary raw local-H1 domains. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff BigOperators
namespace KLSConstantImprovement.ActualWeakKatoExcess405
open KLS ActualBoundedCanonicalSource ActualWeakKatoCompactExcess405
open ActualLocalWeakPositivePart405 ActualWeakKatoExcessAlgebra405 ActualSmoothPositivePart405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem compact_excess_of_actual_weak_Kato
    (d : SourceData μ) {w χ : Space n → ℝ} {Dw Dχ : Fin n → Space n → ℝ}
    {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ E, IsCompact E → MemLp w 2 (volume.restrict E))
    (hDw : ∀ i E, IsCompact E → MemLp (Dw i) 2 (volume.restrict E))
    (hww : ∀ i, HasLocalWeakCoordinateDerivative w (Dw i) i)
    (hwn : ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ w x)
    (hweak : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∀ x, 0 ≤ ψ x) →
      (∑ i, ∫ x, rawKatoFlux d Dw i x * coordinateDerivative ψ i x ∂potentialMeasure d.potential) ≤
        ∫ x, (B-w x/2)*ψ x ∂potentialMeasure d.potential)
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hDχ : ∀ i E, IsCompact E → MemLp (Dχ i) ∞ (volume.restrict E))
    (hwχ : ∀ i, HasLocalWeakCoordinateDerivative χ (Dχ i) i)
    (herror : Integrable (fun x => w x^2*rawCutoffSquare d Dχ x) (potentialMeasure d.potential)) :
    Integrable (fun x => χ x^2*max (w x-2*B) 0 ^ 2) (potentialMeasure d.potential) ∧
      (∫ x, χ x^2*max (w x-2*B) 0 ^ 2 ∂potentialMeasure d.potential) ≤
        4*(∫ x, w x^2*rawCutoffSquare d Dχ x ∂potentialMeasure d.potential) := by
  have hs (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => w x-2*B) 2 (volume.restrict E) := by
    letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
    exact (hw E hE).sub (memLp_const (2*B))
  have hws (i : Fin n) : HasLocalWeakCoordinateDerivative (fun x => w x-2*B) (Dw i) i := by
    have hh := (hww i).add (hasLocalWeakCoordinateDerivative_const (-2*B) i)
      (locallyIntegrable_of_memLp_two_on_compacts hw) (locallyIntegrable_const _)
      (locallyIntegrable_of_memLp_two_on_compacts (hDw i)) (locallyIntegrable_const _)
    refine hh.congr_ae (Eventually.of_forall fun x => by ring)
      (Eventually.of_forall fun x => by simp only [add_zero])
  have he (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => max (w x-2*B) 0) 2 (volume.restrict E) := by
    exact (positivePart_raw_local_L2 (F := fun _ => 0) hs (fun _ _ => MemLp.zero') E hE).1
  have hDe (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => excessSlope (w x-2*B)*Dw i x) 2 (volume.restrict E) :=
    (positivePart_raw_local_L2 hs (hDw i) E hE).2
  have hwe (i : Fin n) : HasLocalWeakCoordinateDerivative (fun x => max (w x-2*B) 0)
      (fun x => excessSlope (w x-2*B)*Dw i x) i :=
    local_positivePart_weak_chain hs (hDw i) (hws i)
  exact compact_excess_of_actual_weak_Kato_and_positive_part_domains d hB hw hDw hwn hweak
    hχ hc hDχ hwχ he hDe hwe herror

end KLSConstantImprovement.ActualWeakKatoExcess405
#print axioms KLSConstantImprovement.ActualWeakKatoExcess405.compact_excess_of_actual_weak_Kato
