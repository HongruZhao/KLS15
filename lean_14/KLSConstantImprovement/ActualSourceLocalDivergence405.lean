import KLSConstantImprovement.ActualLocalWeakDivergenceProduct405
import KLSConstantImprovement.ActualBoundedCanonicalSource

/-! Local weak divergence equations on the actual source weight, with
their genuine domains retained through bounded-H1 multiplication and
finite sums. Actual constructors, rather than an assumed production
equation, will supply the response and Hessian equations. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualSourceLocalDivergence405
open KLS ActualBoundedCanonicalSource ActualLocalBoundedWeakAlgebra405
open ActualLocalWeakDivergenceProduct405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ} {μ : Measure (Space n)}

structure SourceLocalDivergence (d : SourceData μ) where
  flux : Fin n → Space n → ℝ
  drift : Space n → ℝ
  flux_local : ∀ a E, IsCompact E → MemLp (flux a) 2 (volume.restrict E)
  drift_local : LocallyIntegrable drift volume
  identity : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
    (∑ a, ∫ x, flux a x * coordinateDerivative ψ a x ∂potentialMeasure d.potential) =
      ∫ x, drift x * ψ x ∂potentialMeasure d.potential

namespace SourceLocalDivergence
variable {d : SourceData μ}

def mulLocal (e : SourceLocalDivergence d) (f : LocalRawTest n) : SourceLocalDivergence d where
  flux := fun a x => f.value x * e.flux a x
  drift := fun x => f.value x * e.drift x - ∑ a, e.flux a x * f.derivative a x
  flux_local := fun a E hE => (f.value_local_top E hE).mul (e.flux_local a E hE)
  drift_local := (localRawTest_mul_locallyIntegrable f e.drift_local).sub
    (locallyIntegrable_finsetSum Finset.univ fun a _ =>
      locallyIntegrable_product_of_localL2 (e.flux_local a) (f.derivative_local a))
  identity := by
    intro ψ hψ hc
    let ρ : Space n → ℝ := fun x => Real.exp (-d.potential x)
    have hρ : Continuous ρ := Real.continuous_exp.comp d.source_C1.continuous.neg
    have hA (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
        MemLp (fun x => ρ x * e.flux a x) 2 (volume.restrict E) :=
      memLp_continuous_mul_on_compact hE (e.flux_local a E hE) hρ
    have he := divergence_mul_localRawTest hA (e.drift_local.continuous_mul hρ)
      (fun θ hθ hθc => by
        have ht := e.identity θ hθ hθc
        simp_rw [integral_potentialMeasure d.source_C1.continuous.measurable] at ht
        simpa only [ρ, mul_assoc, mul_left_comm, mul_comm] using ht)
      f (hψ.of_le (by norm_num)) hc
    have hl : (∑ a, ∫ x, (f.value x * e.flux a x) * coordinateDerivative ψ a x
        ∂potentialMeasure d.potential) =
        ∑ a, ∫ x, (f.value x * (ρ x * e.flux a x)) * coordinateDerivative ψ a x := by
      apply Finset.sum_congr rfl
      intro a _
      rw [integral_potentialMeasure d.source_C1.continuous.measurable]
      exact integral_congr_ae (Eventually.of_forall fun x => by dsimp only [ρ]; ring)
    have hr : (∫ x, (f.value x * (ρ x * e.drift x) -
        ∑ a, (ρ x * e.flux a x) * f.derivative a x) * ψ x) =
        ∫ x, (f.value x * e.drift x - ∑ a, e.flux a x * f.derivative a x) * ψ x
          ∂potentialMeasure d.potential := by
      rw [integral_potentialMeasure d.source_C1.continuous.measurable]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        have hs : (∑ a, (ρ x * e.flux a x) * f.derivative a x) =
            ρ x * ∑ a, e.flux a x * f.derivative a x := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
        change (f.value x * (ρ x * e.drift x) -
          ∑ a, (ρ x * e.flux a x) * f.derivative a x) * ψ x =
          (f.value x * e.drift x - ∑ a, e.flux a x * f.derivative a x) * ψ x *
            Real.exp (-d.potential x)
        rw [hs]
        dsimp only [ρ]
        ring
    exact hl.trans (he.trans hr)

end SourceLocalDivergence

def sourceLocalDivergenceSum {ι : Type*} [Fintype ι] {d : SourceData μ}
    (e : ι → SourceLocalDivergence d) : SourceLocalDivergence d where
  flux := fun a x => ∑ i, (e i).flux a x
  drift := fun x => ∑ i, (e i).drift x
  flux_local := fun a E hE => memLp_finsetSum Finset.univ fun i _ => (e i).flux_local a E hE
  drift_local := locallyIntegrable_finsetSum Finset.univ fun i _ => (e i).drift_local
  identity := by
    intro ψ hψ hc
    have hF (i : ι) (a : Fin n) : Integrable (fun x => (e i).flux a x * coordinateDerivative ψ a x)
        (potentialMeasure d.potential) :=
      integrable_raw_mul_compact_potential d.source_C1.continuous
        (locallyIntegrable_of_memLp_two_on_compacts ((e i).flux_local a))
        (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) a).continuous
        (hasCompactSupport_coordinateDerivative hc a)
    have hB (i : ι) : Integrable (fun x => (e i).drift x * ψ x) (potentialMeasure d.potential) :=
      integrable_raw_mul_compact_potential d.source_C1.continuous (e i).drift_local hψ.continuous hc
    have hl (a : Fin n) : (∫ x, (∑ i : ι, (e i).flux a x) * coordinateDerivative ψ a x
        ∂potentialMeasure d.potential) =
        ∑ i : ι, ∫ x, (e i).flux a x * coordinateDerivative ψ a x ∂potentialMeasure d.potential := by
      simp only [Finset.sum_mul]
      exact integral_finsetSum Finset.univ fun i _ => hF i a
    have hr : (∫ x, (∑ i : ι, (e i).drift x) * ψ x ∂potentialMeasure d.potential) =
        ∑ i : ι, ∫ x, (e i).drift x * ψ x ∂potentialMeasure d.potential := by
      simp only [Finset.sum_mul]
      exact integral_finsetSum Finset.univ fun i _ => hB i
    simp_rw [hl]
    rw [hr, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (e i).identity ψ hψ hc

end KLSConstantImprovement.ActualSourceLocalDivergence405

#print axioms KLSConstantImprovement.ActualSourceLocalDivergence405.SourceLocalDivergence.mulLocal
#print axioms KLSConstantImprovement.ActualSourceLocalDivergence405.sourceLocalDivergenceSum
