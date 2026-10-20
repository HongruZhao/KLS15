import KLSConstantImprovement.ActualWeakCanonicalMetricOrdinaryGraph
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Constructed scalar response on the actual canonical source

For an actual L2 source vector e, its scalar response is constructed by
Lax--Milgram from the concrete functional `E e dot grad_source psi`.
The source metric, weak gradient, inverse, measure and mean all come from
the same constructed canonical source. The response's adjoint/Riesz action
is a conclusion. This is an operator construction, not a numerical charge
certificate or a conditional raw405 wrapper.
-/

open MeasureTheory InnerProductSpace
open scoped BigOperators ContDiff RealInnerProductSpace

noncomputable section
namespace KLSConstantImprovement.ActualWeakCanonicalMetricResponse

open KLS
open KLSConstantImprovement.ActualBoundedCanonicalSource
open KLSConstantImprovement.ActualCanonicalMetricEnergyGraph
open KLSConstantImprovement.ActualWeakCanonicalMetricInverse
open KLSConstantImprovement.ActualWeakCanonicalMetricOrdinaryGraph
variable {n : ℕ} {μ : Measure (Space n)}

/-- The genuine source weak-gradient functional, using the proved ordinary
H1 embedding of the same metric graph value. -/
def sourceResponseFunctional (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) :
    CanonicalMetricH1 d.potential →L[ℝ] ℝ :=
  ∑ i : Fin n, (innerSL ℝ (e i)).comp
    ((weightedH1Derivative d.potential i).comp (sourceOrdinaryH1Embedding d))

theorem sourceResponseFunctional_apply (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) (U : CanonicalMetricH1 d.potential) :
    sourceResponseFunctional d e U =
      ∑ i : Fin n, inner ℝ (e i)
        (weightedH1Derivative d.potential i (sourceOrdinaryH1Embedding d U)) := by
  simp [sourceResponseFunctional]

/-- The actual variational response potential. -/
def sourceResponseH1 (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) : CanonicalMetricH1 d.potential :=
  (sourceMetricEnergy_isCoercive d).continuousLinearEquivOfBilin.symm
    ((InnerProductSpace.toDual ℝ (CanonicalMetricH1 d.potential)).symm
      (sourceResponseFunctional d e))

/-- The actual centered L2 scalar response, usually denoted f_e. -/
def sourceResponse (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) : Lp ℝ 2 (potentialMeasure d.potential) :=
  canonicalMetricValue d.potential (sourceResponseH1 d e)

theorem sourceResponse_variational (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) (V : CanonicalMetricH1 d.potential) :
    canonicalMetricEnergy d.potential (sourceResponseH1 d e) V =
      sourceResponseFunctional d e V := by
  let hc := sourceMetricEnergy_isCoercive d
  rw [← hc.continuousLinearEquivOfBilin_apply]
  change inner ℝ (hc.continuousLinearEquivOfBilin
    (hc.continuousLinearEquivOfBilin.symm
      ((InnerProductSpace.toDual ℝ (CanonicalMetricH1 d.potential)).symm
        (sourceResponseFunctional d e)))) V = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact InnerProductSpace.toDual_symm_apply

theorem sourceResponse_unique (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) {U : CanonicalMetricH1 d.potential}
    (hU : ∀ V, canonicalMetricEnergy d.potential U V = sourceResponseFunctional d e V) :
    U = sourceResponseH1 d e := by
  let hc := sourceMetricEnergy_isCoercive d
  have he : (InnerProductSpace.toDual ℝ (CanonicalMetricH1 d.potential)).symm
      (sourceResponseFunctional d e) = hc.continuousLinearEquivOfBilin U := by
    apply hc.unique_continuousLinearEquivOfBilin
    intro V
    rw [InnerProductSpace.toDual_symm_apply]
    exact (hU V).symm
  calc
    U = hc.continuousLinearEquivOfBilin.symm (hc.continuousLinearEquivOfBilin U) :=
      (hc.continuousLinearEquivOfBilin.symm_apply_apply U).symm
    _ = hc.continuousLinearEquivOfBilin.symm
        ((InnerProductSpace.toDual ℝ (CanonicalMetricH1 d.potential)).symm
          (sourceResponseFunctional d e)) := by rw [he]
    _ = sourceResponseH1 d e := rfl

theorem existsUnique_sourceResponse (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) :
    ∃! U : CanonicalMetricH1 d.potential, ∀ V,
      canonicalMetricEnergy d.potential U V = sourceResponseFunctional d e V :=
  ⟨sourceResponseH1 d e, sourceResponse_variational d e,
    fun _ hU => sourceResponse_unique d e hU⟩

theorem sourceResponse_integral_eq_zero (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) :
    (∫ x, sourceResponse d e x ∂potentialMeasure d.potential) = 0 := by
  letI := d.source_probability
  exact canonicalMetricValue_integral_eq_zero d.source_C1.continuous _

/-- The response is the actual L2 Riesz representative of the same
canonical inverse followed by the ordinary source-gradient pairing. -/
theorem sourceResponse_adjoint_identity (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential))
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    inner ℝ (sourceResponse d e) g =
      ∑ i : Fin n, inner ℝ (e i)
        (weightedH1Derivative d.potential i
          (sourceOrdinaryH1Embedding d (sourceMetricInverseH1 d g))) := by
  have hf := sourceResponse_variational d e (sourceMetricInverseH1 d g)
  have hg := sourceMetricInverse_variational d g (sourceResponseH1 d e)
  rw [canonicalMetricEnergy_symm] at hg
  rw [real_inner_comm g (sourceResponse d e)]
  exact hg.symm.trans (hf.trans (sourceResponseFunctional_apply d e _))

/-- In particular the norm of f_e is paired against its own canonical
Poisson response, rather than an unrelated test or kernel. -/
theorem sourceResponse_norm_identity (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) :
    ‖sourceResponse d e‖ ^ 2 =
      ∑ i : Fin n, inner ℝ (e i)
        (weightedH1Derivative d.potential i
          (sourceOrdinaryH1Embedding d (sourceMetricInverseH1 d (sourceResponse d e)))) := by
  simpa only [real_inner_self_eq_norm_sq] using
    sourceResponse_adjoint_identity d e (sourceResponse d e)

end KLSConstantImprovement.ActualWeakCanonicalMetricResponse
end

#print axioms KLSConstantImprovement.ActualWeakCanonicalMetricResponse.existsUnique_sourceResponse
#print axioms KLSConstantImprovement.ActualWeakCanonicalMetricResponse.sourceResponse_adjoint_identity
#print axioms KLSConstantImprovement.ActualWeakCanonicalMetricResponse.sourceResponse_norm_identity
