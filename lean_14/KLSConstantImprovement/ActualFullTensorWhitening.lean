import KLSConstantImprovement.ActualFullSymmetricTensorOrdering
import KLSConstantImprovement.ActualBoundedCanonicalSource
import KLS.MatrixInverseSqrtLipschitz

/-! Actual three-slot whitening preserves the concrete tensor ordering on
the constructed weak canonical source. No whitening/symmetry/order witness
is supplied; the source itself is constructed for bounded strong targets. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualFullTensorWhitening
open KLS ActualBoundedCanonicalSource ActualFullSymmetricTensorOrdering
open MixedCubicRankSlicing
variable {ι : Type*} [Fintype ι]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def threeSlotAction (Q : Matrix ι ι ℝ) (N : ι → ι → ι → ℝ) : ι → ι → ι → ℝ :=
  fun i j k => ∑ a, ∑ b, ∑ c, Q i a * Q j b * Q k c * N a b c

private theorem sum3_cycle (f : ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, f b c a) = ∑ a, ∑ b, ∑ c, f a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.sum_comm

theorem threeSlotAction_preserves_cyclic (Q : Matrix ι ι ℝ)
    (N : ι → ι → ι → ℝ) (hN : ∀ i j k, N i j k = N j k i) (i j k : ι) :
    threeSlotAction Q N i j k = threeSlotAction Q N j k i := by
  unfold threeSlotAction
  calc
    _ = ∑ a, ∑ b, ∑ c, Q j b * Q k c * Q i a * N b c a := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [← hN a b c]
      ring
    _ = _ := sum3_cycle (fun a b c => Q j a * Q k b * Q i c * N a b c)

variable {n : ℕ}

def whitenedSourceThird {μ : Measure (Space n)} (d : SourceData μ) (x : Space n) :
    Fin n → Fin n → Fin n → ℝ :=
  threeSlotAction (inverseSqrtMatrix (coordinateHessian d.potential x)) (d.third x)

theorem source_whitened_third_cyclic_ae {μ : Measure (Space n)} (d : SourceData μ) :
    ∀ᵐ x ∂potentialMeasure d.potential, ∀ i j k,
      whitenedSourceThird d x i j k = whitenedSourceThird d x j k i := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  have hs := d.third_symmetric_ae.filter_mono hac.ae_le
  filter_upwards [hs] with x hx
  intro i j k
  exact threeSlotAction_preserves_cyclic _ _
    (fun a b c => ((hx a b c).1).trans ((hx b a c).2)) i j k

theorem source_whitened_tensor_ordering_ae {μ : Measure (Space n)} (d : SourceData μ)
    (B : Space n → Matrix (Fin n) (Fin n) ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      2 * (cubicEnergy (firstAction (B x) (whitenedSourceThird d x)) -
        cubicEnergy (firstAction (B x).transpose (whitenedSourceThird d x))) =
      3 * (cubicEnergy (hook (firstAction (B x) (whitenedSourceThird d x))) -
        cubicEnergy (hook (firstAction (B x).transpose (whitenedSourceThird d x)))) := by
  filter_upwards [source_whitened_third_cyclic_ae d] with x hx
  exact actual_full_tensor_hook_ordering (B x) (whitenedSourceThird d x) hx

theorem exists_actual_source_with_tensor_ordering {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (hreg : HasSmoothBoundedStronglyConvexDensity μ) :
    ∃ d : SourceData μ, ∀ B : Space n → Matrix (Fin n) (Fin n) ℝ,
      ∀ᵐ x ∂potentialMeasure d.potential,
        2 * (cubicEnergy (firstAction (B x) (whitenedSourceThird d x)) -
          cubicEnergy (firstAction (B x).transpose (whitenedSourceThird d x))) =
        3 * (cubicEnergy (hook (firstAction (B x) (whitenedSourceThird d x))) -
          cubicEnergy (hook (firstAction (B x).transpose (whitenedSourceThird d x)))) := by
  obtain ⟨d⟩ := exists_sourceData hμ hreg
  exact ⟨d, source_whitened_tensor_ordering_ae d⟩

end KLSConstantImprovement.ActualFullTensorWhitening
#print axioms KLSConstantImprovement.ActualFullTensorWhitening.threeSlotAction_preserves_cyclic
#print axioms KLSConstantImprovement.ActualFullTensorWhitening.source_whitened_third_cyclic_ae
#print axioms KLSConstantImprovement.ActualFullTensorWhitening.source_whitened_tensor_ordering_ae
#print axioms KLSConstantImprovement.ActualFullTensorWhitening.exists_actual_source_with_tensor_ordering
