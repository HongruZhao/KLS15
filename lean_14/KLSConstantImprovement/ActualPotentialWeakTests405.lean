import KLSConstantImprovement.ActualLocalDivergenceTests405

/-! Bounded compact raw H1 tests on the original source weight. All
integrability and approximation passages are proved with its actual
density, without changing measure or postulating a graph core. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualPotentialWeakTests405
open KLS ActualBoundedCanonicalSource ActualLocalDivergenceTests405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem potential_divergence_bounded_compact_H1_test (d : SourceData μ)
    {A : Fin n → Space n → ℝ} {b f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hA : ∀ i E, IsCompact E → MemLp (A i) 2 (volume.restrict E))
    (hb : ∀ E, IsCompact E → MemLp b 2 (volume.restrict E))
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∑ i, ∫ x, A i x * coordinateDerivative ψ i x ∂potentialMeasure d.potential) =
        ∫ x, b x * ψ x ∂potentialMeasure d.potential)
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E))
    (hc : HasCompactSupport f) {B : ℝ} (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ B)
    (hFloc : ∀ i E, IsCompact E → MemLp (F i) 2 (volume.restrict E))
    (hF : ∀ i, HasLocalWeakCoordinateDerivative f (F i) i) :
    (∀ i, Integrable (fun x => A i x * F i x) (potentialMeasure d.potential)) ∧
      Integrable (fun x => b x * f x) (potentialMeasure d.potential) ∧
      (∑ i, ∫ x, A i x * F i x ∂potentialMeasure d.potential) =
        ∫ x, b x * f x ∂potentialMeasure d.potential := by
  have hρ : Continuous (fun x => Real.exp (-d.potential x)) :=
    Real.continuous_exp.comp d.source_C1.continuous.neg
  have hρA (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => Real.exp (-d.potential x) * A i x) 2 (volume.restrict E) :=
    memLp_continuous_mul_on_compact hE (hA i E hE) hρ
  have hρb (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => Real.exp (-d.potential x) * b x) 2 (volume.restrict E) :=
    memLp_continuous_mul_on_compact hE (hb E hE) hρ
  have he := integral_divergence_of_C3_bounded_compact_H1_test hρA
    (locallyIntegrable_of_memLp_two_on_compacts hρb) (fun ψ hψ hψc => by
      have ht := hdiv ψ hψ hψc
      simp_rw [integral_potentialMeasure d.source_C1.continuous.measurable] at ht
      simpa only [mul_assoc, mul_left_comm, mul_comm] using ht)
    hf hc hbound hFloc hF
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply (integrable_potentialMeasure_iff d.source_C1.continuous.measurable).mpr
    exact (he.1 i).congr (Eventually.of_forall fun x => by dsimp only; ring)
  · apply (integrable_potentialMeasure_iff d.source_C1.continuous.measurable).mpr
    exact he.2.1.congr (Eventually.of_forall fun x => by dsimp only; ring)
  · simp_rw [integral_potentialMeasure d.source_C1.continuous.measurable]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using he.2.2

end KLSConstantImprovement.ActualPotentialWeakTests405

#print axioms KLSConstantImprovement.ActualPotentialWeakTests405.potential_divergence_bounded_compact_H1_test
