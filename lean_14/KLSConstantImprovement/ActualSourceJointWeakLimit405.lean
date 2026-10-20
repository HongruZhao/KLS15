import KLSConstantImprovement.ActualSourceRegularizedEnergyVector405
import KLSConstantImprovement.ActualSourceRegularizedWeakCompactness405

/-!
A common actual metric-regularization subsequence for scalar inverse and
the combined flux/Jacobian energy field. The energy block retains forcing
constant one. Its first block uses the original source Hessian, while the
Jacobian block uses the actual smooth metric conjugation.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceJointWeakLimit405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyForm405
open ActualSourceRegularizedFluxH1405 ActualSourceRegularizedEnergyVector405
open ActualSourceRegularizedWeakCompactness405
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_actual_regularized_joint_weak_limit (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) :
    ∃ (D : ℕ → Fin n → Fin n → Space n → ℝ)
      (W : ℕ → GaffneyEnergyAmbient d) (U : WeightedCenteredH1 d.potential)
      (V : GaffneyEnergyAmbient d) (σ : ℕ → ℕ),
      StrictMono σ ∧ ‖V‖ ≤ ‖g‖ ∧
      (∀ k i j, MemLp (regularizedFluxDerivative d hn k (cutoffScale_pos k) g (D k) i j)
        2 (potentialMeasure d.potential)) ∧
      (∀ k i j, HasLocalWeakCoordinateDerivative (regularizedWeakFlux d hn k (cutoffScale_pos k) g i)
        (regularizedFluxDerivative d hn k (cutoffScale_pos k) g (D k) i j) j) ∧
      (∀ k, ∀ᵐ x ∂(volume : Measure (Space n)),
        (ActualSourceMetricRegularization405.regularizedMetricHessian d k (cutoffScale k) x *
          ActualSourceRegularizedFluxCompatibility405.regularizedFluxJacobian d hn k (cutoffScale_pos k) g (D k) x).IsSymm) ∧
      (∀ k, ‖W k‖ ^ 2 = ‖g‖ ^ 2) ∧
      (∀ k a, (W k a : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
        regularizedGaffneyEnergyField d hn k (cutoffScale_pos k) g (D k) a) ∧
      (∀ L : WeightedCenteredH1 d.potential →L[ℝ] ℝ,
        Tendsto (fun r => L (regularizedOrdinaryInverse d hn (σ r) (cutoffScale_pos (σ r)) g))
          atTop (𝓝 (L U))) ∧
      (∀ Y : GaffneyEnergyAmbient d,
        Tendsto (fun r => inner ℝ (W (σ r)) Y) atTop (𝓝 (inner ℝ V Y))) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  letI : TopologicalSpace.SeparableSpace (Lp ℝ 2 (potentialMeasure d.potential)) := inferInstance
  letI : TopologicalSpace.SeparableSpace (GaffneyEnergyAmbient d) := inferInstance
  have hE (k : ℕ) := exists_actual_regularizedGaffney_energyVector d hn k (cutoffScale_pos k) g hg
  choose D W hDu hw hc hW hnorm using hE
  obtain ⟨K, U, τ, _, hτ, _, hU⟩ := exists_regularizedOrdinaryInverse_weak_subsequence d hn g
  have hb (r : ℕ) : ‖W (τ r)‖ ≤ ‖g‖ := by
    have hh := hnorm (τ r)
    nlinarith [norm_nonneg (W (τ r)), norm_nonneg g]
  obtain ⟨V, ρ, hρ, hV, hweak⟩ := exists_weak_limit_of_bounded_hilbert hb
  refine ⟨D, W, U, V, τ ∘ ρ, hτ.comp hρ, hV, hDu, hw, hc, hnorm, hW, ?_, ?_⟩
  · intro L
    exact (hU L).comp hρ.tendsto_atTop
  · intro Y
    exact hweak Y

end KLSConstantImprovement.ActualSourceJointWeakLimit405
#print axioms KLSConstantImprovement.ActualSourceJointWeakLimit405.exists_actual_regularized_joint_weak_limit
