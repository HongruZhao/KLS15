import KLSConstantImprovement.ActualSourceLimitFluxWeakDerivative405
import KLSConstantImprovement.ActualSourceLimitMetricRelations405

/-! The actual metric limit retains the literal compact divergence
equation.  The equivalent raw inverse-Hessian scalar equation is paid
using the actual symmetric inverse Hessian, not an assumed flux witness. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceLimitDivergence405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyVector405
open ActualSourceRegularizedFluxH1405 ActualSourceRegularizedEnergyForm405
open ActualSourceRegularizedFluxDivergence405 ActualSourceLimitFluxDomains405
open ActualSourceLimitFluxWeakDerivative405 ActualSourceLimitMetricRelations405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem energyLimitFlux_compact_divergence_test (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (D : ℕ → Fin n → Fin n → Space n → ℝ) (W : ℕ → GaffneyEnergyAmbient d)
    (V : GaffneyEnergyAmbient d) (σ : ℕ → ℕ)
    (hW : ∀ k a, (W k a : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      regularizedGaffneyEnergyField d hn k (cutoffScale_pos k) g (D k) a)
    (hw : ∀ Y, Tendsto (fun k => inner ℝ (W (σ k)) Y) atTop (𝓝 (inner ℝ V Y)))
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ j : Fin n, ∫ x, energyLimitFlux d V j x * coordinateDerivative ψ j x
      ∂potentialMeasure d.potential) = ∫ x, g x * ψ x ∂potentialMeasure d.potential := by
  have ht := tendsto_finsetSum Finset.univ (fun j _ =>
    regularizedWeakFlux_compact_pair_tendsto d hn g D W V σ hW hw
      (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) j).continuous
      (hasCompactSupport_coordinateDerivative hc j) j)
  have he (r : ℕ) := regularizedWeakFlux_compact_divergence_test d hn (σ r)
    (cutoffScale_pos (σ r)) g hg hψ hc
  have hr : Tendsto (fun r => ∑ j : Fin n, ∫ x,
      regularizedWeakFlux d hn (σ r) (cutoffScale_pos (σ r)) g j x * coordinateDerivative ψ j x
      ∂potentialMeasure d.potential) atTop (𝓝 (∫ x, g x * ψ x ∂potentialMeasure d.potential)) :=
    tendsto_const_nhds.congr fun r => (he r).symm
  exact tendsto_nhds_unique ht hr

theorem energyLimitScalarGradient_compact_raw_equation (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (D : ℕ → Fin n → Fin n → Space n → ℝ) (W : ℕ → GaffneyEnergyAmbient d)
    (V : GaffneyEnergyAmbient d) (σ : ℕ → ℕ)
    (hW : ∀ k a, (W k a : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      regularizedGaffneyEnergyField d hn k (cutoffScale_pos k) g (D k) a)
    (hw : ∀ Y, Tendsto (fun k => inner ℝ (W (σ k)) Y) atTop (𝓝 (inner ℝ V Y)))
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, ∑ a : Fin n, ∑ b : Fin n, (coordinateHessian d.potential x)⁻¹ a b *
      energyLimitScalarGradient d V a x * coordinateDerivative ψ b x ∂potentialMeasure d.potential) =
      ∫ x, g x * ψ x ∂potentialMeasure d.potential := by
  have hi (j : Fin n) : Integrable (fun x => energyLimitFlux d V j x * coordinateDerivative ψ j x)
      (potentialMeasure d.potential) :=
    integrable_raw_mul_compact_potential d.source_C1.continuous
      (locallyIntegrable_of_memLp_two_on_compacts
        (fun E hE => (energyLimitFlux_Jacobian_local_L2 d V hE).1 j))
      (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) j).continuous
      (hasCompactSupport_coordinateDerivative hc j)
  calc
    _ = ∫ x, ∑ b : Fin n, energyLimitFlux d V b x * coordinateDerivative ψ b x
        ∂potentialMeasure d.potential := by
      apply integral_congr_ae
      filter_upwards [d.hessian_ae_source, ae_all_iff.mpr (energyLimitFlux_eq_inverseGradient_ae d V)] with x hp hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      have hs : ((coordinateHessian d.potential x)⁻¹).IsSymm :=
        (Matrix.isHermitian_iff_isSymm.mp hp.1.isHermitian).inv
      calc
        _ = (∑ a : Fin n, (coordinateHessian d.potential x)⁻¹ b a * energyLimitScalarGradient d V a x) *
            coordinateDerivative ψ b x := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => by rw [hs.apply b a]
        _ = _ := by rw [hx b]
    _ = ∑ b : Fin n, ∫ x, energyLimitFlux d V b x * coordinateDerivative ψ b x
        ∂potentialMeasure d.potential := integral_finsetSum Finset.univ (fun b _ => hi b)
    _ = _ := energyLimitFlux_compact_divergence_test d hn g hg D W V σ hW hw hψ hc

end KLSConstantImprovement.ActualSourceLimitDivergence405
#print axioms KLSConstantImprovement.ActualSourceLimitDivergence405.energyLimitFlux_compact_divergence_test
#print axioms KLSConstantImprovement.ActualSourceLimitDivergence405.energyLimitScalarGradient_compact_raw_equation
