import KLSConstantImprovement.ActualSourceJointWeakLimit405
import KLSConstantImprovement.ActualWhitenedJacobianSymmetry405
import KLSConstantImprovement.ActualFiniteFamilyWeakPassage405

/-! Literal symmetry of the actual energy-limit Jacobian block follows
from weak coordinate equality. No coefficient derivative product is used. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceLimitJacobianSymmetry405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyVector405
open ActualSourceMetricRegularization405 ActualSourceRegularizedEnergyForm405
open ActualSourceRegularizedFluxH1405 ActualSourceRegularizedFluxCompatibility405
open ActualWhitenedJacobianEnergy405 ActualWhitenedJacobianSymmetry405 ActualFiniteFamilyWeakPassage405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def energyLimitWhitenedJacobian (d : SourceData μ) (V : GaffneyEnergyAmbient d) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => V (Sum.inr (i, j)) x

theorem energy_weak_limit_jacobian_coordinates_eq (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : ℕ → Fin n → Fin n → Space n → ℝ) (W : ℕ → GaffneyEnergyAmbient d)
    (V : GaffneyEnergyAmbient d) (σ : ℕ → ℕ)
    (hc : ∀ k, ∀ᵐ x ∂(volume : Measure (Space n)),
      (regularizedMetricHessian d k (cutoffScale k) x *
        regularizedFluxJacobian d hn k (cutoffScale_pos k) g (D k) x).IsSymm)
    (hW : ∀ k a, (W k a : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      regularizedGaffneyEnergyField d hn k (cutoffScale_pos k) g (D k) a)
    (hw : ∀ Y, Tendsto (fun k => inner ℝ (W (σ k)) Y) atTop (𝓝 (inner ℝ V Y)))
    (i j : Fin n) : V (Sum.inr (i, j)) = V (Sum.inr (j, i)) := by
  apply finite_family_coordinate_eq_of_weak_limit hw (Sum.inr (i, j)) (Sum.inr (j, i))
  intro r
  apply Lp.ext
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [hW (σ r) (Sum.inr (i, j)), hW (σ r) (Sum.inr (j, i)),
    (hc (σ r)).filter_mono hac.ae_le] with x hx hy hsym
  rw [hx, hy]
  exact (whitenedJacobian_isSymm (regularizedMetricHessian d (σ r) (cutoffScale (σ r)) x)
    (regularizedFluxJacobian d hn (σ r) (cutoffScale_pos (σ r)) g (D (σ r)) x)
    (regularizedMetricHessian_posDef d (σ r) (cutoffScale_pos (σ r)) x) hsym).apply j i

theorem energyLimitWhitenedJacobian_isSymm_ae (d : SourceData μ) (V : GaffneyEnergyAmbient d)
    (heq : ∀ i j, V (Sum.inr (i, j)) = V (Sum.inr (j, i))) :
    ∀ᵐ x ∂(volume : Measure (Space n)), (energyLimitWhitenedJacobian d V x).IsSymm := by
  have hν (i j : Fin n) : (V (Sum.inr (i, j)) : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      (V (Sum.inr (j, i)) : Space n → ℝ) := by rw [heq i j]
  have hv (i j : Fin n) := (volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous).ae_eq (hν i j)
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hv i j))] with x hx
  exact Matrix.IsSymm.ext fun i j => hx j i

end KLSConstantImprovement.ActualSourceLimitJacobianSymmetry405
#print axioms KLSConstantImprovement.ActualSourceLimitJacobianSymmetry405.energy_weak_limit_jacobian_coordinates_eq
#print axioms KLSConstantImprovement.ActualSourceLimitJacobianSymmetry405.energyLimitWhitenedJacobian_isSymm_ae
