import KLSConstantImprovement.ActualSourceJacobianCompactPairing405
import KLSConstantImprovement.ActualHilbertWeakPassage405
import KLSConstantImprovement.ActualFiniteFamilyWeakPassage405

/-! Genuine compact pairings of the actual regularized Jacobian pass to
the literal original-metric Jacobian by weak/strong L2 pairing. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceJacobianWeakPassage405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyVector405
open ActualSourceRegularizedFluxH1405 ActualSourceRegularizedRootMultipliers405
open ActualSourceLimitFluxDomains405 ActualSourceJacobianCompactPairing405
open ActualHilbertWeakPassage405 ActualFiniteFamilyWeakPassage405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem regularizedFluxDerivative_compact_pair_tendsto (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : ℕ → Fin n → Fin n → Space n → ℝ) (W : ℕ → GaffneyEnergyAmbient d)
    (V : GaffneyEnergyAmbient d) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hW : ∀ k a, (W k a : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      regularizedGaffneyEnergyField d hn k (cutoffScale_pos k) g (D k) a)
    {M : ℝ} (hbound : ∀ k, ‖W k‖ ≤ M)
    (hw : ∀ Y, Tendsto (fun k => inner ℝ (W (σ k)) Y) atTop (𝓝 (inner ℝ V Y)))
    {ψ : Space n → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (i j : Fin n) :
    Tendsto (fun r => ∫ x, regularizedFluxDerivative d hn (σ r) (cutoffScale_pos (σ r)) g (D (σ r)) i j x * ψ x
      ∂potentialMeasure d.potential) atTop
      (𝓝 (∫ x, energyLimitJacobian d V i j x * ψ x ∂potentialMeasure d.potential)) := by
  have hψ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ hc
  have hQ (a b : Fin n) := compact_root_product_mul_tendsto_L2 d hc i a b j hψ2
  choose hp hl ht using hQ
  have hpair (a b : Fin n) :
      Tendsto (fun r => inner ℝ (W (σ r) (Sum.inr (a, b)))
        ((hp a b (σ r)).toLp (fun x => compactRegularizedRootProduct d (tsupport ψ) i a b j (σ r) x * ψ x))) atTop
      (𝓝 (inner ℝ (V (Sum.inr (a, b)))
        ((hl a b).toLp (fun x => compactActualRootProduct d (tsupport ψ) i a b j x * ψ x)))) := by
    have hb (r : ℕ) : ‖W (σ r) (Sum.inr (a, b))‖ ≤ M :=
      (PiLp.norm_apply_le (W (σ r)) (Sum.inr (a, b))).trans (hbound (σ r))
    exact inner_tendsto_of_weak_and_strong hb
      (fun Y => finite_family_weak_coordinate_tendsto hw (Sum.inr (a, b)) Y)
      ((ht a b).comp hσ.tendsto_atTop)
  have hlim := tendsto_finsetSum Finset.univ (fun a _ =>
    tendsto_finsetSum Finset.univ (fun b _ => hpair a b))
  rw [limit_jacobian_compact_pair_eq_inner_sum d V hc i j hl]
  exact hlim.congr fun r =>
    (regularized_jacobian_compact_pair_eq_inner_sum d hn (σ r) g (D (σ r)) (W (σ r))
      (hW (σ r)) hc i j (fun a b => hp a b (σ r))).symm

end KLSConstantImprovement.ActualSourceJacobianWeakPassage405
#print axioms KLSConstantImprovement.ActualSourceJacobianWeakPassage405.regularizedFluxDerivative_compact_pair_tendsto
