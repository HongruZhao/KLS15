import KLSConstantImprovement.ActualSourceJacobianWeakPassage405
import KLSConstantImprovement.ActualSourceRegularizedFluxDivergence405

/-! The literal metric limit flux has its literal weak Jacobian.  The
passage uses compact first-order tests and the common energy subsequence;
it does not use a compact strong operator core or a connection domain. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceLimitFluxWeakDerivative405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyVector405
open ActualSourceRegularizedFluxH1405 ActualSourceRegularizedEnergyForm405
open ActualSourceLimitFluxDomains405 ActualSourceLimitFluxPairing405
open ActualSourceJacobianWeakPassage405 ActualWeakSourceCompactVectorBochner
open ActualCompactSourceVectorBochner
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem regularizedWeakFlux_compact_pair_tendsto (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : ℕ → Fin n → Fin n → Space n → ℝ) (W : ℕ → GaffneyEnergyAmbient d)
    (V : GaffneyEnergyAmbient d) (σ : ℕ → ℕ)
    (hW : ∀ k a, (W k a : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      regularizedGaffneyEnergyField d hn k (cutoffScale_pos k) g (D k) a)
    (hw : ∀ Y, Tendsto (fun k => inner ℝ (W (σ k)) Y) atTop (𝓝 (inner ℝ V Y)))
    {ψ : Space n → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    Tendsto (fun r => ∫ x, regularizedWeakFlux d hn (σ r) (cutoffScale_pos (σ r)) g i x * ψ x
      ∂potentialMeasure d.potential) atTop
      (𝓝 (∫ x, energyLimitFlux d V i x * ψ x ∂potentialMeasure d.potential)) := by
  have ht := energyLimitFlux_compact_pair_tendsto d hw hψ hc i
  exact ht.congr fun r => integral_congr_ae (by
    filter_upwards [regularizedWeakFlux_eq_energyLimitFlux_ae d hn (σ r)
      (cutoffScale_pos (σ r)) g (D (σ r)) (W (σ r)) (hW (σ r)) i] with x hx
    rw [hx])

theorem energyLimitFlux_source_adjoint_pair (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : ℕ → Fin n → Fin n → Space n → ℝ) (W : ℕ → GaffneyEnergyAmbient d)
    (V : GaffneyEnergyAmbient d) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hW : ∀ k a, (W k a : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      regularizedGaffneyEnergyField d hn k (cutoffScale_pos k) g (D k) a)
    (hDu : ∀ k i j, HasLocalWeakCoordinateDerivative
      (regularizedWeakFlux d hn k (cutoffScale_pos k) g i)
      (regularizedFluxDerivative d hn k (cutoffScale_pos k) g (D k) i j) j)
    {M : ℝ} (hbound : ∀ k, ‖W k‖ ≤ M)
    (hw : ∀ Y, Tendsto (fun k => inner ℝ (W (σ k)) Y) atTop (𝓝 (inner ℝ V Y)))
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (i j : Fin n) :
    (∫ x, energyLimitFlux d V i x * coordinateSourceAdjoint d.potential ψ j x
      ∂potentialMeasure d.potential) =
      ∫ x, energyLimitJacobian d V i j x * ψ x ∂potentialMeasure d.potential := by
  have hφj : Continuous (coordinateDerivative d.potential j) :=
    (contDiff_coordinateDerivative d.source_C1 (m := 0) (by norm_num) j).continuous
  have hψj : Continuous (coordinateDerivative ψ j) :=
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) j).continuous
  have hA : Continuous (coordinateSourceAdjoint d.potential ψ j) := by
    change Continuous (fun x => coordinateDerivative d.potential j x * ψ x - coordinateDerivative ψ j x)
    exact (hφj.mul hψ.continuous).sub hψj
  have hAc : HasCompactSupport (coordinateSourceAdjoint d.potential ψ j) := by
    change HasCompactSupport (fun x => coordinateDerivative d.potential j x * ψ x - coordinateDerivative ψ j x)
    exact hc.mul_left.sub (hasCompactSupport_coordinateDerivative hc j)
  have hfl := regularizedWeakFlux_compact_pair_tendsto d hn g D W V σ hW hw hA hAc i
  have hDl := regularizedFluxDerivative_compact_pair_tendsto d hn g D W V σ hσ hW hbound hw hψ.continuous hc i j
  have heq (r : ℕ) :
      (∫ x, regularizedWeakFlux d hn (σ r) (cutoffScale_pos (σ r)) g i x *
        coordinateSourceAdjoint d.potential ψ j x ∂potentialMeasure d.potential) =
        ∫ x, regularizedFluxDerivative d hn (σ r) (cutoffScale_pos (σ r)) g (D (σ r)) i j x * ψ x
          ∂potentialMeasure d.potential := by
    have ht := compact_source_adjoint_pair_weak d.source_C1 hψ hc (hDu (σ r) i j)
    calc
      _ = ∫ x, coordinateSourceAdjoint d.potential ψ j x *
          regularizedWeakFlux d hn (σ r) (cutoffScale_pos (σ r)) g i x
          ∂potentialMeasure d.potential := integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
      _ = ∫ x, ψ x * regularizedFluxDerivative d hn (σ r) (cutoffScale_pos (σ r)) g (D (σ r)) i j x
          ∂potentialMeasure d.potential := ht
      _ = _ := integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  exact tendsto_nhds_unique hfl (hDl.congr fun r => (heq r).symm)

/-- A compact source-adjoint identity at a C1 weight is an ordinary raw
weak derivative identity.  Exponential tests cancel the weight exactly. -/
theorem raw_weakDerivative_of_source_adjoint_pair {φ u Du : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (i : Fin n)
    (hpair : ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, u x * coordinateSourceAdjoint φ ψ i x ∂potentialMeasure φ) =
        ∫ x, Du x * ψ x ∂potentialMeasure φ) :
    HasLocalWeakCoordinateDerivative u Du i := by
  intro ψ hψ hc
  have he := hpair (fun x => ψ x * Real.exp (φ x)) (hψ.mul hφ.exp) hc.mul_right
  have hA (x : Space n) : coordinateSourceAdjoint φ (fun y => ψ y * Real.exp (φ y)) i x =
      -(Real.exp (φ x) * coordinateDerivative ψ i x) := by
    have hn : coordinateSourceAdjoint φ (fun y => ψ y * Real.exp (φ y)) i x =
        -weightedDerivativeTest φ (fun y => ψ y * Real.exp (φ y)) i x := by
      dsimp only [coordinateSourceAdjoint, weightedDerivativeTest]
      ring
    rw [hn, weightedDerivativeTest_exp_mul hφ hψ]
  have hl : (∫ x, u x * coordinateSourceAdjoint φ (fun y => ψ y * Real.exp (φ y)) i x
      ∂potentialMeasure φ) = -(∫ x, u x * coordinateDerivative ψ i x) := by
    rw [integral_potentialMeasure hφ.continuous.measurable, ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [hA]
      calc
        _ = -(u x * coordinateDerivative ψ i x) * (Real.exp (φ x) * Real.exp (-φ x)) := by ring
        _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hr : (∫ x, Du x * (ψ x * Real.exp (φ x)) ∂potentialMeasure φ) = ∫ x, Du x * ψ x := by
    rw [integral_potentialMeasure hφ.continuous.measurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      calc
        _ = (Du x * ψ x) * (Real.exp (φ x) * Real.exp (-φ x)) := by ring
        _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  rw [hl, hr] at he
  linarith

theorem energyLimitFlux_hasLocalWeakDerivative (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : ℕ → Fin n → Fin n → Space n → ℝ) (W : ℕ → GaffneyEnergyAmbient d)
    (V : GaffneyEnergyAmbient d) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hW : ∀ k a, (W k a : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      regularizedGaffneyEnergyField d hn k (cutoffScale_pos k) g (D k) a)
    (hDu : ∀ k i j, HasLocalWeakCoordinateDerivative
      (regularizedWeakFlux d hn k (cutoffScale_pos k) g i)
      (regularizedFluxDerivative d hn k (cutoffScale_pos k) g (D k) i j) j)
    {M : ℝ} (hbound : ∀ k, ‖W k‖ ≤ M)
    (hw : ∀ Y, Tendsto (fun k => inner ℝ (W (σ k)) Y) atTop (𝓝 (inner ℝ V Y))) (i j : Fin n) :
    HasLocalWeakCoordinateDerivative (energyLimitFlux d V i) (energyLimitJacobian d V i j) j := by
  apply raw_weakDerivative_of_source_adjoint_pair d.source_C1 j
  intro ψ hψ hc
  exact energyLimitFlux_source_adjoint_pair d hn g D W V σ hσ hW hDu hbound hw hψ hc i j

end KLSConstantImprovement.ActualSourceLimitFluxWeakDerivative405
#print axioms KLSConstantImprovement.ActualSourceLimitFluxWeakDerivative405.regularizedWeakFlux_compact_pair_tendsto
#print axioms KLSConstantImprovement.ActualSourceLimitFluxWeakDerivative405.energyLimitFlux_source_adjoint_pair
#print axioms KLSConstantImprovement.ActualSourceLimitFluxWeakDerivative405.raw_weakDerivative_of_source_adjoint_pair
#print axioms KLSConstantImprovement.ActualSourceLimitFluxWeakDerivative405.energyLimitFlux_hasLocalWeakDerivative
