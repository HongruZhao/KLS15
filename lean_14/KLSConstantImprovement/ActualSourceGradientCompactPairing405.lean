import KLSConstantImprovement.ActualSourceGradientCoefficientPassage405
import KLSConstantImprovement.ActualSourceLimitFluxPairing405

/-! Literal scalar gradients of the actual regularized inverses are
reconstructed from the original-Hessian mass block.  All compact pairings
retain the actual ordered matrix coefficient H_k H^(-1/2). -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceGradientCompactPairing405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyVector405
open ActualSourceRegularizedFluxH1405 ActualSourceRegularizedEnergyForm405
open ActualSourceMetricRegularization405 ActualSourceInverseMetricRegularization405
open ActualSourceGradientCoefficientPassage405 ActualSourceLimitFluxDomains405 ActualSourceLimitFluxPairing405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricOrdinaryGraph
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem regularizedScalarGradient_eq_energy_coefficient_ae (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (D : Fin n → Fin n → Space n → ℝ)
    (W : GaffneyEnergyAmbient d)
    (hW : ∀ a, (W a : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      regularizedGaffneyEnergyField d hn k (cutoffScale_pos k) g D a) (i : Fin n) :
    (weightedH1Derivative d.potential i (regularizedOrdinaryInverse d hn k (cutoffScale_pos k) g) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] fun x =>
        ∑ a : Fin n, (regularizedMetricHessian d k (cutoffScale k) x * canonicalMetricRoot d.potential x) i a *
          W (Sum.inl a) x := by
  have hflux (j : Fin n) := regularizedWeakFlux_eq_energyLimitFlux_ae d hn k (cutoffScale_pos k) g D W hW j
  filter_upwards [ae_all_iff.mpr hflux] with x hx
  let H := regularizedMetricHessian d k (cutoffScale k) x
  let p : Fin n → ℝ := fun a =>
    weightedH1Derivative d.potential a (regularizedOrdinaryInverse d hn k (cutoffScale_pos k) g) x
  have hHu : H *ᵥ (fun j => regularizedWeakFlux d hn k (cutoffScale_pos k) g j x) = p := by
    change H *ᵥ (H⁻¹ *ᵥ p) = p
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp (regularizedMetricHessian_posDef d k (cutoffScale_pos k) x).isUnit),
      Matrix.one_mulVec]
  have hu : (fun j => regularizedWeakFlux d hn k (cutoffScale_pos k) g j x) =
      canonicalMetricRoot d.potential x *ᵥ (fun a => W (Sum.inl a) x) := funext hx
  rw [hu, Matrix.mulVec_mulVec] at hHu
  exact (congrFun hHu i).symm

theorem regularized_gradient_compact_pair_eq_inner_sum (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (D : Fin n → Fin n → Space n → ℝ)
    (W : GaffneyEnergyAmbient d)
    (hW : ∀ a, (W a : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      regularizedGaffneyEnergyField d hn k (cutoffScale_pos k) g D a)
    {ψ : Space n → ℝ} (hc : HasCompactSupport ψ) (i : Fin n)
    (hQ : ∀ a, MemLp (fun x => compactRegularizedGradientCoefficient d (tsupport ψ) i a k x * ψ x)
      2 (potentialMeasure d.potential)) :
    (∫ x, weightedH1Derivative d.potential i (regularizedOrdinaryInverse d hn k (cutoffScale_pos k) g) x * ψ x
      ∂potentialMeasure d.potential) =
      ∑ a : Fin n, inner ℝ (W (Sum.inl a))
        ((hQ a).toLp (fun x => compactRegularizedGradientCoefficient d (tsupport ψ) i a k x * ψ x)) := by
  have hi (a : Fin n) : Integrable (fun x => W (Sum.inl a) x *
      (compactRegularizedGradientCoefficient d (tsupport ψ) i a k x * ψ x)) (potentialMeasure d.potential) :=
    (Lp.memLp _).integrable_mul (hQ a)
  calc
    _ = ∫ x, ∑ a : Fin n, W (Sum.inl a) x *
        (compactRegularizedGradientCoefficient d (tsupport ψ) i a k x * ψ x) ∂potentialMeasure d.potential := by
      apply integral_congr_ae
      filter_upwards [regularizedScalarGradient_eq_energy_coefficient_ae d hn k g D W hW i] with x hx
      rw [hx, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hxψ : x ∈ tsupport ψ
      · rw [compactRegularizedGradientCoefficient, indicator_of_mem hxψ]
        ring
      · simp only [image_eq_zero_of_notMem_tsupport hxψ, mul_zero]
    _ = ∑ a : Fin n, ∫ x, W (Sum.inl a) x *
        (compactRegularizedGradientCoefficient d (tsupport ψ) i a k x * ψ x) ∂potentialMeasure d.potential :=
      integral_finsetSum Finset.univ (fun a _ => hi a)
    _ = _ := Finset.sum_congr rfl fun a _ => integral_lp_mul_eq_inner_toLp _ _

theorem limit_gradient_compact_pair_eq_inner_sum (d : SourceData μ) (V : GaffneyEnergyAmbient d)
    {ψ : Space n → ℝ} (hc : HasCompactSupport ψ) (i : Fin n)
    (hQ : ∀ a, MemLp (fun x => compactActualGradientCoefficient d (tsupport ψ) i a x * ψ x)
      2 (potentialMeasure d.potential)) :
    (∫ x, energyLimitScalarGradient d V i x * ψ x ∂potentialMeasure d.potential) =
      ∑ a : Fin n, inner ℝ (V (Sum.inl a))
        ((hQ a).toLp (fun x => compactActualGradientCoefficient d (tsupport ψ) i a x * ψ x)) := by
  have hi (a : Fin n) : Integrable (fun x => V (Sum.inl a) x *
      (compactActualGradientCoefficient d (tsupport ψ) i a x * ψ x)) (potentialMeasure d.potential) :=
    (Lp.memLp _).integrable_mul (hQ a)
  calc
    _ = ∫ x, ∑ a : Fin n, V (Sum.inl a) x *
        (compactActualGradientCoefficient d (tsupport ψ) i a x * ψ x) ∂potentialMeasure d.potential := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [energyLimitScalarGradient, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        by_cases hxψ : x ∈ tsupport ψ
        · rw [compactActualGradientCoefficient, indicator_of_mem hxψ]
          ring
        · simp only [image_eq_zero_of_notMem_tsupport hxψ, mul_zero]
    _ = ∑ a : Fin n, ∫ x, V (Sum.inl a) x *
        (compactActualGradientCoefficient d (tsupport ψ) i a x * ψ x) ∂potentialMeasure d.potential :=
      integral_finsetSum Finset.univ (fun a _ => hi a)
    _ = _ := Finset.sum_congr rfl fun a _ => integral_lp_mul_eq_inner_toLp _ _

end KLSConstantImprovement.ActualSourceGradientCompactPairing405
#print axioms KLSConstantImprovement.ActualSourceGradientCompactPairing405.regularizedScalarGradient_eq_energy_coefficient_ae
#print axioms KLSConstantImprovement.ActualSourceGradientCompactPairing405.regularized_gradient_compact_pair_eq_inner_sum
#print axioms KLSConstantImprovement.ActualSourceGradientCompactPairing405.limit_gradient_compact_pair_eq_inner_sum
