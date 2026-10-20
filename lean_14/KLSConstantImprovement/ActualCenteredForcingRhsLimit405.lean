import KLSConstantImprovement.ActualCompactTargetExtensions405
import KLSConstantImprovement.ActualDensityGradientCoefficient405

/-! Compact weak-equation right-hand sides converge for the actual
centered target forcing on the same centered source family.  A common
global potential lower bound is constructed from centering and convergence
at zero, and pays an explicit Lebesgue dominated-convergence passage. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualCenteredForcingRhsLimit405
open KLS ActualBoundedCanonicalSource ActualCompactTargetExtensions405
open ActualDensityGradientCoefficient405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {ρ : ℕ → Measure (Space n)} {μ : Measure (Space n)}

theorem centeredTargetDatum_pair_eq_volume
    (d : SourceData μ) (F : Space n → ℝ) (hF : Continuous F) (ψ : Space n → ℝ) :
    (∫ x, centeredTargetDatum d F hF x*ψ x ∂potentialMeasure d.potential) =
      ∫ x, Real.exp (-d.potential x)*
        (F (gradient d.potential x)-(∫ y, F y ∂μ))*ψ x := by
  calc
    _ = ∫ x, (F (gradient d.potential x)-(∫ y, F y ∂μ))*ψ x
        ∂potentialMeasure d.potential := by
      apply integral_congr_ae
      filter_upwards [centeredTargetDatum_ae d F hF] with x hx
      rw [hx]
    _ = _ := by
      rw [integral_potentialMeasure d.source_C1.continuous.measurable]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring

theorem centeredTargetDatum_compact_rhs_tendsto
    (d : ∀ k, SourceData (ρ k)) (e : SourceData μ)
    (hgrad0 : ∀ k, gradient (d k).potential (0 : Space n) = 0)
    (hφ : ∀ x, Tendsto (fun k => (d k).potential x) atTop (𝓝 (e.potential x)))
    (hgrad : ∀ x, Tendsto (fun k => gradient (d k).potential x) atTop
      (𝓝 (gradient e.potential x)))
    {F : Space n → ℝ} (hF : Continuous F) {C : ℝ}
    (hC : 0 ≤ C) (hbF : ∀ y, ‖F y‖ ≤ C)
    (hmean : Tendsto (fun k => ∫ y, F y ∂ρ k) atTop (𝓝 (∫ y, F y ∂μ)))
    {ψ : Space n → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Tendsto (fun k => ∫ x, centeredTargetDatum (d k) F hF x*ψ x
      ∂potentialMeasure (d k).potential) atTop
      (𝓝 (∫ x, centeredTargetDatum e F hF x*ψ x ∂potentialMeasure e.potential)) := by
  obtain ⟨A, hA⟩ := actual_centered_family_global_potential_lower d hgrad0 (hφ 0)
  obtain ⟨M, hM⟩ := hmean.norm.bddAbove_range
  have hm (k : ℕ) : ‖∫ y, F y ∂ρ k‖ ≤ M := hM (mem_range_self k)
  have hMn : 0 ≤ M := (norm_nonneg (∫ y, F y ∂ρ 0)).trans (hm 0)
  let G (k : ℕ) (x : Space n) : ℝ := Real.exp (-(d k).potential x)*
    (F (gradient (d k).potential x)-(∫ y, F y ∂ρ k))*ψ x
  let G₀ (x : Space n) : ℝ := Real.exp (-e.potential x)*
    (F (gradient e.potential x)-(∫ y, F y ∂μ))*ψ x
  have hdom : Integrable (fun x : Space n => Real.exp (-A)*(C+M)*‖ψ x‖)
      (volume : Measure (Space n)) :=
    (hψ.norm.integrable_of_hasCompactSupport hcψ.norm).const_mul _
  have hmeas (k : ℕ) : AEStronglyMeasurable (G k) (volume : Measure (Space n)) :=
    (((Real.continuous_exp.comp (d k).source_C1.continuous.neg).mul
      ((hF.comp (d k).gradient_lipschitz.continuous).sub continuous_const)).mul hψ).aestronglyMeasurable
  have hb (k : ℕ) : ∀ᵐ x ∂(volume : Measure (Space n)),
      ‖G k x‖ ≤ Real.exp (-A)*(C+M)*‖ψ x‖ := Eventually.of_forall fun x => by
    have hρ : Real.exp (-(d k).potential x) ≤ Real.exp (-A) :=
      Real.exp_le_exp.mpr (neg_le_neg (hA k x))
    have hv : ‖F (gradient (d k).potential x)-(∫ y, F y ∂ρ k)‖ ≤ C+M :=
      (norm_sub_le _ _).trans (add_le_add (hbF _) (hm k))
    dsimp only [G]
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hρ hv (norm_nonneg _) (Real.exp_nonneg _)) (norm_nonneg _)
  have ht : ∀ᵐ x ∂(volume : Measure (Space n)),
      Tendsto (fun k => G k x) atTop (𝓝 (G₀ x)) := Eventually.of_forall fun x => by
    have hρ := (Real.continuous_exp.tendsto (-e.potential x)).comp (hφ x).neg
    have hv := hF.continuousAt.tendsto.comp (hgrad x)
    exact (hρ.mul (hv.sub hmean)).mul_const (ψ x)
  have hi := tendsto_integral_of_dominated_convergence
    (fun x : Space n => Real.exp (-A)*(C+M)*‖ψ x‖) hmeas hdom hb ht
  simpa only [centeredTargetDatum_pair_eq_volume, G, G₀] using hi

end KLSConstantImprovement.ActualCenteredForcingRhsLimit405
#print axioms KLSConstantImprovement.ActualCenteredForcingRhsLimit405.centeredTargetDatum_pair_eq_volume
#print axioms KLSConstantImprovement.ActualCenteredForcingRhsLimit405.centeredTargetDatum_compact_rhs_tendsto
