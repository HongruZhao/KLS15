import KLS.LocalWeakDerivativeUniqueness
import KLS.WeakMomentLipschitzInverseTests

/-! Genuine raw local weak derivatives are closed under locally dominated
L1 limits. This is used for common joint truncations: their derivative
errors need only a local L1 dominator, rather than an unproved uniform H1
bound for the truncated products. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualLocalDominatedWeakClosure405
open KLS
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem local_dominated_compact_pairing_tendsto
    {f : ℕ → Space n → ℝ} {u : Space n → ℝ}
    (hf : ∀ k, LocallyIntegrable (f k) volume)
    (hlim : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto (fun k => f k x) atTop (𝓝 (u x)))
    (hdom : ∀ E : Set (Space n), IsCompact E → ∃ b : Space n → ℝ,
      Integrable b (volume.restrict E) ∧ ∀ k, ∀ᵐ x ∂volume.restrict E, ‖f k x‖ ≤ b x)
    {c : Space n → ℝ} (hcm : AEStronglyMeasurable c volume)
    (hcc : HasCompactSupport c) (hcb : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖c x‖ ≤ C) :
    Tendsto (fun k => ∫ x, f k x * c x) atTop (𝓝 (∫ x, u x * c x)) := by
  let E := tsupport c
  have hE : IsCompact E := hcc
  obtain ⟨b, hb, hbound⟩ := hdom E hE
  obtain ⟨C, hC, hCb⟩ := hcb
  have hm (k : ℕ) : AEStronglyMeasurable (fun x => f k x * c x) (volume.restrict E) :=
    ((locallyIntegrable_iff.mp (hf k) E hE).aestronglyMeasurable).mul
      (hcm.mono_measure Measure.restrict_le_self)
  have ht := tendsto_integral_of_dominated_convergence (fun x => ‖b x‖ * C) hm
    (hb.norm.mul_const C) (fun k => by
      filter_upwards [hbound k] with x hx
      rw [norm_mul]
      exact mul_le_mul (hx.trans (Real.le_norm_self _)) (hCb x) (norm_nonneg _) (norm_nonneg _))
    (by
      filter_upwards [ae_restrict_of_ae hlim] with x hx
      exact hx.mul_const (c x))
  have he (q : Space n → ℝ) : (∫ x in E, q x * c x) = ∫ x, q x * c x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  simpa only [he] using ht

theorem local_weak_derivative_of_dominated_limits
    {f F : ℕ → Space n → ℝ} {u U : Space n → ℝ} {i : Fin n}
    (hf : ∀ k, LocallyIntegrable (f k) volume)
    (hF : ∀ k, LocallyIntegrable (F k) volume)
    (hweak : ∀ k, HasLocalWeakCoordinateDerivative (f k) (F k) i)
    (hlim : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto (fun k => f k x) atTop (𝓝 (u x)))
    (hDlim : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto (fun k => F k x) atTop (𝓝 (U x)))
    (hdom : ∀ E : Set (Space n), IsCompact E → ∃ b : Space n → ℝ,
      Integrable b (volume.restrict E) ∧ ∀ k, ∀ᵐ x ∂volume.restrict E, ‖f k x‖ ≤ b x)
    (hDdom : ∀ E : Set (Space n), IsCompact E → ∃ b : Space n → ℝ,
      Integrable b (volume.restrict E) ∧ ∀ k, ∀ᵐ x ∂volume.restrict E, ‖F k x‖ ≤ b x) :
    HasLocalWeakCoordinateDerivative u U i := by
  intro ψ hψ hc
  have hdcont : Continuous (coordinateDerivative ψ i) :=
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous
  have hdcompact : HasCompactSupport (coordinateDerivative ψ i) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_coordinateDerivative_subset ψ i)
  obtain ⟨C, hC⟩ := hdcompact.exists_bound_of_continuous hdcont
  obtain ⟨D, hD⟩ := hc.exists_bound_of_continuous hψ.continuous
  have hleft := local_dominated_compact_pairing_tendsto hf hlim hdom
    hdcont.aestronglyMeasurable hdcompact
    ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩
  have hright := local_dominated_compact_pairing_tendsto hF hDlim hDdom
    hψ.continuous.aestronglyMeasurable hc
    ⟨max D 0, le_max_right _ _, fun x => (hD x).trans (le_max_left _ _)⟩
  exact tendsto_nhds_unique hleft
    (hright.neg.congr fun k => (hweak k ψ hψ hc).symm)

end KLSConstantImprovement.ActualLocalDominatedWeakClosure405
#print axioms KLSConstantImprovement.ActualLocalDominatedWeakClosure405.local_dominated_compact_pairing_tendsto
#print axioms KLSConstantImprovement.ActualLocalDominatedWeakClosure405.local_weak_derivative_of_dominated_limits
