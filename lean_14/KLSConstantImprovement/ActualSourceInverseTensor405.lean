import KLSConstantImprovement.ActualBoundedCanonicalSource
import KLS.WeakInverseTensorDivergence
import KLS.BoundedCompactH1Tests

/-!
Actual inverse-Hessian third-tensor divergence on the constructed C1,1
source. Both local domains and the coefficient divergence are consequences
of SourceData. The second theorem extends this exact actual coefficient
identity to bounded compact raw H1 tests, for canonical Bochner integration.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceInverseTensor405
open KLS ActualBoundedCanonicalSource
variable {n : ℕ} {μ : Measure (Space n)}

def actualInverseTensor (d : SourceData μ) (k : Fin n) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  (coordinateHessian d.potential x)⁻¹ * Matrix.of (d.third x k) *
    (coordinateHessian d.potential x)⁻¹

theorem inverse_tensor_local_L2 (d : SourceData μ) (k a i : Fin n)
    (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (fun x => actualInverseTensor d k x a i) 2 (volume.restrict E) := by
  obtain ⟨_, hDJ, _⟩ := actual_mongeAmpere_inverse_hasLocalWeakDerivative d.source_C1
    (d.target_smooth.of_le (by simp)) d.gradient_lipschitz
    (d.hessian_ae.mono fun _ hx => hx.2.1) d.third_local_L2 d.third_weak_derivative
  have h := (hDJ k a i E hE).neg
  change MemLp (fun x => -(-actualInverseTensor d k x a i)) 2 (volume.restrict E) at h
  simpa only [neg_neg] using h

private theorem inverse_column_transport (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    (∑ a, ∫ x, Real.exp (-d.potential x) * (coordinateHessian d.potential x)⁻¹ a i *
      coordinateDerivative ψ a x) =
      ∫ x, Real.exp (-d.potential x) * coordinateDerivative d.targetPotential i
        (gradient d.potential x) * ψ x := by
  letI := d.source_probability
  exact weak_moment_inverseHessian_integral_column_volume d.source_lipschitz d.source_convex
    (d.target_smooth.of_le (by simp)) d.target_convex_potential d.target_convexity_pos
    d.target_strong d.target_closed d.target_convex (d.pushforward.trans d.target_representation)
    hψ hc i

theorem actual_inverse_tensor_divergence (d : SourceData μ) (k i : Fin n)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∑ a, ∫ x, actualInverseTensor d k x a i * coordinateDerivative ψ a x
      ∂potentialMeasure d.potential) =
      ∫ x, ((1 : Matrix (Fin n) (Fin n) ℝ) k i -
        (coordinateHessian d.potential x * coordinateHessian d.targetPotential
          (gradient d.potential x)) k i) * ψ x ∂potentialMeasure d.potential := by
  have hv := actual_inverse_tensor_integral_column d.source_C1
    (d.target_smooth.of_le (by simp)) d.gradient_lipschitz
    (d.hessian_ae.mono fun _ hx => hx.2.1) d.third_local_L2 d.third_weak_derivative
    (fun ψ hψ hc i => inverse_column_transport d hψ hc i) k i hψ hc
  change (∑ a, ∫ x, Real.exp (-d.potential x) * actualInverseTensor d k x a i *
      coordinateDerivative ψ a x) =
    ∫ x, Real.exp (-d.potential x) *
      ((1 : Matrix (Fin n) (Fin n) ℝ) k i -
        (coordinateHessian d.potential x * coordinateHessian d.targetPotential
          (gradient d.potential x)) k i) * ψ x at hv
  simpa only [integral_potentialMeasure d.source_C1.continuous.measurable,
    mul_comm, mul_left_comm, mul_assoc] using hv

/-- The actual divergence can be tested against u_k times a compact
derivative of psi, even though u_k is only locally H1. The stated F are
genuine weak derivatives of this test, not a supplied divergence identity. -/
theorem actual_inverse_tensor_bounded_H1_test (d : SourceData μ) (k i : Fin n)
    {f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E)) (hc : HasCompactSupport f)
    {C : ℝ} (hbnd : ∀ᵐ x ∂volume, ‖f x‖ ≤ C)
    (hFl : ∀ a E, IsCompact E → MemLp (F a) 2 (volume.restrict E))
    (hFw : ∀ a, HasLocalWeakCoordinateDerivative f (F a) a) :
    (∑ a, ∫ x, actualInverseTensor d k x a i * F a x ∂potentialMeasure d.potential) =
      ∫ x, ((1 : Matrix (Fin n) (Fin n) ℝ) k i -
        (coordinateHessian d.potential x * coordinateHessian d.targetPotential
          (gradient d.potential x)) k i) * f x ∂potentialMeasure d.potential := by
  let A : Fin n → Space n → ℝ := fun a x =>
    Real.exp (-d.potential x) * actualInverseTensor d k x a i
  let b : Space n → ℝ := fun x => Real.exp (-d.potential x) *
    ((1 : Matrix (Fin n) (Fin n) ℝ) k i -
      (coordinateHessian d.potential x * coordinateHessian d.targetPotential
        (gradient d.potential x)) k i)
  have hρ : Continuous (fun x => Real.exp (-d.potential x)) :=
    Real.continuous_exp.comp d.source_C1.continuous.neg
  have hA (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (A a) 2 (volume.restrict E) :=
    (memLp_top_restrict_compact_of_continuous hρ hE).mul (inverse_tensor_local_L2 d k a i E hE)
  have hb : LocallyIntegrable b volume := by
    apply locallyIntegrable_of_memLp_two_on_compacts
    intro E hE
    letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
    have hP (a : Fin n) : Continuous (fun x => coordinateHessian d.targetPotential
        (gradient d.potential x) a i) :=
      (contDiff_coordinateHessian (d.target_smooth.of_le (by simp) : ContDiff ℝ 2 d.targetPotential)
        (m := 0) (by norm_num) a i).continuous.comp d.gradient_lipschitz.continuous
    have hHP : MemLp (fun x => (coordinateHessian d.potential x *
        coordinateHessian d.targetPotential (gradient d.potential x)) k i) ∞ (volume.restrict E) := by
      simp only [Matrix.mul_apply]
      exact memLp_finsetSum Finset.univ fun a _ =>
        (memLp_top_actual_hessian_of_locallyLipschitz_gradient d.gradient_lipschitz.locallyLipschitz
          k a hE).mul (memLp_top_restrict_compact_of_continuous (hP a) hE)
    have hconst : MemLp (fun _ : Space n => (1 : Matrix (Fin n) (Fin n) ℝ) k i)
        ∞ (volume.restrict E) := memLp_const _
    have hbTop : MemLp b ∞ (volume.restrict E) :=
      (memLp_top_restrict_compact_of_continuous hρ hE).mul (hconst.sub hHP)
    exact hbTop.mono_exponent (by norm_num)
  have hdiv (ψ : Space n → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
      (∑ a, ∫ x, A a x * coordinateDerivative ψ a x) = ∫ x, b x * ψ x := by
    have he := actual_inverse_tensor_divergence d k i hψ hψc
    simpa only [A, b, integral_potentialMeasure d.source_C1.continuous.measurable,
      mul_comm, mul_left_comm, mul_assoc] using he
  have he := integral_divergence_of_bounded_compact_H1_test hA hb hdiv hf hc hbnd hFl hFw
  simpa only [A, b, integral_potentialMeasure d.source_C1.continuous.measurable,
    mul_comm, mul_left_comm, mul_assoc] using he.2.2

end KLSConstantImprovement.ActualSourceInverseTensor405

#print axioms KLSConstantImprovement.ActualSourceInverseTensor405.inverse_tensor_local_L2
#print axioms KLSConstantImprovement.ActualSourceInverseTensor405.actual_inverse_tensor_divergence
#print axioms KLSConstantImprovement.ActualSourceInverseTensor405.actual_inverse_tensor_bounded_H1_test
