import KLSConstantImprovement.ActualSourceInverseGradientDomain405

/-!
The actual raw H1 product test in the inverse-tensor divergence. For a
compact C2 scalar psi, testing with (J grad psi)_k partial_i psi is fully
in the actual source domain. All boundedness, weak derivative and local L2
conditions are proved, without differentiability of J or of a Poisson
optimizer being assumed. This is the analytic connection-cancellation test
for compact canonical Bochner; its finite index contractions are separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceCanonicalConnectionTest405
open KLS ActualBoundedCanonicalSource ActualSourceInverseTensor405 ActualSourceInverseGradientDomain405
variable {n : ℕ} {μ : Measure (Space n)}

private theorem compact_top_of_local_top {f : Space n → ℝ}
    (hc : HasCompactSupport f)
    (hf : ∀ E, IsCompact E → MemLp f ∞ (volume.restrict E)) : MemLp f ∞ volume := by
  have hi := (memLp_indicator_iff_restrict hc.measurableSet.nullMeasurableSet).mpr (hf _ hc)
  have he : (tsupport f).indicator f = f := by
    funext x
    by_cases hx : x ∈ tsupport f
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
  rwa [he] at hi

/-- The actual scalar test u_k partial_i psi is accepted by the source's
inverse-tensor divergence, with its literal raw product derivative. -/
theorem actual_compact_connection_product_test (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) (k i : Fin n) :
    (∑ a, ∫ x, actualInverseTensor d k x a i *
      (actualInverseGradientDerivative d ψ k a x * coordinateDerivative ψ i x +
        actualInverseGradient d ψ k x * coordinateHessian ψ x a i)
          ∂potentialMeasure d.potential) =
      ∫ x, ((1 : Matrix (Fin n) (Fin n) ℝ) k i -
        (coordinateHessian d.potential x * coordinateHessian d.targetPotential
          (gradient d.potential x)) k i) *
        (actualInverseGradient d ψ k x * coordinateDerivative ψ i x) ∂potentialMeasure d.potential := by
  let u := actualInverseGradient d ψ k
  let Du := actualInverseGradientDerivative d ψ k
  let p := coordinateDerivative ψ i
  let f : Space n → ℝ := fun x => u x * p x
  let F : Fin n → Space n → ℝ := fun a x =>
    Du a x * p x + u x * coordinateHessian ψ x a i
  have hp : ContDiff ℝ 1 p := contDiff_coordinateDerivative hψ (by norm_num) i
  have huTop := inverseGradient_local_top d (hψ.of_le (by norm_num)) k
  have hDu := inverseGradientDerivative_local_L2 d hψ k
  have hpTop (E : Set (Space n)) (hE : IsCompact E) : MemLp p ∞ (volume.restrict E) :=
    memLp_top_restrict_compact_of_continuous hp.continuous hE
  have hCl (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => coordinateHessian ψ x a i) 2 (volume.restrict E) :=
    memLp_continuous_on_compact
      (contDiff_coordinateHessian hψ (m := 0) (by norm_num) a i).continuous hE
  have hfTopLocal (E : Set (Space n)) (hE : IsCompact E) : MemLp f ∞ (volume.restrict E) :=
    (huTop E hE).mul (hpTop E hE)
  have hfc : HasCompactSupport f := (inverseGradient_compact d hc k).mul_right
  have hfTop := compact_top_of_local_top hfc hfTopLocal
  have hFl (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (F a) 2 (volume.restrict E) := by
    have hfirst : MemLp (fun x => Du a x * p x) 2 (volume.restrict E) := by
      have hDu' : MemLp (Du a) 2 (volume.restrict E) := hDu a E hE
      have hprod : MemLp (p * Du a) 2 (volume.restrict E) := (hpTop E hE).mul hDu'
      change MemLp (fun x => p x * Du a x) 2 (volume.restrict E) at hprod
      simpa only [mul_comm] using hprod
    exact hfirst.add ((huTop E hE).mul (hCl a E hE))
  have hFw (a : Fin n) : HasLocalWeakCoordinateDerivative f (F a) a :=
    (inverseGradient_hasLocalWeakDerivative d hψ k a).mul
      (hasLocalWeakCoordinateDerivative_of_contDiff hp a)
      (memLp_two_on_compacts_of_top huTop) (memLp_two_on_compacts_of_top hpTop)
      (hDu a) (hCl a)
  have hess : eLpNormEssSup f volume < (⊤ : ℝ≥0∞) := by
    rw [← eLpNorm_exponent_top hfTop.aestronglyMeasurable]
    exact hfTop
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hess
  have hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ (C : ℝ) := by
    filter_upwards [hC] with x hx
    exact_mod_cast hx
  exact actual_inverse_tensor_bounded_H1_test d k i
    (memLp_two_on_compacts_of_top hfTopLocal) hfc hb hFl hFw

end KLSConstantImprovement.ActualSourceCanonicalConnectionTest405

#print axioms KLSConstantImprovement.ActualSourceCanonicalConnectionTest405.actual_compact_connection_product_test
