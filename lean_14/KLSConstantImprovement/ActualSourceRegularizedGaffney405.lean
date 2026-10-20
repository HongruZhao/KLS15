import KLSConstantImprovement.ActualSourceGaffneyBoundary405

/-!
The actual fixed-parameter regularized inverse satisfies the exact
ordinary-source Gaffney energy. Its final forcing constant is one.
All global Jacobian domains, compatibility, and vanished radius errors
are consequences of the preceding actual construction.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceRegularizedGaffney405
open KLS ActualBoundedCanonicalSource ActualSourceLocalizedGaffney405
open ActualSourceGlobalJacobianDomain405 ActualSourceGaffneyBoundary405
open ActualSourceMetricRegularization405 ActualSourceRegularizedEnergyForm405
open ActualSourceRegularizedFluxH1405 ActualSourceRegularizedFluxCompatibility405
open ActualCompatibleJacobianCoercivity405 ActualCompactWeakSourceVectorSquare
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem source_vector_mass_nonneg_ae (d : SourceData μ) (u : Fin n → Space n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ sourceVectorMass d.potential u x := by
  filter_upwards [d.hessian_ae_source] with x hx
  have hp := hx.1.posSemidef.dotProduct_mulVec_nonneg (fun i => u i x)
  have he : (fun i => u i x) ⬝ᵥ (coordinateHessian d.potential x *ᵥ (fun i => u i x)) =
      sourceVectorMass d.potential u x := by
    simp only [dotProduct, Matrix.mulVec, sourceVectorMass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [star_trivial, he] using hp

theorem exists_regularizedWeakFlux_exact_gaffney (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) :
    ∃ D : Fin n → Fin n → Space n → ℝ,
      (∀ i j, MemLp (regularizedFluxDerivative d hn k hε g D i j) 2 (potentialMeasure d.potential)) ∧
      (∀ i j, HasLocalWeakCoordinateDerivative (regularizedWeakFlux d hn k hε g i)
        (regularizedFluxDerivative d hn k hε g D i j) j) ∧
      (∀ᵐ x ∂(volume : Measure (Space n)),
        (regularizedMetricHessian d k ε x * regularizedFluxJacobian d hn k hε g D x).IsSymm) ∧
      (rawWeakSourceVectorAdjoint d.potential (regularizedWeakFlux d hn k hε g)
        (regularizedFluxDerivative d hn k hε g D) =ᵐ[potentialMeasure d.potential] (g : Space n → ℝ)) ∧
      Integrable (sourceVectorMass d.potential (regularizedWeakFlux d hn k hε g))
        (potentialMeasure d.potential) ∧
      Integrable (sourceVectorJacobianEnergy (regularizedFluxDerivative d hn k hε g D))
        (potentialMeasure d.potential) ∧
      (∫ x, sourceVectorMass d.potential (regularizedWeakFlux d hn k hε g) x +
        sourceVectorJacobianEnergy (regularizedFluxDerivative d hn k hε g D) x
          ∂potentialMeasure d.potential) = ‖g‖ ^ 2 ∧
      (∫ x, sourceVectorMass d.potential (regularizedWeakFlux d hn k hε g) x
        ∂potentialMeasure d.potential) ≤ ‖g‖ ^ 2 ∧
      (∫ x, sourceVectorJacobianEnergy (regularizedFluxDerivative d hn k hε g D) x
        ∂potentialMeasure d.potential) ≤ ‖g‖ ^ 2 := by
  obtain ⟨D, hDu, hw, hc, ha⟩ := exists_regularizedWeakFlux_global_jacobian d hn k hε g hg
  let u := regularizedWeakFlux d hn k hε g
  let Du := regularizedFluxDerivative d hn k hε g D
  let ν := potentialMeasure d.potential
  have hu := regularizedWeakFlux_memLp d hn k hε g
  have hM : Integrable (sourceVectorMass d.potential u) ν := source_vector_mass_integrable d u hu
  have hQ : Integrable (sourceVectorJacobianEnergy Du) ν :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => (hDu i j).integrable_mul (hDu j i)))
  have he := integral_source_vector_global_gaffney d u Du hu hDu hw g (Lp.memLp _) ha
  rw [← L2.norm_sq_eq_integral_sq] at he
  have hac : ν ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  have hQn : ∀ᵐ x ∂ν, 0 ≤ sourceVectorJacobianEnergy Du x := by
    filter_upwards [hc.filter_mono hac.ae_le] with x hx
    have hh := compatible_jacobian_trace_nonneg (regularizedMetricHessian d k ε x)
      (regularizedFluxJacobian d hn k hε g D x) (regularizedMetricHessian_posDef d k hε x) hx
    simpa only [sourceVectorJacobianEnergy, Du, regularizedFluxJacobian,
      Matrix.trace, Matrix.diag_apply, Matrix.mul_apply] using hh
  have hMn : 0 ≤ ∫ x, sourceVectorMass d.potential u x ∂ν :=
    integral_nonneg_of_ae (source_vector_mass_nonneg_ae d u)
  have hQnn : 0 ≤ ∫ x, sourceVectorJacobianEnergy Du x ∂ν := integral_nonneg_of_ae hQn
  have hadd : (∫ x, sourceVectorMass d.potential u x + sourceVectorJacobianEnergy Du x ∂ν) =
      (∫ x, sourceVectorMass d.potential u x ∂ν) + (∫ x, sourceVectorJacobianEnergy Du x ∂ν) := by
    simpa only [Pi.add_apply] using integral_add hM hQ
  refine ⟨D, hDu, hw, hc, ha, hM, hQ, he, ?_, ?_⟩ <;> linarith

end KLSConstantImprovement.ActualSourceRegularizedGaffney405
#print axioms KLSConstantImprovement.ActualSourceRegularizedGaffney405.source_vector_mass_nonneg_ae
#print axioms KLSConstantImprovement.ActualSourceRegularizedGaffney405.exists_regularizedWeakFlux_exact_gaffney
