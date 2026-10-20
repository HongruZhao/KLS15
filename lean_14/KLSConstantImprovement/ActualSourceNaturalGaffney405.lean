import KLSConstantImprovement.ActualSourceNaturalInverseIdentification405
import KLSConstantImprovement.ActualSourceLimitGaffneyEnergy405

/-! Actual natural-domain source Gaffney regularity.  The flux is defined
from the constructed canonical inverse itself.  All local weak domains,
metric compatibility and the global combined energy bound are proved by
the actual joint regularization limit; no analytic witness is an input. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceNaturalGaffney405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyVector405 ActualSourceJointWeakLimit405
open ActualSourceRegularizedFluxH1405 ActualSourceRegularizedEnergyForm405
open ActualSourceLimitFluxDomains405 ActualSourceLimitFluxWeakDerivative405 ActualSourceLimitDivergence405
open ActualSourceLimitJacobianSymmetry405 ActualSourceLimitGaffneyEnergy405 ActualSourceLocalizedGaffney405
open ActualSourceNaturalInverseIdentification405 ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricInverse
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

def naturalCanonicalFlux (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (i : Fin n) (x : Space n) : ℝ :=
  ∑ a : Fin n, canonicalMetricRoot d.potential x i a *
    canonicalMetricGradient d.potential a (sourceMetricInverseH1 d g) x

theorem exists_naturalCanonicalFlux_gaffney (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) :
    ∃ Du : Fin n → Fin n → Space n → ℝ,
      (∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E)) ∧
      (∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E)) ∧
      (∀ i j, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i j) j) ∧
      (∀ᵐ x ∂(volume : Measure (Space n)),
        (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x)).IsSymm) ∧
      Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential) ∧
      Integrable (sourceVectorJacobianEnergy Du) (potentialMeasure d.potential) ∧
      (∫ x, sourceVectorMass d.potential (naturalCanonicalFlux d g) x + sourceVectorJacobianEnergy Du x
        ∂potentialMeasure d.potential) ≤ ‖g‖ ^ 2 ∧
      (∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
        (∑ j : Fin n, ∫ x, naturalCanonicalFlux d g j x * coordinateDerivative ψ j x
          ∂potentialMeasure d.potential) = ∫ x, g x * ψ x ∂potentialMeasure d.potential) := by
  obtain ⟨D, W, U, V, σ, hσ, hV, _, hDu, hc, hnorm, hW, hU, hw⟩ :=
    exists_actual_regularized_joint_weak_limit d hn g hg
  have hb (k : ℕ) : ‖W k‖ ≤ ‖g‖ := by nlinarith [hnorm k, norm_nonneg (W k), norm_nonneg g]
  obtain ⟨_, hgrad⟩ := naturalInverse_eq_joint_scalar_limit d hn g hg D W U V σ hσ hW hb hU hw
  have hflux (i : Fin n) : naturalCanonicalFlux d g i =ᵐ[potentialMeasure d.potential] energyLimitFlux d V i := by
    filter_upwards [ae_all_iff.mpr hgrad] with x hx
    exact Finset.sum_congr rfl fun a _ => congrArg (fun t : ℝ => canonicalMetricRoot d.potential x i a * t) (hx a)
  have hfluxV (i : Fin n) := (volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous).ae_eq (hflux i)
  have hZ := energyLimitWhitenedJacobian_isSymm_ae d V
    (energy_weak_limit_jacobian_coordinates_eq d hn g D W V σ hc hW hw)
  have hM : sourceVectorMass d.potential (energyLimitFlux d V) =ᵐ[potentialMeasure d.potential]
      sourceVectorMass d.potential (naturalCanonicalFlux d g) := by
    filter_upwards [ae_all_iff.mpr hflux] with x hx
    simp only [sourceVectorMass]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hx i, hx j]
  have hdomains := energyLimitGaffney_integrable d V hZ
  refine ⟨energyLimitJacobian d V, ?_, ?_, ?_, ?_, hdomains.1.congr hM, hdomains.2, ?_, ?_⟩
  · intro i E hE
    exact (memLp_congr_ae (ae_restrict_of_ae (hfluxV i))).mpr ((energyLimitFlux_Jacobian_local_L2 d V hE).1 i)
  · intro i j E hE
    exact (energyLimitFlux_Jacobian_local_L2 d V hE).2 i j
  · intro i j
    exact (energyLimitFlux_hasLocalWeakDerivative d hn g D W V σ hσ hW hDu hb hw i j).congr_ae
      (hfluxV i).symm EventuallyEq.rfl
  · exact energyLimitJacobian_compatible_ae d V hZ
  · calc
      _ = ∫ x, sourceVectorMass d.potential (energyLimitFlux d V) x +
          sourceVectorJacobianEnergy (energyLimitJacobian d V) x ∂potentialMeasure d.potential :=
        integral_congr_ae (hM.symm.fun_add EventuallyEq.rfl)
      _ = ‖V‖ ^ 2 := energyLimitGaffney_integral_eq_norm_sq d V hZ
      _ ≤ ‖g‖ ^ 2 := (sq_le_sq₀ (norm_nonneg V) (norm_nonneg g)).mpr hV
  · intro ψ hψ hψc
    calc
      _ = ∑ j : Fin n, ∫ x, energyLimitFlux d V j x * coordinateDerivative ψ j x
          ∂potentialMeasure d.potential := Finset.sum_congr rfl fun j _ =>
        integral_congr_ae ((hflux j).fun_mul EventuallyEq.rfl)
      _ = _ := energyLimitFlux_compact_divergence_test d hn g hg D W V σ hW hw hψ hψc

end KLSConstantImprovement.ActualSourceNaturalGaffney405
#print axioms KLSConstantImprovement.ActualSourceNaturalGaffney405.exists_naturalCanonicalFlux_gaffney
