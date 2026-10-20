import KLSConstantImprovement.ActualNaturalWeakKatoLimit405
import KLSConstantImprovement.ActualRegularizedWeakKato405
import KLSConstantImprovement.OriginalCubic405OfWeakKato

/-! The actual natural inverse satisfies weak Kato. One genuine Gaffney
Jacobian supplies every local connection, Hessian and covariant domain;
the regularized Bochner inequality and its zero-parameter limit refer to
that same Jacobian. No mass, regularity, PDE or domain witness is input. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualNaturalWeakKato405
open KLS ActualBoundedCanonicalSource ActualNaturalWeakKatoLimit405 ActualNaturalSqrtMass405
open ActualRegularizedWeakKato405 OriginalCubic405OfWeakKato
open ActualNaturalLocalConnectionDomain405 ActualNaturalLocalHessianDomain405
open ActualNaturalCovariantEnergy405 ActualSourceConnectionFields405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceNaturalHessian405
open ActualCompactRawMetricGraph
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

theorem actual_natural_weak_Kato_gate405 : ActualNaturalWeakKatoGate405 := by
  intro n μ d hn _hμ g hg Dg hgw hDg B hB hgrad
  obtain ⟨Du, hu, hDu, hw, hcomp, hMi, hQi, _hEnergy, _hdiv⟩ :=
    exists_naturalCanonicalFlux_gaffney d hn g hg
  have hΓ (E : Set (Space n)) (hE : IsCompact E) :=
    (actual_connectionGamma_local_domains d g Du hDu hw hcomp hMi hQi E hE).2
  have hΓloc : LocallyIntegrable (sourceConnectionGamma d (naturalCanonicalFlux d g)) volume :=
    locallyIntegrable_iff.mpr hΓ
  have hC := naturalHessian_local_L2_of_local_Gamma d g Du hu hDu hΓ
  have hEloc := natural_covariant_energy_local_integrable d g Du hu hDu hΓ
  have hSqrt := naturalSqrtMass_raw_H1 d g Du hu hDu hw hC hcomp hMi hEloc
  have hgradMatrix : ∀ᵐ x ∂potentialMeasure d.potential,
      (fun a => Dg a x) ⬝ᵥ ((coordinateHessian d.potential x)⁻¹ *ᵥ (fun a => Dg a x)) ≤ B^2 := by
    filter_upwards [hgrad, d.raw_metric_derivative_sq_ae Dg] with x hx he
    rw [he] at hx
    simpa only [rawInverseHessianGradientForm, matrix_quadratic_sum_eq_dotProduct] using hx
  refine ⟨naturalSqrtMassDerivative d g Du, hSqrt.1, hSqrt.2, ?_⟩
  apply natural_weak_Kato_of_regularized d g Du hu hDu hC hcomp hMi hEloc B
  intro k ψ hψ hcψ hnψ
  exact actual_regularized_weak_Kato d hn g hg Du hu hDu hw hC hcomp hMi hEloc hΓloc
    Dg hgw hDg hB hgradMatrix (cutoffScale_pos k) hψ hcψ hnψ

end KLSConstantImprovement.ActualNaturalWeakKato405
#print axioms KLSConstantImprovement.ActualNaturalWeakKato405.actual_natural_weak_Kato_gate405
