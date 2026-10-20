import KLSConstantImprovement.ActualKatoJointExpansion405
import KLSConstantImprovement.ActualDualWeakBochner405
import KLSConstantImprovement.ActualDualBumpDerivative405

/-! Actual common-cutoff Bochner integrands equal the limiting Kato
integrand times the bump plus the literal metric-flux bump error. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualKatoJointPointwise405
open KLS ActualBoundedCanonicalSource ActualNaturalDualJoint405 ActualDualKatoMultiplier405
open ActualKatoJointExpansion405 ActualKatoFluxAlgebra405 ActualKatoNonlinearDomains405
open ActualKatoLocalDomains405 ActualNaturalMassWeakDerivative405 ActualSmoothKatoRegularizer405
open ActualDualWeakBochner405 ActualJointWeakBochner405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
variable {n : ℕ} {μ : Measure (Space n)}

def katoJointMultiplier (ε : ℝ) (k : ℕ) (v : DualIndex n → ℝ) : ℝ :=
  dualScalarMultiplier (fun t => 2 * katoFirst ε t) k v

def naturalKatoWeakIntegrand (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (ε : ℝ) (ψ : Space n → ℝ) (x : Space n) : ℝ :=
  ψ x * naturalKatoDensity d g Du ε x +
    ∑ a : Fin n, naturalKatoMetricFlux d g Du ε a x * coordinateDerivative ψ a x

def naturalKatoBumpError (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (ε : ℝ) (k : ℕ) (ψ : Space n → ℝ) (x : Space n) : ℝ :=
  ψ x * ∑ a : Fin n, naturalKatoMetricFlux d g Du ε a x *
    dualSourceDerivative d g Du (dualBump k) a x

def naturalKatoForcing (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (ε : ℝ) (Dg : Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  2 * katoFirst ε (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) *
    (∑ j : Fin n, Dg j x * naturalCanonicalFlux d g j x)

theorem katoJointMultiplier_contDiff_compact {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    ContDiff ℝ 1 (katoJointMultiplier (n := n) ε k) ∧
      HasCompactSupport (katoJointMultiplier (n := n) ε k) :=
  dualScalarMultiplier_contDiff_compact (contDiff_const.mul (katoFirst_contDiff hε)) k

theorem actual_Kato_common_bump_expansion_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm)
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) (ψ : Space n → ℝ) :
    dualBochnerIntegrand d g Du (katoJointMultiplier ε k) ψ =ᵐ[potentialMeasure d.potential]
      fun x => dualSource d g (dualBump k) x * naturalKatoWeakIntegrand d g Du ε ψ x +
        naturalKatoBumpError d g Du ε k ψ x := by
  have hF : ContDiff ℝ 1 (fun t => 2 * katoFirst ε t) :=
    contDiff_const.mul (katoFirst_contDiff hε)
  have hDer (t : ℝ) : HasDerivAt (fun y => 2 * katoFirst ε y) (2 * katoSecond ε t) t :=
    (katoFirst_hasDerivAt hε t).const_mul 2
  have hD (a : Fin n) := actual_dual_scalar_multiplier_derivative_ae d g Du hF hDer k a
  filter_upwards [actual_dualMass_eq_ae d g, ae_all_iff.mpr hD,
    natural_half_mass_flux_eq_ae d g Du hcomp] with x hM hd hh
  have hv : dualSource d g (katoJointMultiplier ε k) x =
      dualSource d g (dualBump k) x * (2 * katoFirst ε (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)) := by
    change dualBump k _ * (2 * katoFirst ε (dualMass _)) = _
    rw [hM]
    rfl
  have he := finite_joint_Kato_expansion (ψ x) (dualSource d g (dualBump k) x)
    (katoFirst ε (sourceVectorMass d.potential (naturalCanonicalFlux d g) x))
    (katoSecond ε (sourceVectorMass d.potential (naturalCanonicalFlux d g) x))
    (sourceBochnerDensity d (naturalCanonicalFlux d g) Du x)
    (fun a => naturalMassRawDerivative d g Du a x)
    ((coordinateHessian d.potential x)⁻¹ *ᵥ (fun a => naturalMassRawDerivative d g Du a x))
    (fun a => coordinateDerivative ψ a x) (fun a => dualSourceDerivative d g Du (dualBump k) a x)
  simp only [dualBochnerIntegrand, dualEffectiveDerivative, hv]
  simp_rw [show ∀ a, dualSourceDerivative d g Du (katoJointMultiplier ε k) a x =
      dualSource d g (dualBump k) x * (2 * katoSecond ε (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)) *
        naturalMassRawDerivative d g Du a x +
          (2 * katoFirst ε (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)) *
            dualSourceDerivative d g Du (dualBump k) a x from hd, hh]
  simpa only [naturalKatoWeakIntegrand, naturalKatoDensity, naturalMassMetricSquare,
    dotProduct, naturalKatoBumpError, naturalKatoMetricFlux_eq] using he

end KLSConstantImprovement.ActualKatoJointPointwise405
#print axioms KLSConstantImprovement.ActualKatoJointPointwise405.katoJointMultiplier_contDiff_compact
#print axioms KLSConstantImprovement.ActualKatoJointPointwise405.actual_Kato_common_bump_expansion_ae
