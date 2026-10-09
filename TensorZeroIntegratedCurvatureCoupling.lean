import TensorZeroMaximalCurvatureEnergy
import TensorIntegratedCurvatureCoupling

/-! Integration of the actual pointwise completed square against an
arbitrary full-domain constrained Hodge test. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators ENNReal RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
open KLS
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ} {φ : Space n → ℝ}

lemma weakConstrainedTensorHodgeZero_compatible_ae
    {f : TensorTwoFormIndex n 0 → Space n → ℝ}
    {g : TensorHodgeOutputIndex n 0 → Space n → ℝ}
    (h : HasWeakConstrainedTensorHodge φ 0 f g) :
    ∀ᵐ x ∂potentialMeasure φ, TensorTwoFormCompatible (fun z => f z x) := by
  have hall : ∀ᵐ x ∂volume, ∀ a,
      (∑ z, tensorTwoFormConstraintMatrix n 0 a z*f z x)=0 := ae_all_iff.mpr h.2
  have hw := (withDensity_absolutelyContinuous volume
    (fun x => ENNReal.ofReal (Real.exp (-φ x)))) hall
  filter_upwards [hw] with x hx
  apply (mem_tensorTwoFormFiber_iff_compatible (WithLp.toLp 2 (fun z => f z x))).mp
  exact (mem_tensorTwoFormFiber_iff _).mpr hx

theorem tensorCurvatureZero_integrated_test_bound
    (hφ : ContDiff ℝ 2 φ)
    (F : OrderedTensorIndex n 2 → Space n → ℝ)
    (hs : ∀ x I J, List.Perm (List.ofFn I) (List.ofFn J) → F I x=F J x)
    {f : TensorTwoFormIndex n 0 → Space n → ℝ}
    {g : TensorHodgeOutputIndex n 0 → Space n → ℝ}
    (h : HasWeakConstrainedTensorHodge φ 0 f g)
    (hf : ∀ z, MemLp (f z) 2 (potentialMeasure φ))
    (hg : ∀ z, MemLp (g z) 2 (potentialMeasure φ))
    (hcurl : ∀ z, MemLp (fun x =>
      tensorCurvatureCurlZero (coordinateHessian φ x) (fun I => F I x) z) 2 (potentialMeasure φ))
    (hB : Integrable (fun x => tensorPhysicalCurvatureForm (coordinateHessian φ x)
      (fun I => F I x)) (potentialMeasure φ))
    (hFnorm : Integrable (fun x => ∑ I, (F I x)^2) (potentialMeasure φ))
    {a : ℝ} (ha : 0 ≤ a)
    (hlower : ∀ (x : Space n) (v : Fin n → ℝ),
      a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
    2*inner ℝ (finiteMatrixLp (fun z x =>
      tensorCurvatureCurlZero (coordinateHessian φ x) (fun I => F I x) z) hcurl)
      (finiteMatrixLp f hf)-‖finiteMatrixLp g hg‖^2 ≤
      (∫ x, tensorPhysicalCurvatureForm (coordinateHessian φ x) (fun I => F I x) ∂potentialMeasure φ)-
        a*(∫ x, ∑ I, (F I x)^2 ∂potentialMeasure φ) := by
  obtain ⟨hQint,hQle⟩ := maximal_tensorHodgeZero_curvature_integrable_le hφ h hf hg ha hlower
  have hpair := finiteMatrix_inner_integrable
    (fun z x => tensorCurvatureCurlZero (coordinateHessian φ x) (fun I => F I x) z) f hcurl hf
  have hp : (∫ x, 2*inner ℝ
      (tensorCurvatureCurlZero (coordinateHessian φ x) (fun I => F I x))
      (WithLp.toLp 2 (fun z => f z x))-
      tensorTwoFormCurvatureZero (coordinateHessian φ x) (fun z => f z x) ∂potentialMeasure φ) ≤
      ∫ x, tensorPhysicalCurvatureForm (coordinateHessian φ x) (fun I => F I x)-
        a*(∑ I, (F I x)^2) ∂potentialMeasure φ := by
    apply integral_mono_ae ((hpair.const_mul 2).sub hQint) (hB.sub (hFnorm.const_mul a))
    filter_upwards [weakConstrainedTensorHodgeZero_compatible_ae h] with x hx
    exact tensorCurvatureCurlZero_pairing_sub_correction_le _ (coordinateHessian_symmetric hφ x)
      (fun I => F I x) (hs x) (fun z => f z x) hx.2.1 ha (hlower x)
  rw [integral_sub ((hpair.const_mul 2)) hQint,integral_const_mul,
    integral_sub hB (hFnorm.const_mul a),integral_const_mul] at hp
  have hcross := finiteMatrixLp_inner_integral
    (fun z x => tensorCurvatureCurlZero (coordinateHessian φ x) (fun I => F I x) z) f hcurl hf
  change inner ℝ (finiteMatrixLp (fun z x =>
      tensorCurvatureCurlZero (coordinateHessian φ x) (fun I => F I x) z) hcurl) (finiteMatrixLp f hf)=
    ∫ x, inner ℝ (tensorCurvatureCurlZero (coordinateHessian φ x) (fun I => F I x))
      (WithLp.toLp 2 (fun z => f z x)) ∂potentialMeasure φ at hcross
  rw [←hcross] at hp
  linarith

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.tensorCurvatureZero_integrated_test_bound
