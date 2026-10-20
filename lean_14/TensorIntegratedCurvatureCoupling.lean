import TensorMaximalCurvatureEnergy
import TensorCurvatureCoupling

/-! Integration of the actual pointwise completed square against an
arbitrary full-domain constrained Hodge test. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators ENNReal RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
open KLS
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n r : ℕ} {φ : Space n → ℝ}

lemma finiteMatrixLp_inner_integral {ι : Type*} [Fintype ι] {μ : Measure (Space n)}
    (f g : ι → Space n → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ) :
    inner ℝ (finiteMatrixLp f hf) (finiteMatrixLp g hg)=
      ∫ x, inner ℝ (WithLp.toLp 2 (fun i => f i x)) (WithLp.toLp 2 (fun i => g i x)) ∂μ := by
  have hp (i : ι) : Integrable (fun x => g i x*f i x) μ := (hg i).integrable_mul (hf i)
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,PiLp.toLp_apply]
  rw [integral_finsetSum Finset.univ (fun i _ => hp i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hf i).coeFn_toLp,(hg i).coeFn_toLp] with x hfx hgx
  simp only [finiteMatrixLp,RCLike.inner_apply,conj_trivial,hfx,hgx]

lemma finiteMatrix_inner_integrable {ι : Type*} [Fintype ι] {μ : Measure (Space n)}
    (f g : ι → Space n → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ) :
    Integrable (fun x => inner ℝ (WithLp.toLp 2 (fun i => f i x))
      (WithLp.toLp 2 (fun i => g i x))) μ := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,PiLp.toLp_apply]
  exact integrable_finsetSum Finset.univ (fun i _ => (hg i).integrable_mul (hf i))

theorem tensorCurvature_integrated_test_bound
    (hφ : ContDiff ℝ 2 φ)
    (F : OrderedTensorIndex n (r+3) → Space n → ℝ)
    (hs : ∀ x I J, List.Perm (List.ofFn I) (List.ofFn J) → F I x=F J x)
    {f : TensorTwoFormIndex n (r+1) → Space n → ℝ}
    {g : TensorHodgeOutputIndex n (r+1) → Space n → ℝ}
    (h : HasWeakConstrainedTensorHodge φ (r+1) f g)
    (hf : ∀ z, MemLp (f z) 2 (potentialMeasure φ))
    (hg : ∀ z, MemLp (g z) 2 (potentialMeasure φ))
    (hcurl : ∀ z, MemLp (fun x =>
      tensorCurvatureCurl (coordinateHessian φ x) (fun I => F I x) z) 2 (potentialMeasure φ))
    (hB : Integrable (fun x => tensorPhysicalCurvatureForm (coordinateHessian φ x)
      (fun I => F I x)) (potentialMeasure φ))
    (hFnorm : Integrable (fun x => ∑ I, (F I x)^2) (potentialMeasure φ))
    {a : ℝ} (ha : 0 ≤ a)
    (hlower : ∀ (x : Space n) (v : Fin n → ℝ),
      a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
    2*inner ℝ (finiteMatrixLp (fun z x =>
      tensorCurvatureCurl (coordinateHessian φ x) (fun I => F I x) z) hcurl)
      (finiteMatrixLp f hf)-‖finiteMatrixLp g hg‖^2 ≤
      (∫ x, tensorPhysicalCurvatureForm (coordinateHessian φ x) (fun I => F I x) ∂potentialMeasure φ)-
        a*(∫ x, ∑ I, (F I x)^2 ∂potentialMeasure φ) := by
  obtain ⟨hQint,hQle⟩ := maximal_tensorHodge_curvature_integrable_le hφ h hf hg ha hlower
  have hpair := finiteMatrix_inner_integrable
    (fun z x => tensorCurvatureCurl (coordinateHessian φ x) (fun I => F I x) z) f hcurl hf
  have hp : (∫ x, 2*inner ℝ
      (tensorCurvatureCurl (coordinateHessian φ x) (fun I => F I x))
      (WithLp.toLp 2 (fun z => f z x))-
      tensorTwoFormCurvatureCorrection (coordinateHessian φ x) (fun z => f z x) ∂potentialMeasure φ) ≤
      ∫ x, tensorPhysicalCurvatureForm (coordinateHessian φ x) (fun I => F I x)-
        a*(∑ I, (F I x)^2) ∂potentialMeasure φ := by
    apply integral_mono_ae ((hpair.const_mul 2).sub hQint) (hB.sub (hFnorm.const_mul a))
    filter_upwards [weakConstrainedTensorHodge_compatible_ae h] with x hx
    exact tensorCurvatureCurl_pairing_sub_correction_le _ (coordinateHessian_symmetric hφ x)
      (fun I => F I x) (hs x) (fun z => f z x) hx ha (hlower x)
  rw [integral_sub ((hpair.const_mul 2)) hQint,integral_const_mul,
    integral_sub hB (hFnorm.const_mul a),integral_const_mul] at hp
  have hcross := finiteMatrixLp_inner_integral
    (fun z x => tensorCurvatureCurl (coordinateHessian φ x) (fun I => F I x) z) f hcurl hf
  change inner ℝ (finiteMatrixLp (fun z x =>
      tensorCurvatureCurl (coordinateHessian φ x) (fun I => F I x) z) hcurl) (finiteMatrixLp f hf)=
    ∫ x, inner ℝ (tensorCurvatureCurl (coordinateHessian φ x) (fun I => F I x))
      (WithLp.toLp 2 (fun z => f z x)) ∂potentialMeasure φ at hcross
  rw [←hcross] at hp
  linarith

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.tensorCurvature_integrated_test_bound
