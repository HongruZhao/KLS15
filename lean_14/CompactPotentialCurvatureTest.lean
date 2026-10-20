import TensorIntegratedCurvatureCoupling
import CompactPotentialRankZeroCurvature

/-! The full-domain completed-square test bound with an actual compact
potential, with all ordinary coefficient integrability proved internally. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators ENNReal RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
open KLS
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {n r : ℕ} {φ ψ : Space n → ℝ}

lemma tensorCurvatureCurl_coefficient_continuous (hφ : ContDiff ℝ 2 φ)
    {F : OrderedTensorIndex n (r+3) → Space n → ℝ} (hF : ∀ I, Continuous (F I))
    (z : TensorTwoFormIndex n (r+1)) :
    Continuous (fun x => tensorCurvatureCurl (coordinateHessian φ x) (fun I => F I x) z) := by
  have hK (i j : Fin n) : Continuous (fun x => coordinateHessian φ x i j) :=
    (contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous
  unfold tensorCurvatureCurl
  simp only [PiLp.toLp_apply]
  fun_prop

lemma tensorCurvatureCurl_coefficient_compact
    {F : OrderedTensorIndex n (r+3) → Space n → ℝ}
    (hc : ∀ I, HasCompactSupport (F I)) (z : TensorTwoFormIndex n (r+1)) :
    HasCompactSupport (fun x => tensorCurvatureCurl (coordinateHessian φ x) (fun I => F I x) z) := by
  have hs := compactSupport_finsetSum (n := n) Finset.univ (fun j _ =>
    ((hc (Fin.cons j (Fin.cons z.2.2 z.1))).mul_left (f := fun x => coordinateHessian φ x z.2.1 j)).sub
      ((hc (Fin.cons j (Fin.cons z.2.1 z.1))).mul_left (f := fun x => coordinateHessian φ x z.2.2 j)))
  exact hs.mul_left

lemma compactPotentialCurvatureCurl_memLp (hφ : ContDiff ℝ 2 φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (z : TensorTwoFormIndex n (r+1)) :
    MemLp (fun x => tensorCurvatureCurl (coordinateHessian φ x)
      (fun I => coordinatePotentialTensor ψ (r+3) I x) z) 2 (potentialMeasure φ) :=
  memLp_of_continuous_hasCompactSupport hφ.continuous
    (tensorCurvatureCurl_coefficient_continuous hφ
      (fun I => (coordinatePotentialTensor_contDiff hψ (r+3) I).continuous) z)
    (tensorCurvatureCurl_coefficient_compact (coordinatePotentialTensor_hasCompactSupport hc (r+3)) z)

def compactPotentialCurvatureCurlLp (hφ : ContDiff ℝ 2 φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℕ) :
    CenteredL2.Family (potentialMeasure φ) (TensorTwoFormIndex n (r+1)) :=
  finiteMatrixLp (fun z x => tensorCurvatureCurl (coordinateHessian φ x)
    (fun I => coordinatePotentialTensor ψ (r+3) I x) z)
    (compactPotentialCurvatureCurl_memLp hφ hψ hc)

theorem compactPotential_curvature_test_bound
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    {f : TensorTwoFormIndex n (r+1) → Space n → ℝ}
    {g : TensorHodgeOutputIndex n (r+1) → Space n → ℝ}
    (h : HasWeakConstrainedTensorHodge φ (r+1) f g)
    (hf : ∀ z, MemLp (f z) 2 (potentialMeasure φ))
    (hg : ∀ z, MemLp (g z) 2 (potentialMeasure φ))
    {a : ℝ} (ha : 0 ≤ a)
    (hlower : ∀ (x : Space n) (v : Fin n → ℝ),
      a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
    2*inner ℝ (compactPotentialCurvatureCurlLp hφ hψ hc r) (finiteMatrixLp f hf)-
      ‖finiteMatrixLp g hg‖^2 ≤ compactPotentialCurvatureEnergy φ ψ (r+2)-
        a*‖compactPotentialTensorLp hφ.continuous hψ hc (r+3)‖^2 := by
  have hsq (I : OrderedTensorIndex n (r+3)) :
      Integrable (fun x => (coordinatePotentialTensor ψ (r+3) I x)^2) (potentialMeasure φ) :=
    (memLp_of_continuous_hasCompactSupport hφ.continuous
      (coordinatePotentialTensor_contDiff hψ (r+3) I).continuous
      (coordinatePotentialTensor_hasCompactSupport hc (r+3) I)).integrable_sq
  have hB := integrable_compactTensorPhysicalCurvatureForm hφ
    (coordinatePotentialTensor ψ (r+3))
    (fun I => (coordinatePotentialTensor_contDiff hψ (r+3) I).continuous)
    (coordinatePotentialTensor_hasCompactSupport hc (r+3))
  have hb := tensorCurvature_integrated_test_bound hφ (coordinatePotentialTensor ψ (r+3))
    (fun x I J hp => congrFun (coordinatePotentialTensor_symmetric hψ (r+3) I J hp) x)
    h hf hg (compactPotentialCurvatureCurl_memLp hφ hψ hc) hB
    (integrable_finsetSum Finset.univ (fun I _ => hsq I)) ha hlower
  change 2*inner ℝ (compactPotentialCurvatureCurlLp hφ hψ hc r) (finiteMatrixLp f hf)-
      ‖finiteMatrixLp g hg‖^2 ≤ compactPotentialCurvatureEnergy φ ψ (r+2)-
        a*(∫ x, ∑ I, (coordinatePotentialTensor ψ (r+3) I x)^2 ∂potentialMeasure φ) at hb
  rw [integral_finsetSum Finset.univ (fun I _ => hsq I)] at hb
  rw [←compactTensorLp_norm_sq_integral hφ.continuous (coordinatePotentialTensor ψ (r+3))
    (fun I => (coordinatePotentialTensor_contDiff hψ (r+3) I).continuous)
    (coordinatePotentialTensor_hasCompactSupport hc (r+3))] at hb
  exact hb

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.compactPotential_curvature_test_bound
