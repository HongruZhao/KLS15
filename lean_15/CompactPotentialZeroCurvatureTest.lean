import TensorZeroIntegratedCurvatureCoupling
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
variable {n : ℕ} {φ ψ : Space n → ℝ}

lemma tensorCurvatureCurlZero_coefficient_continuous (hφ : ContDiff ℝ 2 φ)
    {F : OrderedTensorIndex n 2 → Space n → ℝ} (hF : ∀ I, Continuous (F I))
    (z : TensorTwoFormIndex n 0) :
    Continuous (fun x => tensorCurvatureCurlZero (coordinateHessian φ x) (fun I => F I x) z) := by
  have hK (i j : Fin n) : Continuous (fun x => coordinateHessian φ x i j) :=
    (contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous
  unfold tensorCurvatureCurlZero
  simp only [PiLp.toLp_apply]
  fun_prop

lemma tensorCurvatureCurlZero_coefficient_compact
    {F : OrderedTensorIndex n 2 → Space n → ℝ}
    (hc : ∀ I, HasCompactSupport (F I)) (z : TensorTwoFormIndex n 0) :
    HasCompactSupport (fun x => tensorCurvatureCurlZero (coordinateHessian φ x) (fun I => F I x) z) := by
  have hs := compactSupport_finsetSum (n := n) Finset.univ (fun j _ =>
    ((hc (Fin.cons j (Fin.cons z.2.2 z.1))).mul_left (f := fun x => coordinateHessian φ x z.2.1 j)).sub
      ((hc (Fin.cons j (Fin.cons z.2.1 z.1))).mul_left (f := fun x => coordinateHessian φ x z.2.2 j)))
  exact hs.mul_left

lemma compactPotentialCurvatureCurlZero_memLp (hφ : ContDiff ℝ 2 φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (z : TensorTwoFormIndex n 0) :
    MemLp (fun x => tensorCurvatureCurlZero (coordinateHessian φ x)
      (fun I => coordinatePotentialTensor ψ 2 I x) z) 2 (potentialMeasure φ) :=
  memLp_of_continuous_hasCompactSupport hφ.continuous
    (tensorCurvatureCurlZero_coefficient_continuous hφ
      (fun I => (coordinatePotentialTensor_contDiff hψ 2 I).continuous) z)
    (tensorCurvatureCurlZero_coefficient_compact (coordinatePotentialTensor_hasCompactSupport hc 2) z)

def compactPotentialCurvatureCurlZeroLp (hφ : ContDiff ℝ 2 φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    CenteredL2.Family (potentialMeasure φ) (TensorTwoFormIndex n 0) :=
  finiteMatrixLp (fun z x => tensorCurvatureCurlZero (coordinateHessian φ x)
    (fun I => coordinatePotentialTensor ψ 2 I x) z)
    (compactPotentialCurvatureCurlZero_memLp hφ hψ hc)

theorem compactPotentialZero_curvature_test_bound
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    {f : TensorTwoFormIndex n 0 → Space n → ℝ}
    {g : TensorHodgeOutputIndex n 0 → Space n → ℝ}
    (h : HasWeakConstrainedTensorHodge φ 0 f g)
    (hf : ∀ z, MemLp (f z) 2 (potentialMeasure φ))
    (hg : ∀ z, MemLp (g z) 2 (potentialMeasure φ))
    {a : ℝ} (ha : 0 ≤ a)
    (hlower : ∀ (x : Space n) (v : Fin n → ℝ),
      a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
    2*inner ℝ (compactPotentialCurvatureCurlZeroLp hφ hψ hc) (finiteMatrixLp f hf)-
      ‖finiteMatrixLp g hg‖^2 ≤ compactPotentialCurvatureEnergy φ ψ 1-
        a*‖compactPotentialTensorLp hφ.continuous hψ hc 2‖^2 := by
  have hsq (I : OrderedTensorIndex n 2) :
      Integrable (fun x => (coordinatePotentialTensor ψ 2 I x)^2) (potentialMeasure φ) :=
    (memLp_of_continuous_hasCompactSupport hφ.continuous
      (coordinatePotentialTensor_contDiff hψ 2 I).continuous
      (coordinatePotentialTensor_hasCompactSupport hc 2 I)).integrable_sq
  have hB := integrable_compactTensorPhysicalCurvatureForm hφ
    (coordinatePotentialTensor ψ 2)
    (fun I => (coordinatePotentialTensor_contDiff hψ 2 I).continuous)
    (coordinatePotentialTensor_hasCompactSupport hc 2)
  have hb := tensorCurvatureZero_integrated_test_bound hφ (coordinatePotentialTensor ψ 2)
    (fun x I J hp => congrFun (coordinatePotentialTensor_symmetric hψ 2 I J hp) x)
    h hf hg (compactPotentialCurvatureCurlZero_memLp hφ hψ hc) hB
    (integrable_finsetSum Finset.univ (fun I _ => hsq I)) ha hlower
  change 2*inner ℝ (compactPotentialCurvatureCurlZeroLp hφ hψ hc) (finiteMatrixLp f hf)-
      ‖finiteMatrixLp g hg‖^2 ≤ compactPotentialCurvatureEnergy φ ψ 1-
        a*(∫ x, ∑ I, (coordinatePotentialTensor ψ 2 I x)^2 ∂potentialMeasure φ) at hb
  rw [integral_finsetSum Finset.univ (fun I _ => hsq I)] at hb
  rw [←compactTensorLp_norm_sq_integral hφ.continuous (coordinatePotentialTensor ψ 2)
    (fun I => (coordinatePotentialTensor_contDiff hψ 2 I).continuous)
    (coordinatePotentialTensor_hasCompactSupport hc 2)] at hb
  exact hb

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialZero_curvature_test_bound
