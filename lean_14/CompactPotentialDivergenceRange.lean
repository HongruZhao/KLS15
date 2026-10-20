import CenteredTensorZero
import TensorInverseAdjointCore
import KLS.DirectionalWordAffine

/-! The actual projected-divergence image of C∞ compact potentials is a
linear subspace. Triviality of its actual annihilator gives density of
the image itself, rather than only density of its span. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n r : ℕ} {φ : Space n → ℝ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def compactSmoothPotentialSubmodule (n : ℕ) : Submodule ℝ (Space n → ℝ) where
  carrier := {ψ | ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ}
  zero_mem' := ⟨contDiff_const,HasCompactSupport.zero⟩
  add_mem' hp hq := ⟨hp.1.add hq.1,hp.2.add hq.2⟩
  smul_mem' c ψ hp := ⟨hp.1.const_smul c,by
    change HasCompactSupport (fun x => c*ψ x)
    exact hp.2.mul_left (f := fun _ => c)⟩

def compactPotentialAdjointDivergenceLp (hφ : ContDiff ℝ 2 φ)
    (ψ : compactSmoothPotentialSubmodule n) (r : ℕ) : OrderedTensorField φ r :=
  tensorAdjointDivergenceLp hφ
    (fun I => (coordinatePotentialTensor_contDiff ψ.property.1 (r+1) I).of_le (by simp))
    (coordinatePotentialTensor_hasCompactSupport ψ.property.2 (r+1))

lemma coordinatePotentialTensor_add
    {ψ θ : Space n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (r : ℕ) (I : OrderedTensorIndex n r) :
    coordinatePotentialTensor (ψ+θ) r I =
      coordinatePotentialTensor ψ r I+coordinatePotentialTensor θ r I := by
  funext x
  exact directionalWordDerivative_add hψ hθ _ x

lemma coordinatePotentialTensor_smul
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (c : ℝ)
    (r : ℕ) (I : OrderedTensorIndex n r) :
    coordinatePotentialTensor (c • ψ) r I = c • coordinatePotentialTensor ψ r I := by
  funext x
  exact directionalWordDerivative_const_mul hψ c _ x

lemma compactPotentialAdjointDivergenceLp_add (hφ : ContDiff ℝ 2 φ)
    (ψ θ : compactSmoothPotentialSubmodule n) (r : ℕ) :
    compactPotentialAdjointDivergenceLp hφ (ψ+θ) r =
      compactPotentialAdjointDivergenceLp hφ ψ r+compactPotentialAdjointDivergenceLp hφ θ r := by
  apply PiLp.ext
  intro I
  apply Lp.ext
  have hA := tensorAdjointDivergenceLp_ae hφ
    (fun J => (coordinatePotentialTensor_contDiff (ψ+θ).property.1 (r+1) J).of_le (by simp))
    (coordinatePotentialTensor_hasCompactSupport (ψ+θ).property.2 (r+1)) I
  have hB := tensorAdjointDivergenceLp_ae hφ
    (fun J => (coordinatePotentialTensor_contDiff ψ.property.1 (r+1) J).of_le (by simp))
    (coordinatePotentialTensor_hasCompactSupport ψ.property.2 (r+1)) I
  have hC := tensorAdjointDivergenceLp_ae hφ
    (fun J => (coordinatePotentialTensor_contDiff θ.property.1 (r+1) J).of_le (by simp))
    (coordinatePotentialTensor_hasCompactSupport θ.property.2 (r+1)) I
  have hsum := Lp.coeFn_add (compactPotentialAdjointDivergenceLp hφ ψ r I)
    (compactPotentialAdjointDivergenceLp hφ θ r I)
  filter_upwards [hA,hB,hC,hsum] with x hAx hBx hCx hsx
  change compactPotentialAdjointDivergenceLp hφ (ψ+θ) r I x =
    (compactPotentialAdjointDivergenceLp hφ ψ r I+compactPotentialAdjointDivergenceLp hφ θ r I) x
  rw [hsx]
  simp only [Pi.add_apply]
  simp only [compactPotentialAdjointDivergenceLp]
  rw [hAx,hBx,hCx]
  have he (j : Fin n) := coordinatePotentialTensor_add ψ.property.1 θ.property.1
    (r+1) (Fin.cons j I)
  unfold tensorAdjointDivergence
  change -(∑ j, weightedDerivativeTest φ
    (coordinatePotentialTensor ((ψ : Space n → ℝ)+(θ : Space n → ℝ)) (r+1) (Fin.cons j I)) j x) = _
  simp_rw [he]
  have hd (j : Fin n) := coordinateDerivative_add
    ((coordinatePotentialTensor_contDiff ψ.property.1 (r+1) (Fin.cons j I)).differentiable (by simp) x)
    ((coordinatePotentialTensor_contDiff θ.property.1 (r+1) (Fin.cons j I)).differentiable (by simp) x) j
  simp only [weightedDerivativeTest,hd,Pi.add_apply]
  simp only [add_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  ring

lemma compactPotentialAdjointDivergenceLp_smul (hφ : ContDiff ℝ 2 φ)
    (ψ : compactSmoothPotentialSubmodule n) (c : ℝ) (r : ℕ) :
    compactPotentialAdjointDivergenceLp hφ (c • ψ) r =
      c • compactPotentialAdjointDivergenceLp hφ ψ r := by
  apply PiLp.ext
  intro I
  apply Lp.ext
  have hA := tensorAdjointDivergenceLp_ae hφ
    (fun J => (coordinatePotentialTensor_contDiff (c • ψ).property.1 (r+1) J).of_le (by simp))
    (coordinatePotentialTensor_hasCompactSupport (c • ψ).property.2 (r+1)) I
  have hB := tensorAdjointDivergenceLp_ae hφ
    (fun J => (coordinatePotentialTensor_contDiff ψ.property.1 (r+1) J).of_le (by simp))
    (coordinatePotentialTensor_hasCompactSupport ψ.property.2 (r+1)) I
  have hsmul := Lp.coeFn_smul c (compactPotentialAdjointDivergenceLp hφ ψ r I)
  filter_upwards [hA,hB,hsmul] with x hAx hBx hsx
  change compactPotentialAdjointDivergenceLp hφ (c • ψ) r I x =
    (c • compactPotentialAdjointDivergenceLp hφ ψ r I) x
  rw [hsx]
  simp only [Pi.smul_apply,smul_eq_mul]
  simp only [compactPotentialAdjointDivergenceLp]
  rw [hAx,hBx]
  have he (j : Fin n) := coordinatePotentialTensor_smul ψ.property.1 c
    (r+1) (Fin.cons j I)
  unfold tensorAdjointDivergence
  change -(∑ j, weightedDerivativeTest φ
    (coordinatePotentialTensor (c • (ψ : Space n → ℝ)) (r+1) (Fin.cons j I)) j x) = _
  simp_rw [he]
  have hd (j : Fin n) := coordinateDerivative_smul
    ((coordinatePotentialTensor_contDiff ψ.property.1 (r+1) (Fin.cons j I)).differentiable (by simp) x) c j
  simp only [weightedDerivativeTest,hd,Pi.smul_apply,smul_eq_mul]
  have hf (j : Fin n) :
      c*coordinateDerivative (coordinatePotentialTensor (ψ : Space n → ℝ) (r+1) (Fin.cons j I)) j x-
        c*coordinatePotentialTensor (ψ : Space n → ℝ) (r+1) (Fin.cons j I) x*coordinateDerivative φ j x =
      c*(coordinateDerivative (coordinatePotentialTensor (ψ : Space n → ℝ) (r+1) (Fin.cons j I)) j x-
        coordinatePotentialTensor (ψ : Space n → ℝ) (r+1) (Fin.cons j I) x*coordinateDerivative φ j x) := by ring
  simp_rw [hf]
  rw [← Finset.mul_sum]
  ring

section Probability
variable [IsProbabilityMeasure (potentialMeasure φ)]

def compactPotentialDivergenceFromTest (hφ : ContDiff ℝ 2 φ) (r : ℕ)
    (ψ : compactSmoothPotentialSubmodule n) :
    CenteredCompatibleTensorHilbert (hφ.of_le (by norm_num)) r :=
  ⟨tensorCompactProjection (hφ.of_le (by norm_num)) r
      (compactPotentialAdjointDivergenceLp hφ ψ r),
    projectedTensorDivergence_mem_centered hφ _ _⟩

lemma compactPotentialDivergenceFromTest_coe (hφ : ContDiff ℝ 2 φ) (r : ℕ)
    (ψ : compactSmoothPotentialSubmodule n) :
    (compactPotentialDivergenceFromTest hφ r ψ : OrderedTensorField φ r) =
      compactPotentialProjectedDivergence hφ ψ.property.1 ψ.property.2 r := rfl

def compactPotentialDivergenceLinearMap (hφ : ContDiff ℝ 2 φ) (r : ℕ) :
    compactSmoothPotentialSubmodule n →ₗ[ℝ]
      CenteredCompatibleTensorHilbert (hφ.of_le (by norm_num)) r where
  toFun := compactPotentialDivergenceFromTest hφ r
  map_add' ψ θ := by
    apply Subtype.ext
    change tensorCompactProjection _ r (compactPotentialAdjointDivergenceLp hφ (ψ+θ) r) = _
    rw [compactPotentialAdjointDivergenceLp_add,map_add]
    rfl
  map_smul' c ψ := by
    apply Subtype.ext
    change tensorCompactProjection _ r (compactPotentialAdjointDivergenceLp hφ (c • ψ) r) = _
    rw [compactPotentialAdjointDivergenceLp_smul,map_smul]
    rfl

/-- The literal compact-potential divergence image, as a submodule. -/
def compactPotentialDivergenceRange (hφ : ContDiff ℝ 2 φ) (r : ℕ) :
    Submodule ℝ (CenteredCompatibleTensorHilbert (hφ.of_le (by norm_num)) r) :=
  (compactPotentialDivergenceLinearMap hφ r).range

/-- A zero actual annihilator makes the actual image dense. No span or
finite-combination enlargement occurs in the conclusion. -/
theorem dense_compactPotentialDivergenceRange
    (hφ : ContDiff ℝ 2 φ) (r : ℕ)
    (hzero : ∀ U : CenteredCompatibleTensorHilbert (hφ.of_le (by norm_num)) r,
      (∀ ψ : compactSmoothPotentialSubmodule n,
        inner ℝ U (compactPotentialDivergenceFromTest hφ r ψ)=0) → U=0) :
    Dense (Set.range (compactPotentialDivergenceFromTest hφ r)) := by
  have ho : (compactPotentialDivergenceRange hφ r)ᗮ=⊥ := by
    apply le_antisymm ?_ bot_le
    intro U hU
    change U=0
    apply hzero U
    intro ψ
    exact (Submodule.mem_orthogonal' _ _).mp hU
      (compactPotentialDivergenceFromTest hφ r ψ) ⟨ψ,rfl⟩
  have hd : Dense ((compactPotentialDivergenceRange hφ r) : Set
      (CenteredCompatibleTensorHilbert (hφ.of_le (by norm_num)) r)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (Submodule.topologicalClosure_eq_top_iff.mpr ho)
  exact hd

/-- The same density criterion in the original compact smooth test syntax. -/
theorem dense_compactPotentialDivergenceRange_of_tests
    (hφ : ContDiff ℝ 2 φ) (r : ℕ)
    (hzero : ∀ U : CenteredCompatibleTensorHilbert (hφ.of_le (by norm_num)) r,
      (∀ (ψ : Space n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ),
        inner ℝ (U : OrderedTensorField φ r)
          (compactPotentialProjectedDivergence hφ hψ hc r)=0) → U=0) :
    Dense (Set.range (compactPotentialDivergenceFromTest hφ r)) := by
  apply dense_compactPotentialDivergenceRange hφ r
  intro U hU
  apply hzero U
  intro ψ hψ hc
  exact hU ⟨ψ,hψ,hc⟩

end Probability
end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialDivergenceLinearMap
#print axioms KLS.DeterministicBridgeIntegration.dense_compactPotentialDivergenceRange_of_tests
