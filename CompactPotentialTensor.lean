import ProjectedTensorDivergence
import KLS.DirectionalWordSymmetry

/-! The literal compact potential tensor family Kₛ = {∇ˢψ : ψ∈C∞c}.
Actual derivative words prove symmetry, compatibility, compact support,
and membership in the already constructed closed Cₛ space at every rank.
No density of Kₛ or of its projected divergences is postulated. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ} {φ ψ : Space n → ℝ}

def coordinatePotentialTensor (ψ : Space n → ℝ) (r : ℕ)
    (I : OrderedTensorIndex n r) : Space n → ℝ :=
  directionalWordDerivative ψ ((List.ofFn I).map (fun i => EuclideanSpace.single i 1))

lemma coordinatePotentialTensor_cons (ψ : Space n → ℝ) (I : OrderedTensorIndex n r) (i : Fin n) :
    coordinatePotentialTensor ψ (r + 1) (Fin.cons i I) =
      coordinateDerivative (coordinatePotentialTensor ψ r I) i := by
  funext x
  simp only [coordinatePotentialTensor, List.ofFn_cons, List.map_cons,
    directionalWordDerivative_cons, coordinateDerivative]

lemma coordinatePotentialTensor_contDiff (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (r : ℕ) (I : OrderedTensorIndex n r) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinatePotentialTensor ψ r I) :=
  contDiff_directionalWordDerivative hψ _

lemma coordinatePotentialTensor_hasCompactSupport (hc : HasCompactSupport ψ)
    (r : ℕ) (I : OrderedTensorIndex n r) :
    HasCompactSupport (coordinatePotentialTensor ψ r I) := by
  induction r with
  | zero => simpa only [coordinatePotentialTensor, List.ofFn_zero, List.map_nil,
      directionalWordDerivative_nil] using hc
  | succ r ih =>
    rw [← Fin.cons_self_tail I, coordinatePotentialTensor_cons]
    exact hasCompactSupport_coordinateDerivative (ih (Fin.tail I)) (I 0)

lemma coordinatePotentialTensor_symmetric (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℕ) :
    classicalTensorSymmetric (coordinatePotentialTensor ψ r) := by
  intro I J hIJ
  exact directionalWordDerivative_perm hψ (hIJ.map (fun i => EuclideanSpace.single i 1))

lemma coordinatePotentialTensor_compatible (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℕ) :
    classicalTensorCompatible (coordinatePotentialTensor ψ (r + 1)) := by
  intro I θ hθ hc i j
  have hFi (i : Fin n) := coordinatePotentialTensor_contDiff hψ (r + 1) (Fin.cons i I)
  have hi := hasLocalWeakCoordinateDerivative_of_locallyLipschitz
    ((hFi i).of_le (by simp) : ContDiff ℝ 1 _).locallyLipschitz j θ (hθ.of_le (by simp)) hc
  have hj := hasLocalWeakCoordinateDerivative_of_locallyLipschitz
    ((hFi j).of_le (by simp) : ContDiff ℝ 1 _).locallyLipschitz i θ (hθ.of_le (by simp)) hc
  have hd : coordinateDerivative (coordinatePotentialTensor ψ (r + 1) (Fin.cons i I)) j =
      coordinateDerivative (coordinatePotentialTensor ψ (r + 1) (Fin.cons j I)) i := by
    rw [← coordinatePotentialTensor_cons, ← coordinatePotentialTensor_cons]
    exact classicalTensorSymmetric_swap (coordinatePotentialTensor_symmetric hψ (r + 2)) I j i
  rw [hd] at hi
  exact hi.trans hj.symm

lemma compactTensorLp_mem_compatible (hφ : ContDiff ℝ 1 φ)
    (F : OrderedTensorIndex n r → Space n → ℝ)
    (hF : ∀ I, Continuous (F I)) (hc : ∀ I, HasCompactSupport (F I))
    (hsym : classicalTensorSymmetric F)
    (hcomp : match r with | 0 => True | s + 1 => classicalTensorCompatible F) :
    compactTensorLp hφ.continuous F hF hc ∈ compatibleSymmetricTensorSubspace hφ r := by
  constructor
  · change compactTensorLp hφ.continuous F hF hc ∈ orderedTensorSymmetricSubspace φ r
    rw [mem_orderedTensorSymmetricSubspace_iff]
    intro I J hIJ
    apply Lp.ext
    filter_upwards [compactTensorLp_ae hφ.continuous F hF hc I,
      compactTensorLp_ae hφ.continuous F hF hc J] with x hx hy
    rw [hx, hy, congrFun (hsym I J hIJ) x]
  · cases r with
    | zero => trivial
    | succ r =>
      have hcompat : classicalTensorCompatible F := hcomp
      change compactTensorLp hφ.continuous F hF hc ∈ orderedTensorCurlSubspace hφ (r + 1)
      rw [mem_orderedTensorCurlSubspace_succ_iff]
      intro I
      rw [mem_weightedCurlFreeSubspace_iff]
      intro θ hθ hθc i j
      have hae (k : Fin n) :
          (orderedTensorSlice r I (compactTensorLp hφ.continuous F hF hc) k : Space n → ℝ)
            =ᵐ[volume] F (Fin.cons k I) :=
        (volume_absolutelyContinuous_potentialMeasure hφ.continuous).ae_eq
          (compactTensorLp_ae hφ.continuous F hF hc (Fin.cons k I))
      calc
        _ = ∫ x, F (Fin.cons i I) x * coordinateDerivative θ j x :=
          integral_congr_ae ((hae i).fun_mul EventuallyEq.rfl)
        _ = ∫ x, F (Fin.cons j I) x * coordinateDerivative θ i x := hcompat I θ hθ hθc i j
        _ = _ := (integral_congr_ae ((hae j).fun_mul EventuallyEq.rfl)).symm

def compactPotentialTensorLp (hφ : Continuous φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (r : ℕ) : OrderedTensorField φ r :=
  compactTensorLp hφ (coordinatePotentialTensor ψ r)
    (fun I => (coordinatePotentialTensor_contDiff hψ r I).continuous)
    (coordinatePotentialTensor_hasCompactSupport hc r)

theorem compactPotentialTensorLp_mem (hφ : ContDiff ℝ 1 φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℕ) :
    compactPotentialTensorLp hφ.continuous hψ hc r ∈ compatibleSymmetricTensorSubspace hφ r := by
  apply compactTensorLp_mem_compatible hφ _ _ _ (coordinatePotentialTensor_symmetric hψ r)
  cases r with
  | zero => trivial
  | succ r => exact coordinatePotentialTensor_compatible hψ r

/-- The actual projected compact-potential divergence Sᵣ∇ʳ⁺¹ψ. -/
def compactPotentialProjectedDivergence (hφ : ContDiff ℝ 2 φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℕ) : OrderedTensorField φ r :=
  projectedTensorDivergence hφ
    (fun I => (coordinatePotentialTensor_contDiff hψ (r + 1) I).of_le (by simp))
    (coordinatePotentialTensor_hasCompactSupport hc (r + 1))

theorem compactPotentialProjectedDivergence_mem (hφ : ContDiff ℝ 2 φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℕ) :
    compactPotentialProjectedDivergence hφ hψ hc r ∈
      compatibleSymmetricTensorSubspace (hφ.of_le (by norm_num)) r :=
  Submodule.starProjection_apply_mem _ _

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.coordinatePotentialTensor_symmetric
#print axioms KLS.DeterministicBridgeIntegration.coordinatePotentialTensor_compatible
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialTensorLp_mem
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialProjectedDivergence_mem
