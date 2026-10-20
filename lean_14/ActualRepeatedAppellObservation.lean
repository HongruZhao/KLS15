import ListAppellTensorBounds
import SymmetricListExtension
import ActualQuadraticTensorObservation

/-! Actual repeated tensor integration is the factorially normalized
Appell observation, at every free tensor rank. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration KLSBelow25.GradedHilbert
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
variable {κ : ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ y (v : Fin n → ℝ),
    κ*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))

def listConstantCompatibleTensor (r : ℕ) (t : List (Fin n) → ℝ) (ht : ListTensorSymmetric t) :
    ConstantCompatibleTensorHilbert (hφ.of_le (by simp)) r :=
  ⟨orderedConstantTensorField (φ := φ) (fun I => t (List.ofFn I)),
    orderedListConstant_mem_compatible (hφ.of_le (by simp)) r t ht,by
      change orderedTensorMeanPart φ r
        (orderedConstantTensorField (φ := φ) (fun I => t (List.ofFn I)))-
          orderedConstantTensorField (φ := φ) (fun I => t (List.ofFn I))=0
      apply sub_eq_zero.mpr
      apply PiLp.ext
      intro I
      rw [orderedTensorMeanPart_apply,
        integral_congr_ae (orderedConstantTensorField_ae (fun I => t (List.ofFn I)) I)]
      simp only [integral_const,probReal_univ,one_smul,orderedConstantTensorField_apply]
      ⟩

theorem actual_repeated_observation_field (hμ : admissibleMeasure (potentialMeasure φ))
    (hiso : IsIsotropic (potentialMeasure φ)) (d r : ℕ)
    (t : List (Fin n) → ℝ) (ht : ListTensorSymmetric t)
    (x : GradedConstantTensorHilbert hφ)
    (hx : x (r+d)=listConstantCompatibleTensor hφ (r+d+1) t ht) :
    ((((gradedTensorIntegration hφ hκ hlower)^d).comp
      (gradedConstantIntegration hφ hκ hlower hiso)) x r : OrderedTensorField φ r)=
        listAppellTensorField hμ r (d+1) t := by
  induction d generalizing r with
  | zero =>
      simp only [Nat.add_zero] at hx
      change (constantTensorIntegration hφ hκ hlower r (x r) : OrderedTensorField φ r)=_
      rw [hx]
      change compatibleTensorPrimitive hφ hκ hlower r
        (orderedConstantTensorField (φ := φ) (fun I : Fin (r+1) → Fin n => t (List.ofFn I)))=_
      rw [←listAppellTensorField_zero hμ (r+1) t,
        compatibleTensorPrimitive_listAppellTensorField hφ hκ hlower hμ r 0 t ht]
  | succ d ih =>
      rw [pow_succ',ContinuousLinearMap.comp_apply,_root_.mul_apply_eq_comp]
      change compatibleTensorPrimitive hφ hκ hlower r
        (((gradedTensorIntegration hφ hκ hlower)^d)
          ((gradedConstantIntegration hφ hκ hlower hiso) x) (r+1) : OrderedTensorField φ (r+1))=_
      have hx' : x ((r+1)+d)=listConstantCompatibleTensor hφ ((r+1)+d+1) t ht := by
        have hall : ∀ s, s=r+(d+1) →
            x s=listConstantCompatibleTensor hφ (s+1) t ht := by
          intro s hs
          subst s
          exact hx
        exact hall _ (by omega)
      rw [show (((gradedTensorIntegration hφ hκ hlower)^d)
          ((gradedConstantIntegration hφ hκ hlower hiso) x) (r+1) : OrderedTensorField φ (r+1))=
          listAppellTensorField hμ (r+1) (d+1) t from ih (r+1) hx',
        compatibleTensorPrimitive_listAppellTensorField hφ hκ hlower hμ r (d+1) t ht]

theorem actual_repeated_observation_block_norm_le
    (hμ : admissibleMeasure (potentialMeasure φ)) (d r : ℕ) :
    ‖powerObservationBlock (centeredTensorIntegration hφ hκ hlower)
      (constantTensorIntegration hφ hκ hlower) (Real.sqrt_nonneg _)
      (centeredTensorIntegration_opNorm_le hφ hκ hlower) zero_le_one
      (constantTensorIntegration_opNorm_le_one hφ hκ hlower hμ.isotropic) d r‖ ≤
      ((d+1).factorial : ℝ)⁻¹ * ‖actualAppellObservation hμ (d+1)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (norm_nonneg _))
  intro F
  let T : (Fin (r+d+1) → Fin n) → ℝ := fun I => ∫ x, F.val I x ∂potentialMeasure φ
  let t : List (Fin n) → ℝ := symmetricListExtension (r+d+1) T
  have hT : ∀ I J, List.Perm (List.ofFn I) (List.ofFn J) → T I=T J := by
    intro I J hIJ
    exact congrArg (fun f : Lp ℝ 2 (potentialMeasure φ) => ∫ x, f x ∂potentialMeasure φ)
      ((mem_orderedTensorSymmetricSubspace_iff F.val).mp F.property.1.1 I J hIJ)
  have ht : ListTensorSymmetric t := symmetricListExtension_perm (r+d+1) T hT
  have hF : F=listConstantCompatibleTensor hφ (r+d+1) t ht := by
    apply Subtype.ext
    rw [constantCompatibleTensor_eq hφ (r+d+1) F]
    apply PiLp.ext
    intro I
    simp only [orderedConstantTensorField_apply]
    change T I • CenteredL2.oneLp (potentialMeasure φ)=
      symmetricListExtension (r+d+1) T (List.ofFn I) • CenteredL2.oneLp (potentialMeasure φ)
    rw [symmetricListExtension_ofFn]
  have he := actual_repeated_observation_field hφ hκ hlower hμ hμ.isotropic d r t ht
    (lp.single 2 (r+d) F) (by simpa using hF)
  have hb := listAppellTensorField_norm_sq_le hμ r (d+1) t
  rw [show (d+1)+r=r+d+1 by omega] at hb
  have hc : orderedConstantTensorField (φ := φ)
      (fun I : Fin (r+d+1) → Fin n => t (List.ofFn I))=(F : OrderedTensorField φ (r+d+1)) := by
    rw [hF]
    rfl
  rw [hc] at hb
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _)) (norm_nonneg _)) (norm_nonneg _))).mp
  change ‖((((gradedTensorIntegration hφ hκ hlower)^d).comp
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic)) (lp.single 2 (r+d) F) r :
        OrderedTensorField φ r)‖^2 ≤ _
  rw [he]
  change ‖listAppellTensorField hμ r (d+1) t‖^2 ≤
    (((d+1).factorial : ℝ)⁻¹ * ‖actualAppellObservation hμ (d+1)‖ *
      ‖(F : OrderedTensorField φ (r+d+1))‖)^2
  simpa only [mul_pow,mul_assoc] using hb

theorem actual_repeated_observation_norm_le
    (hμ : admissibleMeasure (potentialMeasure φ)) (d : ℕ) :
    ‖((gradedTensorIntegration hφ hκ hlower)^d).comp
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic)‖ ≤
      ((d+1).factorial : ℝ)⁻¹ * ‖actualAppellObservation hμ (d+1)‖ :=
  norm_power_observation_le_of_blocks _ _ _ _ _ _ d
    (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (norm_nonneg _))
    (actual_repeated_observation_block_norm_le hφ hκ hlower hμ d)

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_repeated_observation_field
#print axioms KLS.DeterministicBridgeNext.actual_repeated_observation_block_norm_le
#print axioms KLS.DeterministicBridgeNext.actual_repeated_observation_norm_le
