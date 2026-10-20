import ActualQuadraticPrimitive
import GradedPowerObservation

/-! Literal quadratic observation bound for the actual compatible tensor
integration operators, uniformly in the number of free tensor indices. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix Set Filter
open scoped ContDiff BigOperators RealInnerProductSpace ENNReal
namespace KLS.DeterministicBridgeIntegration
open KLS.DeterministicBridge KLSBelow25.GradedHilbert
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

theorem constantCompatibleTensor_eq (r : ℕ)
    (F : ConstantCompatibleTensorHilbert (hφ.of_le (by simp)) r) :
    (F : OrderedTensorField φ r)=orderedConstantTensorField (φ := φ)
      (fun I => ∫ x, F.val I x ∂potentialMeasure φ) := by
  have he : orderedTensorMeanPart φ r F-(F : OrderedTensorField φ r)=0 := F.property.2
  rw [←orderedTensorMeanPart_eq_constant]
  exact (sub_eq_zero.mp he).symm

theorem quadratic_tensor_observation_norm_sq_le (hμ : admissibleMeasure (potentialMeasure φ))
    (r : ℕ) (F : ConstantCompatibleTensorHilbert (hφ.of_le (by simp)) (r+2)) :
    ‖centeredTensorIntegration hφ hκ hlower r
      (constantTensorIntegration hφ hκ hlower (r+1) F)‖^2 ≤ 2*‖F‖^2 := by
  let T : OrderedTensorIndex n (r+2) → ℝ := fun I => ∫ x, F.val I x ∂potentialMeasure φ
  let M (I : OrderedTensorIndex n r) : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => T (Fin.cons i (Fin.cons j I))
  have hsym (I : OrderedTensorIndex n r) : (M I).IsSymm := by
    apply Matrix.ext
    intro i j
    exact congrArg (fun f : Lp ℝ 2 (potentialMeasure φ) => ∫ x, f x ∂potentialMeasure φ)
      (tensor_symmetry_swap (F : OrderedTensorField φ (r+2)) F.property.1.1 I j i)
  have hF : (F : OrderedTensorField φ (r+2))=orderedConstantTensorField (φ := φ) T :=
    constantCompatibleTensor_eq hφ (r+2) F
  have hG (I : OrderedTensorIndex n r) (i : Fin n) :
      ((orderedTensorSlice r I
        (compatibleTensorPrimitive hφ hκ hlower (r+1) F)) i : Space n → ℝ)
        =ᵐ[potentialMeasure φ] fun x => matrixAction (M I) x i := by
    change (compatibleTensorPrimitive hφ hκ hlower (r+1) F (Fin.cons i I) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] _
    rw [hF]
    filter_upwards [compatibleTensorPrimitive_constant_value_ae hφ hκ hlower hμ.isotropic
      T (Fin.cons i I)] with x hx
    rw [hx,matrixAction_apply]
    simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
    apply Finset.sum_congr rfl
    intro j _
    change x j*T (Fin.cons j (Fin.cons i I))=T (Fin.cons i (Fin.cons j I))*x j
    rw [show T (Fin.cons j (Fin.cons i I))=T (Fin.cons i (Fin.cons j I))
      from congrArg (fun f : Lp ℝ 2 (potentialMeasure φ) => ∫ x, f x ∂potentialMeasure φ)
        (tensor_symmetry_swap (F : OrderedTensorField φ (r+2)) F.property.1.1 I j i)]
    exact mul_comm _ _
  change ‖compatibleTensorPrimitive hφ hκ hlower r
    (compatibleTensorPrimitive hφ hκ hlower (r+1) F)‖^2 ≤ 2*‖(F : OrderedTensorField φ (r+2))‖^2
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ I : OrderedTensorIndex n r, 2*matrixFrobeniusSq (M I) := by
      apply Finset.sum_le_sum
      intro I _
      exact weightedGradientPrimitive_quadratic_norm_sq_le_two (hφ.of_le (by simp))
        hκ hlower hμ (M I) (hsym I) _ (hG I)
    _ = 2*∑ I : OrderedTensorIndex n (r+2), (T I)^2 := by
      simp only [matrixFrobeniusSq,←Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      calc
        _ = ∑ i : Fin n, ∑ J : OrderedTensorIndex n (r+1), (T (Fin.cons i J))^2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
          exact (Fintype.sum_prod_type
            (fun p : Fin n × OrderedTensorIndex n r => (T (Fin.cons i (Fin.cons p.1 p.2)))^2)).symm.trans
            (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (r+1) => Fin n))
              (fun p : Fin n × OrderedTensorIndex n r => (T (Fin.cons i (Fin.cons p.1 p.2)))^2)
              (fun J => (T (Fin.cons i J))^2) (fun _ => rfl))
        _ = _ := (Fintype.sum_prod_type
          (fun p : Fin n × OrderedTensorIndex n (r+1) => (T (Fin.cons p.1 p.2))^2)).symm.trans
          (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (r+2) => Fin n)) _ _ (fun _ => rfl))
    _ = _ := by rw [hF,orderedConstantTensorField_norm_sq]

theorem quadratic_tensor_observation_opNorm_le (hμ : admissibleMeasure (potentialMeasure φ))
    (r : ℕ) :
    ‖(centeredTensorIntegration hφ hκ hlower r).comp
      (constantTensorIntegration hφ hκ hlower (r+1))‖ ≤ Real.sqrt 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro F
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [ContinuousLinearMap.comp_apply,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    using quadratic_tensor_observation_norm_sq_le hφ hκ hlower hμ r F

/-- The first observation hypothesis in both numerical endgames is now a
theorem about the actual operators, for every genuine admissible regular law. -/
theorem actual_graded_quadratic_observation_le_two
    (hμ : admissibleMeasure (potentialMeasure φ)) :
    ‖(gradedTensorIntegration hφ hκ hlower).comp
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic)‖^2 ≤ 2 := by
  have hb (r : ℕ) :
      powerObservationBlock (centeredTensorIntegration hφ hκ hlower)
        (constantTensorIntegration hφ hκ hlower) (Real.sqrt_nonneg _)
        (centeredTensorIntegration_opNorm_le hφ hκ hlower) zero_le_one
        (constantTensorIntegration_opNorm_le_one hφ hκ hlower hμ.isotropic) 1 r =
      (centeredTensorIntegration hφ hκ hlower r).comp
        (constantTensorIntegration hφ hκ hlower (r+1)) := by
    apply ContinuousLinearMap.ext
    intro F
    change ((gradedTensorIntegration hφ hκ hlower)^1)
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic (lp.single 2 (r+1) F)) r = _
    rw [pow_one,gradedTensorIntegration_apply,gradedConstantIntegration_apply,lp.single_apply_self]
    rfl
  have hn := norm_power_observation_le_of_blocks
    (centeredTensorIntegration hφ hκ hlower) (constantTensorIntegration hφ hκ hlower)
    (Real.sqrt_nonneg _) (centeredTensorIntegration_opNorm_le hφ hκ hlower)
    zero_le_one (constantTensorIntegration_opNorm_le_one hφ hκ hlower hμ.isotropic)
    1 (Real.sqrt_nonneg 2) (fun r => by
      rw [hb r]
      exact quadratic_tensor_observation_opNorm_le hφ hκ hlower hμ r)
  change ‖((gradedTensorIntegration hφ hκ hlower)^1).comp
    (gradedConstantIntegration hφ hκ hlower hμ.isotropic)‖ ≤ Real.sqrt 2 at hn
  rw [pow_one] at hn
  have hs := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg 2)).mpr hn
  rwa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hs

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.quadratic_tensor_observation_norm_sq_le
#print axioms KLS.DeterministicBridgeIntegration.actual_graded_quadratic_observation_le_two
