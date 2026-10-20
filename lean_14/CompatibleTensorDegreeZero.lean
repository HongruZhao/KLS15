import ActualGradedTensorOperators

/-! The actual scalar Dirichlet graph is the rank-zero tensor primitive.
This identifies its faithful Poincare constant with the graded norm bound,
without any universal numeric bound being assumed. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace
open scoped ContDiff ENNReal BigOperators
namespace KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

theorem compatibleTensorPrimitive_norm_sq_le_split
    (hiso : IsIsotropic (potentialMeasure φ)) {r : ℕ}
    (F : OrderedTensorField φ (r+1))
    (hF : F ∈ compatibleSymmetricTensorSubspace (hφ.of_le (by simp)) (r+1)) :
    ‖compatibleTensorPrimitive hφ hκ hlower r F‖^2 ≤
      (1+‖gradedTensorIntegration hφ hκ hlower‖^2)*‖F‖^2 := by
  let E : ConstantCompatibleTensorHilbert (hφ.of_le (by simp)) (r+1) :=
    ⟨orderedTensorMeanPart φ (r+1) F,
      orderedTensorMeanPart_mem (hφ.of_le (by simp)) F hF,
      sub_eq_zero.mpr (orderedTensorMeanPart_idempotent F)⟩
  let G : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) (r+1) :=
    ⟨orderedTensorCenter φ (r+1) F,
      orderedTensorCenter_mem (hφ.of_le (by simp)) F hF,orderedTensorMeanPart_center F⟩
  let A := ‖gradedTensorIntegration hφ hκ hlower‖
  have hsplit : compatibleTensorPrimitive hφ hκ hlower r F=
      (centeredTensorIntegration hφ hκ hlower r G : OrderedTensorField φ r)+
      (constantTensorIntegration hφ hκ hlower r E : OrderedTensorField φ r) := by
    change compatibleTensorPrimitive hφ hκ hlower r F=
      compatibleTensorPrimitive hφ hκ hlower r (F-orderedTensorMeanPart φ (r+1) F)+
      compatibleTensorPrimitive hφ hκ hlower r (orderedTensorMeanPart φ (r+1) F)
    rw [map_sub]
    abel
  have hG : ‖centeredTensorIntegration hφ hκ hlower r G‖ ≤ A*‖G‖ :=
    (centeredTensorIntegration hφ hκ hlower r).le_of_opNorm_le
      (centeredTensorIntegration_norm_le_graded hφ hκ hlower r) G
  have hE := constantTensorIntegration_norm hφ hκ hlower hiso r E
  have hn : ‖compatibleTensorPrimitive hφ hκ hlower r F‖ ≤ A*‖G‖+‖E‖ := by
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hG hE.le)
  have hs : ‖F‖^2=‖E‖^2+‖G‖^2 := orderedTensor_split_norm_sq F
  have hcs : (A*‖G‖+‖E‖)^2 ≤ (1+A^2)*(‖E‖^2+‖G‖^2) := by
    nlinarith [sq_nonneg (A*‖E‖-‖G‖)]
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (hs ▸ hcs)

def rankOneGraphGradient (U : WeightedCenteredH1 φ) : OrderedTensorField φ 1 :=
  WithLp.toLp 2 (fun I => weightedH1Gradient φ U (I 0))

theorem rankOneGraphGradient_slice (U : WeightedCenteredH1 φ) (I : OrderedTensorIndex n 0) :
    orderedTensorSlice 0 I (rankOneGraphGradient U)=weightedH1Gradient φ U := by
  apply PiLp.ext
  intro i
  rfl

theorem rankOneGraphGradient_mem (U : WeightedCenteredH1 φ) :
    rankOneGraphGradient U ∈ compatibleSymmetricTensorSubspace (hφ.of_le (by simp)) 1 := by
  constructor
  · change rankOneGraphGradient U ∈ orderedTensorSymmetricSubspace φ 1
    rw [mem_orderedTensorSymmetricSubspace_iff]
    intro I J hIJ
    have he : I 0=J 0 := by
      simpa only [List.ofFn_succ,List.ofFn_zero,List.perm_singleton,List.singleton_inj] using hIJ
    change weightedH1Gradient φ U (I 0)=weightedH1Gradient φ U (J 0)
    rw [he]
  · change rankOneGraphGradient U ∈ orderedTensorCurlSubspace (hφ.of_le (by simp)) (0+1)
    rw [mem_orderedTensorCurlSubspace_succ_iff]
    intro I
    rw [rankOneGraphGradient_slice,mem_weightedCurlFreeSubspace_iff]
    intro ψ hψ hc i j
    exact weightedH1Gradient_distributionally_curlFree (hφ.of_le (by simp)) U i j hψ hc

theorem rankOneGraphGradient_norm_sq (U : WeightedCenteredH1 φ) :
    ‖rankOneGraphGradient U‖^2=‖weightedH1Gradient φ U‖^2 := by
  have he := orderedTensorSlices_norm_sq (rankOneGraphGradient U)
  rw [PiLp.norm_sq_eq_of_L2] at he
  simp only [orderedTensorSlices_apply,rankOneGraphGradient_slice,Finset.sum_const,
    Finset.card_univ,Fintype.card_unique,one_nsmul] at he
  exact he.symm

theorem rankZeroGraphPrimitive_norm_sq (U : WeightedCenteredH1 φ) :
    ‖compatibleTensorPrimitive hφ hκ hlower 0 (rankOneGraphGradient U)‖^2=
      ‖weightedH1Value φ U‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  have he (I : OrderedTensorIndex n 0) :
      compatibleTensorPrimitive hφ hκ hlower 0 (rankOneGraphGradient U) I=weightedH1Value φ U := by
    rw [compatibleTensorPrimitive_apply,compatibleTensorPrimitiveGraph_apply,
      rankOneGraphGradient_slice,weightedGradientPrimitive_gradient]
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_unique,one_nsmul]

theorem poincareConstant_le_one_add_graded_norm_sq (hn : 0 < n)
    (hiso : IsIsotropic (potentialMeasure φ)) :
    poincareConstant (potentialMeasure φ) ≤
      ENNReal.ofReal (1+‖gradedTensorIntegration hφ hκ hlower‖^2) := by
  obtain ⟨lam,U,_,hlam,hU,hweak,_,hCP⟩ :=
    exists_positive_weighted_eigenpair_with_optimal_poincare hn (hφ.of_le (by simp)) hκ hlower
  have he : weightedEnergyForm φ U U=lam := by
    simpa only [real_inner_self_eq_norm_sq,hU,one_pow,mul_one] using hweak U
  have hb := compatibleTensorPrimitive_norm_sq_le_split hφ hκ hlower hiso
    (rankOneGraphGradient U) (rankOneGraphGradient_mem hφ U)
  rw [rankZeroGraphPrimitive_norm_sq,rankOneGraphGradient_norm_sq,
    weightedH1Gradient_norm_sq,hU,one_pow] at hb
  rw [← weightedEnergyForm_self,he] at hb
  have hr : lam⁻¹ ≤ 1+‖gradedTensorIntegration hφ hκ hlower‖^2 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hlam).mpr (by nlinarith [hb])
  rw [hCP]
  exact ENNReal.ofReal_le_ofReal hr

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.compatibleTensorPrimitive_norm_sq_le_split
#print axioms KLS.DeterministicBridgeIntegration.rankOneGraphGradient_mem
#print axioms KLS.DeterministicBridgeIntegration.poincareConstant_le_one_add_graded_norm_sq
