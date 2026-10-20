import CompatibleTensorSplitting

/-! Faithful real Hilbert interfaces for the paper's inverse maps.
All carriers are actual closed distributional tensor spaces. The operators
are restrictions of the proved centered Dirichlet primitive, with no
abstract operator realization or numerical spectral assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open MeasureTheory InnerProductSpace Set Matrix
open scoped ContDiff BigOperators RealInnerProductSpace ENNReal
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {φ : Space n → ℝ}

abbrev CompatibleTensorHilbert (hφ : ContDiff ℝ 1 φ) (r : ℕ) :=
  ↥(compatibleSymmetricTensorSubspace hφ r)

instance compatibleTensorHilbert_complete (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    CompleteSpace (CompatibleTensorHilbert hφ r) :=
  (compatibleSymmetricTensorSubspace_isClosed hφ r).isComplete.completeSpace_coe

variable [IsProbabilityMeasure (potentialMeasure φ)]

abbrev CenteredCompatibleTensorHilbert (hφ : ContDiff ℝ 1 φ) (r : ℕ) :=
  ↥(centeredCompatibleTensorSubspace hφ r)

abbrev ConstantCompatibleTensorHilbert (hφ : ContDiff ℝ 1 φ) (r : ℕ) :=
  ↥(constantCompatibleTensorSubspace hφ r)

instance centeredCompatibleTensorHilbert_complete (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    CompleteSpace (CenteredCompatibleTensorHilbert hφ r) :=
  (centeredCompatibleTensorSubspace_isClosed hφ r).isComplete.completeSpace_coe

lemma constantCompatibleTensorSubspace_isClosed (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    IsClosed (constantCompatibleTensorSubspace hφ r : Set (OrderedTensorField φ r)) :=
  (compatibleSymmetricTensorSubspace_isClosed hφ r).inter
    (orderedTensorMeanPart φ r - ContinuousLinearMap.id ℝ _).isClosed_ker

instance constantCompatibleTensorHilbert_complete (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    CompleteSpace (ConstantCompatibleTensorHilbert hφ r) :=
  (constantCompatibleTensorSubspace_isClosed hφ r).isComplete.completeSpace_coe

def centeredCompatibleTensorInclusion (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    CenteredCompatibleTensorHilbert hφ r →L[ℝ] CompatibleTensorHilbert hφ r :=
  ((centeredCompatibleTensorSubspace hφ r).subtypeL).codRestrict
    (compatibleSymmetricTensorSubspace hφ r) (fun F => F.property.1)

def constantCompatibleTensorInclusion (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    ConstantCompatibleTensorHilbert hφ r →L[ℝ] CompatibleTensorHilbert hφ r :=
  ((constantCompatibleTensorSubspace hφ r).subtypeL).codRestrict
    (compatibleSymmetricTensorSubspace hφ r) (fun F => F.property.1)

variable {κ : ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

/-- The paper's actual inverse gradient J̃ᵣ : Cᵣ₊₁ → Gᵣ. -/
def compatibleTensorInverse (r : ℕ) :
    CompatibleTensorHilbert (hφ.of_le (by simp)) (r + 1) →L[ℝ]
      CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r :=
  ((compatibleTensorPrimitive hφ hκ hlower r).domRestrict
    (compatibleSymmetricTensorSubspace (hφ.of_le (by simp)) (r + 1))).codRestrict
      (centeredCompatibleTensorSubspace (hφ.of_le (by simp)) r)
        (fun (F : CompatibleTensorHilbert (hφ.of_le (by simp)) (r + 1)) =>
          compatibleTensorPrimitive_mem_centered hφ hκ hlower
            (F : OrderedTensorField φ (r + 1)) F.property)

/-- The paper's centered-input integration Jᵣ : Gᵣ₊₁ → Gᵣ. -/
def centeredTensorIntegration (r : ℕ) :
    CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) (r + 1) →L[ℝ]
      CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r :=
  (compatibleTensorInverse hφ hκ hlower r).comp
    (centeredCompatibleTensorInclusion (hφ.of_le (by simp)) (r + 1))

/-- The paper's constant-input integration Lᵣ : Eᵣ₊₁ → Gᵣ. -/
def constantTensorIntegration (r : ℕ) :
    ConstantCompatibleTensorHilbert (hφ.of_le (by simp)) (r + 1) →L[ℝ]
      CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r :=
  (compatibleTensorInverse hφ hκ hlower r).comp
    (constantCompatibleTensorInclusion (hφ.of_le (by simp)) (r + 1))

@[simp] lemma compatibleTensorInverse_coe (r : ℕ)
    (F : CompatibleTensorHilbert (hφ.of_le (by simp)) (r + 1)) :
    (compatibleTensorInverse hφ hκ hlower r F : OrderedTensorField φ r) =
      compatibleTensorPrimitive hφ hκ hlower r F := rfl

@[simp] lemma centeredTensorIntegration_coe (r : ℕ)
    (F : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) (r + 1)) :
    (centeredTensorIntegration hφ hκ hlower r F : OrderedTensorField φ r) =
      compatibleTensorPrimitive hφ hκ hlower r F := rfl

@[simp] lemma constantTensorIntegration_coe (r : ℕ)
    (F : ConstantCompatibleTensorHilbert (hφ.of_le (by simp)) (r + 1)) :
    (constantTensorIntegration hφ hκ hlower r F : OrderedTensorField φ r) =
      compatibleTensorPrimitive hφ hκ hlower r F := rfl

theorem compatibleTensorInverse_opNorm_le (r : ℕ) :
    ‖compatibleTensorInverse hφ hκ hlower r‖ ≤ Real.sqrt κ⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro F
  change ‖compatibleTensorPrimitive hφ hκ hlower r (F : OrderedTensorField φ (r + 1))‖ ≤
    Real.sqrt κ⁻¹ * ‖(F : OrderedTensorField φ (r + 1))‖
  exact compatibleTensorPrimitive_norm_le hφ hκ hlower (r := r)
    (F : OrderedTensorField φ (r + 1))

theorem exists_optimal_centeredTensorIntegration_bound (hn : 0 < n) :
    ∃ lam : ℝ, 0 < lam ∧
      poincareConstant (potentialMeasure φ) = ENNReal.ofReal lam⁻¹ ∧
      ∀ r, ‖compatibleTensorInverse hφ hκ hlower r‖ ≤ Real.sqrt lam⁻¹ ∧
        ‖centeredTensorIntegration hφ hκ hlower r‖ ≤ Real.sqrt lam⁻¹ := by
  obtain ⟨lam, hlam, hCP, hb⟩ := exists_optimal_compatibleTensorPrimitive_bound hφ hκ hlower hn
  refine ⟨lam, hlam, hCP, fun r => ⟨?_, ?_⟩⟩
  · exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun F => hb r F)
  · exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun F => hb r F)

lemma oneLp_norm_sq : ‖CenteredL2.oneLp (potentialMeasure φ)‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, CenteredL2.inner_oneLp, CenteredL2.integral_oneLp]

theorem orderedConstantTensorField_norm_sq {r : ℕ} (T : OrderedTensorIndex n r → ℝ) :
    ‖orderedConstantTensorField (φ := φ) T‖ ^ 2 = ∑ I, (T I) ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, orderedConstantTensorField_apply, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, oneLp_norm_sq, mul_one]

theorem constantTensorIntegration_norm (hiso : IsIsotropic (potentialMeasure φ)) (r : ℕ)
    (F : ConstantCompatibleTensorHilbert (hφ.of_le (by simp)) (r + 1)) :
    ‖constantTensorIntegration hφ hκ hlower r F‖ = ‖F‖ := by
  have hfixed : orderedTensorMeanPart φ (r + 1) F - (F : OrderedTensorField φ (r + 1)) = 0 :=
    F.property.2
  have hconst : (F : OrderedTensorField φ (r + 1)) =
      orderedConstantTensorField (φ := φ) (fun I => ∫ x, F.val I x ∂potentialMeasure φ) := by
    rw [← orderedTensorMeanPart_eq_constant]
    exact (sub_eq_zero.mp hfixed).symm
  have hn : ‖constantTensorIntegration hφ hκ hlower r F‖ ^ 2 = ‖F‖ ^ 2 := by
    change ‖compatibleTensorPrimitive hφ hκ hlower r (F : OrderedTensorField φ (r + 1))‖ ^ 2 =
      ‖(F : OrderedTensorField φ (r + 1))‖ ^ 2
    rw [hconst, compatibleTensorPrimitive_constant_norm_sq hφ hκ hlower hiso,
      orderedConstantTensorField_norm_sq]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hn

theorem constantTensorIntegration_opNorm_le_one (hiso : IsIsotropic (potentialMeasure φ)) (r : ℕ) :
    ‖constantTensorIntegration hφ hκ hlower r‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun F =>
    by simpa only [one_mul] using (constantTensorIntegration_norm hφ hκ hlower hiso r F).le)

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.compatibleTensorInverse
#print axioms KLS.DeterministicBridgeIntegration.exists_optimal_centeredTensorIntegration_bound
#print axioms KLS.DeterministicBridgeIntegration.constantTensorIntegration_norm
#print axioms KLS.DeterministicBridgeIntegration.constantTensorIntegration_opNorm_le_one
