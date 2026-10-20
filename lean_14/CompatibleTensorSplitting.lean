import CompatibleTensorPrimitive
import KLS.LocalLipschitzWeakDerivative

/-! Genuine orthogonal splitting Cᵣ = Eᵣ ⊕ Gᵣ. The constant part is the
actual coordinatewise mean in L²(μ), not an abstract chosen summand. The
centered inverse on isotropic constant tensors is actual contraction with x. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ} {φ : Space n → ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]

def orderedConstantTensorField (T : OrderedTensorIndex n r → ℝ) : OrderedTensorField φ r :=
  WithLp.toLp 2 (fun I => T I • CenteredL2.oneLp (potentialMeasure φ))

@[simp] lemma orderedConstantTensorField_apply (T : OrderedTensorIndex n r → ℝ)
    (I : OrderedTensorIndex n r) :
    orderedConstantTensorField (φ := φ) T I = T I • CenteredL2.oneLp (potentialMeasure φ) := rfl

lemma orderedConstantTensorField_ae (T : OrderedTensorIndex n r → ℝ)
    (I : OrderedTensorIndex n r) :
    (orderedConstantTensorField (φ := φ) T I : Space n → ℝ) =ᵐ[potentialMeasure φ]
      fun _ => T I := by
  filter_upwards [Lp.coeFn_smul (T I) (CenteredL2.oneLp (potentialMeasure φ)),
    CenteredL2.oneLp_ae (potentialMeasure φ)] with x hx hy
  change (T I • CenteredL2.oneLp (potentialMeasure φ)) x = _
  rw [hx, Pi.smul_apply, smul_eq_mul, hy, mul_one]

lemma integral_coordinateDerivative_compact_eq_zero {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    (∫ x, coordinateDerivative ψ i x) = 0 := by
  have he := hasLocalWeakCoordinateDerivative_of_locallyLipschitz
    (contDiff_const : ContDiff ℝ 1 (fun _ : Space n => (1 : ℝ))).locallyLipschitz i
  have ht := he ψ hψ hc
  simpa [coordinateDerivative] using ht

lemma orderedConstantTensorField_mem_curl (hφ : ContDiff ℝ 1 φ)
    (T : OrderedTensorIndex n r → ℝ) :
    orderedConstantTensorField (φ := φ) T ∈ orderedTensorCurlSubspace hφ r := by
  cases r with
  | zero => trivial
  | succ r =>
    rw [mem_orderedTensorCurlSubspace_succ_iff]
    intro I
    rw [mem_weightedCurlFreeSubspace_iff]
    intro ψ hψ hc i j
    have hae (k : Fin n) :
        (orderedTensorSlice r I (orderedConstantTensorField (φ := φ) T) k : Space n → ℝ)
          =ᵐ[volume] fun _ => T (Fin.cons k I) :=
      (volume_absolutelyContinuous_potentialMeasure hφ.continuous).ae_eq
        (orderedConstantTensorField_ae T (Fin.cons k I))
    rw [integral_congr_ae ((hae i).fun_mul EventuallyEq.rfl),
      integral_congr_ae ((hae j).fun_mul EventuallyEq.rfl), integral_const_mul,
      integral_const_mul, integral_coordinateDerivative_compact_eq_zero (hψ.of_le (by simp)) hc,
      integral_coordinateDerivative_compact_eq_zero (hψ.of_le (by simp)) hc]
    simp

def orderedTensorMeanPart (φ : Space n → ℝ) (r : ℕ)
    [IsProbabilityMeasure (potentialMeasure φ)] :
    OrderedTensorField φ r →L[ℝ] OrderedTensorField φ r :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : OrderedTensorIndex n r => Lp ℝ 2 (potentialMeasure φ))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun I =>
        ((ContinuousLinearMap.smulRight (innerSL ℝ (CenteredL2.oneLp (potentialMeasure φ)))
          (CenteredL2.oneLp (potentialMeasure φ))).comp
            (PiLp.proj 2 (fun _ : OrderedTensorIndex n r => Lp ℝ 2 (potentialMeasure φ)) I)))

lemma orderedTensorMeanPart_apply (F : OrderedTensorField φ r) (I : OrderedTensorIndex n r) :
    orderedTensorMeanPart φ r F I = (∫ x, F I x ∂potentialMeasure φ) •
      CenteredL2.oneLp (potentialMeasure φ) := by
  change (inner ℝ (CenteredL2.oneLp (potentialMeasure φ)) (F I)) •
    CenteredL2.oneLp (potentialMeasure φ) =
      (∫ x, F I x ∂potentialMeasure φ) • CenteredL2.oneLp (potentialMeasure φ)
  rw [CenteredL2.inner_oneLp]

lemma orderedTensorMeanPart_eq_constant (F : OrderedTensorField φ r) :
    orderedTensorMeanPart φ r F =
      orderedConstantTensorField (φ := φ) (fun I => ∫ x, F I x ∂potentialMeasure φ) := by
  apply PiLp.ext
  intro I
  exact orderedTensorMeanPart_apply F I

def orderedTensorCenter (φ : Space n → ℝ) (r : ℕ)
    [IsProbabilityMeasure (potentialMeasure φ)] :
    OrderedTensorField φ r →L[ℝ] OrderedTensorField φ r :=
  ContinuousLinearMap.id ℝ _ - orderedTensorMeanPart φ r

lemma orderedTensorCenter_apply (F : OrderedTensorField φ r) (I : OrderedTensorIndex n r) :
    orderedTensorCenter φ r F I = CenteredL2.center (potentialMeasure φ) (F I) := by
  change F I - orderedTensorMeanPart φ r F I = _
  rw [orderedTensorMeanPart_apply]
  rfl

lemma orderedTensorMeanPart_integral (F : OrderedTensorField φ r) (I : OrderedTensorIndex n r) :
    (∫ x, orderedTensorMeanPart φ r F I x ∂potentialMeasure φ) =
      ∫ x, F I x ∂potentialMeasure φ := by
  rw [orderedTensorMeanPart_eq_constant,
    integral_congr_ae (orderedConstantTensorField_ae _ I)]
  simp

lemma orderedTensorMeanPart_idempotent (F : OrderedTensorField φ r) :
    orderedTensorMeanPart φ r (orderedTensorMeanPart φ r F) = orderedTensorMeanPart φ r F := by
  apply PiLp.ext
  intro I
  rw [orderedTensorMeanPart_apply, orderedTensorMeanPart_integral, orderedTensorMeanPart_apply]

lemma orderedTensorCenter_integral_eq_zero (F : OrderedTensorField φ r)
    (I : OrderedTensorIndex n r) :
    (∫ x, orderedTensorCenter φ r F I x ∂potentialMeasure φ) = 0 := by
  rw [orderedTensorCenter_apply]
  exact CenteredL2.integral_center _ _

lemma orderedTensorMeanPart_center (F : OrderedTensorField φ r) :
    orderedTensorMeanPart φ r (orderedTensorCenter φ r F) = 0 := by
  apply PiLp.ext
  intro I
  simp only [orderedTensorMeanPart_apply, orderedTensorCenter_integral_eq_zero, zero_smul]
  rfl

lemma orderedTensorMeanPart_mem (hφ : ContDiff ℝ 1 φ) (F : OrderedTensorField φ r)
    (hF : F ∈ compatibleSymmetricTensorSubspace hφ r) :
    orderedTensorMeanPart φ r F ∈ compatibleSymmetricTensorSubspace hφ r := by
  constructor
  · change orderedTensorMeanPart φ r F ∈ orderedTensorSymmetricSubspace φ r
    rw [mem_orderedTensorSymmetricSubspace_iff]
    intro I J hIJ
    simp only [orderedTensorMeanPart_apply,
      (mem_orderedTensorSymmetricSubspace_iff F).mp hF.1 I J hIJ]
  · rw [orderedTensorMeanPart_eq_constant]
    exact orderedConstantTensorField_mem_curl hφ _

lemma orderedTensorCenter_mem (hφ : ContDiff ℝ 1 φ) (F : OrderedTensorField φ r)
    (hF : F ∈ compatibleSymmetricTensorSubspace hφ r) :
    orderedTensorCenter φ r F ∈ compatibleSymmetricTensorSubspace hφ r :=
  (compatibleSymmetricTensorSubspace hφ r).sub_mem hF (orderedTensorMeanPart_mem hφ F hF)

def constantCompatibleTensorSubspace (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    Submodule ℝ (OrderedTensorField φ r) :=
  compatibleSymmetricTensorSubspace hφ r ⊓
    LinearMap.ker (orderedTensorMeanPart φ r - ContinuousLinearMap.id ℝ _).toLinearMap

def centeredCompatibleTensorSubspace (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    Submodule ℝ (OrderedTensorField φ r) :=
  compatibleSymmetricTensorSubspace hφ r ⊓ LinearMap.ker (orderedTensorMeanPart φ r).toLinearMap

lemma centeredCompatibleTensorSubspace_isClosed (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    IsClosed (centeredCompatibleTensorSubspace hφ r : Set (OrderedTensorField φ r)) :=
  (compatibleSymmetricTensorSubspace_isClosed hφ r).inter (orderedTensorMeanPart φ r).isClosed_ker

lemma mem_centeredCompatibleTensorSubspace_iff (hφ : ContDiff ℝ 1 φ)
    (F : OrderedTensorField φ r) :
    F ∈ centeredCompatibleTensorSubspace hφ r ↔
      F ∈ compatibleSymmetricTensorSubspace hφ r ∧
        ∀ I, (∫ x, F I x ∂potentialMeasure φ) = 0 := by
  constructor
  · intro hF
    refine ⟨hF.1, fun I => ?_⟩
    have he : orderedTensorMeanPart φ r F = 0 := hF.2
    have hi := orderedTensorMeanPart_integral F I
    rw [he] at hi
    have hz : (∫ x, (0 : OrderedTensorField φ r) I x ∂potentialMeasure φ) = 0 := by
      change (∫ x, (0 : Lp ℝ 2 (potentialMeasure φ)) x ∂potentialMeasure φ) = 0
      rw [integral_congr_ae (Lp.coeFn_zero ℝ 2 (potentialMeasure φ))]
      simp only [Pi.zero_apply, integral_zero]
    exact hi.symm.trans hz
  · rintro ⟨hF, hm⟩
    refine ⟨hF, ?_⟩
    change orderedTensorMeanPart φ r F = 0
    apply PiLp.ext
    intro I
    simp only [orderedTensorMeanPart_apply, hm, zero_smul]
    rfl

lemma compatibleTensorPrimitive_mem_centered {κ : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (F : OrderedTensorField φ (r + 1))
    (hF : F ∈ compatibleSymmetricTensorSubspace (hφ.of_le (by simp)) (r + 1)) :
    compatibleTensorPrimitive hφ hκ hlower r F ∈
      centeredCompatibleTensorSubspace (hφ.of_le (by simp)) r := by
  rw [mem_centeredCompatibleTensorSubspace_iff]
  exact ⟨compatibleTensorPrimitive_mem hφ hκ hlower F hF,
    compatibleTensorPrimitive_integral_eq_zero hφ hκ hlower F⟩

theorem compatibleTensor_orthogonal_decomposition (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    compatibleSymmetricTensorSubspace hφ r =
      constantCompatibleTensorSubspace hφ r ⊔ centeredCompatibleTensorSubspace hφ r := by
  apply le_antisymm
  · intro F hF
    have he : orderedTensorMeanPart φ r F ∈ constantCompatibleTensorSubspace hφ r :=
      ⟨orderedTensorMeanPart_mem hφ F hF,
        sub_eq_zero.mpr (orderedTensorMeanPart_idempotent F)⟩
    have hg : orderedTensorCenter φ r F ∈ centeredCompatibleTensorSubspace hφ r :=
      ⟨orderedTensorCenter_mem hφ F hF, orderedTensorMeanPart_center F⟩
    have hh := Submodule.add_mem_sup he hg
    have hs : orderedTensorMeanPart φ r F + orderedTensorCenter φ r F = F := by
      change orderedTensorMeanPart φ r F + (F - orderedTensorMeanPart φ r F) = F
      abel
    rwa [hs] at hh
  · exact sup_le inf_le_left inf_le_left

theorem compatibleTensor_summands_disjoint (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    Disjoint (constantCompatibleTensorSubspace hφ r) (centeredCompatibleTensorSubspace hφ r) := by
  rw [disjoint_iff_inf_le]
  rintro F ⟨hE, hG⟩
  change F = 0
  have he : orderedTensorMeanPart φ r F - F = 0 := hE.2
  have hg : orderedTensorMeanPart φ r F = 0 := hG.2
  rw [hg] at he
  exact neg_eq_zero.mp (by simpa only [zero_sub] using he)

theorem orderedTensorMeanPart_inner_center (F : OrderedTensorField φ r) :
    inner ℝ (orderedTensorMeanPart φ r F) (orderedTensorCenter φ r F) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro I _
  rw [orderedTensorMeanPart_apply, orderedTensorCenter_apply, inner_smul_left,
    CenteredL2.inner_oneLp, CenteredL2.integral_center, mul_zero]

theorem orderedTensor_split_norm_sq (F : OrderedTensorField φ r) :
    ‖F‖ ^ 2 = ‖orderedTensorMeanPart φ r F‖ ^ 2 + ‖orderedTensorCenter φ r F‖ ^ 2 := by
  have hs : F = orderedTensorMeanPart φ r F + orderedTensorCenter φ r F := by
    change F = orderedTensorMeanPart φ r F + (F - orderedTensorMeanPart φ r F)
    abel
  have he := norm_add_sq_real (orderedTensorMeanPart φ r F) (orderedTensorCenter φ r F)
  rw [orderedTensorMeanPart_inner_center, mul_zero, add_zero] at he
  conv_lhs => rw [hs]
  exact he

theorem compatibleTensorPrimitive_constant_value_ae {κ : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hiso : IsIsotropic (potentialMeasure φ)) (T : OrderedTensorIndex n (r + 1) → ℝ)
    (I : OrderedTensorIndex n r) :
    (compatibleTensorPrimitive hφ hκ hlower r (orderedConstantTensorField (φ := φ) T) I :
      Space n → ℝ) =ᵐ[potentialMeasure φ]
        fun x => inner ℝ (WithLp.toLp 2 (fun j => T (Fin.cons j I)) : Space n) x :=
  weightedGradientPrimitive_constant_value_ae (hφ.of_le (by simp)) hκ hlower hiso
    (WithLp.toLp 2 (fun j => T (Fin.cons j I)))

theorem compatibleTensorPrimitive_constant_norm_sq {κ : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hiso : IsIsotropic (potentialMeasure φ)) (T : OrderedTensorIndex n (r + 1) → ℝ) :
    ‖compatibleTensorPrimitive hφ hκ hlower r (orderedConstantTensorField (φ := φ) T)‖ ^ 2 =
      ∑ J, (T J) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ = ∑ I : OrderedTensorIndex n r, ‖(WithLp.toLp 2 (fun j => T (Fin.cons j I)) : Space n)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro I _
      exact weightedGradientPrimitive_constant_norm_sq (hφ.of_le (by simp)) hκ hlower hiso
        (WithLp.toLp 2 (fun j => T (Fin.cons j I)))
    _ = ∑ I : OrderedTensorIndex n r, ∑ j : Fin n, (T (Fin.cons j I)) ^ 2 := by
      simp only [EuclideanSpace.real_norm_sq_eq]
    _ = _ := by
      rw [Finset.sum_comm]
      calc
        _ = ∑ p : Fin n × OrderedTensorIndex n r, (T (Fin.cons p.1 p.2)) ^ 2 :=
          (Fintype.sum_prod_type (fun p : Fin n × OrderedTensorIndex n r =>
            (T (Fin.cons p.1 p.2)) ^ 2)).symm
        _ = _ := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (r + 1) => Fin n))
          _ _ (fun _ => rfl)

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.compatibleTensorPrimitive_mem_centered
#print axioms KLS.DeterministicBridgeIntegration.compatibleTensor_orthogonal_decomposition
#print axioms KLS.DeterministicBridgeIntegration.compatibleTensor_summands_disjoint
#print axioms KLS.DeterministicBridgeIntegration.orderedTensor_split_norm_sq
#print axioms KLS.DeterministicBridgeIntegration.compatibleTensorPrimitive_constant_value_ae
#print axioms KLS.DeterministicBridgeIntegration.compatibleTensorPrimitive_constant_norm_sq
