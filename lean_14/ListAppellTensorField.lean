import AppellPrimitiveIdentity
import KLS.TiltCumulantLowOrders

/-! Factorially normalized genuine Appell tensor fields. List-indexed
constant coefficients let rank changes preserve the same symmetric tensor
without casts. The actual inverse-gradient step is proved on these fields. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

def ListTensorSymmetric (t : List (Fin n) → ℝ) : Prop :=
  ∀ a b, List.Perm a b → t a=t b

def listAppellSlice (t : List (Fin n) → ℝ) {r d : ℕ}
    (I : Fin r → Fin n) (a : Fin d → Fin n) : ℝ :=
  t (List.ofFn a ++ List.ofFn I)

theorem listAppellSlice_symmetric {t : List (Fin n) → ℝ}
    (ht : ListTensorSymmetric t) {r d : ℕ} (I : Fin r → Fin n)
    (a b : Fin d → Fin n) (h : List.Perm (List.ofFn a) (List.ofFn b)) :
    listAppellSlice t I a=listAppellSlice t I b :=
  ht _ _ (h.append_right _)

theorem listAppellSlice_cons {t : List (Fin n) → ℝ}
    (ht : ListTensorSymmetric t) {r d : ℕ} (I : Fin r → Fin n)
    (a : Fin d → Fin n) (j : Fin n) :
    listAppellSlice t I (Fin.cons j a)=listAppellSlice t (Fin.cons j I) a := by
  apply ht
  simp only [List.ofFn_cons,List.cons_append]
  exact List.perm_middle.symm

def listAppellTensorField (hμ : admissibleMeasure (potentialMeasure φ))
    (r d : ℕ) (t : List (Fin n) → ℝ) : OrderedTensorField φ r :=
  WithLp.toLp 2 (fun I => (d.factorial : ℝ)⁻¹ •
    polynomialLp hμ.logConcave (contractedAppellPolynomial hμ d (listAppellSlice t I)))

@[simp] theorem listAppellTensorField_apply (hμ : admissibleMeasure (potentialMeasure φ))
    (r d : ℕ) (t : List (Fin n) → ℝ) (I : Fin r → Fin n) :
    listAppellTensorField hμ r d t I = (d.factorial : ℝ)⁻¹ •
      polynomialLp hμ.logConcave (contractedAppellPolynomial hμ d (listAppellSlice t I)) := rfl

theorem listAppellTensorField_coe (hμ : admissibleMeasure (potentialMeasure φ))
    (r d : ℕ) (t : List (Fin n) → ℝ) (I : Fin r → Fin n) :
    (listAppellTensorField hμ r d t I : Space n → ℝ) =ᵐ[potentialMeasure φ]
      fun x => (d.factorial : ℝ)⁻¹ *
        polynomialEval (contractedAppellPolynomial hμ d (listAppellSlice t I)) x := by
  exact (Lp.coeFn_smul _ _).trans ((polynomialLp_coe hμ.logConcave _).const_smul _)

theorem listAppellTensorField_mean_zero (hμ : admissibleMeasure (potentialMeasure φ))
    (r : ℕ) {d : ℕ} (hd : d ≠ 0) (t : List (Fin n) → ℝ) (I : Fin r → Fin n) :
    (∫ x, listAppellTensorField hμ r d t I x ∂potentialMeasure φ)=0 := by
  rw [integral_congr_ae (listAppellTensorField_coe hμ r d t I),integral_const_mul,
    contractedAppellPolynomial_integral_zero hμ hd,mul_zero]

theorem compatibleTensorPrimitive_listAppellTensorField {κ : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hμ : admissibleMeasure (potentialMeasure φ)) (r d : ℕ)
    (t : List (Fin n) → ℝ) (ht : ListTensorSymmetric t) :
    compatibleTensorPrimitive hφ hκ hlower r (listAppellTensorField hμ (r+1) d t)=
      listAppellTensorField hμ r (d+1) t := by
  apply PiLp.ext
  intro I
  let s : (Fin (d+1) → Fin n) → ℝ := listAppellSlice t I
  have hs := listAppellSlice_symmetric ht I (d := d+1)
  obtain ⟨U,hv,hD⟩ := exists_weightedH1_normalizedContractedAppell
    (hφ.of_le (by simp)) hκ hlower hμ d s hs
  let V : WeightedCenteredH1 φ := (d.factorial : ℝ)⁻¹ • U
  have hgrad : weightedH1Gradient φ V=
      orderedTensorSlice r I (listAppellTensorField hμ (r+1) d t) := by
    apply PiLp.ext
    intro j
    apply Lp.ext
    have he : (fun b : Fin d → Fin n => s (Fin.cons j b))=
        listAppellSlice t (Fin.cons j I) := by
      funext b
      exact listAppellSlice_cons ht I b j
    have hleft : (weightedH1Derivative φ j V : Space n → ℝ) =ᵐ[potentialMeasure φ]
        fun x => (d.factorial : ℝ)⁻¹ *
          polynomialEval (contractedAppellPolynomial hμ d (listAppellSlice t (Fin.cons j I))) x := by
      change (weightedH1Derivative φ j ((d.factorial : ℝ)⁻¹ • U) : Space n → ℝ) =ᵐ[_] _
      rw [map_smul]
      have h := (Lp.coeFn_smul _ _).trans ((hD j).const_smul (d.factorial : ℝ)⁻¹)
      filter_upwards [h] with x hx
      simpa only [he,smul_eq_mul,Pi.smul_apply] using hx
    exact hleft.trans (listAppellTensorField_coe hμ (r+1) d t (Fin.cons j I)).symm
  change weightedH1Value φ (weightedGradientPrimitive (hφ.of_le (by simp)) hκ hlower
      (orderedTensorSlice r I (listAppellTensorField hμ (r+1) d t)))=_
  rw [←hgrad,weightedGradientPrimitive_gradient]
  apply Lp.ext
  have hleft : (weightedH1Value φ V : Space n → ℝ) =ᵐ[potentialMeasure φ]
      fun x => (d.factorial : ℝ)⁻¹ * normalizedContractedAppell hμ d s x := by
    change (weightedH1Value φ ((d.factorial : ℝ)⁻¹ • U) : Space n → ℝ) =ᵐ[_] _
    rw [map_smul]
    exact (Lp.coeFn_smul _ _).trans (hv.const_smul _)
  apply hleft.trans
  apply EventuallyEq.trans _ (listAppellTensorField_coe hμ r (d+1) t I).symm
  exact Eventually.of_forall fun x => by
    dsimp only [normalizedContractedAppell,s]
    rw [Nat.factorial_succ,Nat.cast_mul, _root_.mul_inv_rev]
    ring

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.listAppellTensorField_mean_zero
#print axioms KLS.DeterministicBridgeNext.compatibleTensorPrimitive_listAppellTensorField
