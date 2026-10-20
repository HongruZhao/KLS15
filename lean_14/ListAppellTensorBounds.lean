import ListAppellTensorField

/-! Exact rank-uniform norm control of the genuine factorially normalized
Appell fields by their actual coefficient-observation operator. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

theorem listAppellTensorField_zero (hμ : admissibleMeasure (potentialMeasure φ))
    (r : ℕ) (t : List (Fin n) → ℝ) :
    listAppellTensorField hμ r 0 t=orderedConstantTensorField (φ := φ) (fun I => t (List.ofFn I)) := by
  apply PiLp.ext
  intro I
  simp only [listAppellTensorField_apply,Nat.factorial_zero,Nat.cast_one,inv_one,one_smul,
    orderedConstantTensorField_apply]
  apply ext_inner_right ℝ
  intro f
  rw [inner_polynomialLp_eq_integral,
    contractedAppellPolynomial_pairing hμ 0 _ (Lp.memLp f),real_inner_smul_left,
    CenteredL2.inner_oneLp]
  simp only [actualAppellCoefficient,iteratedFDeriv_zero_apply,exponentialTilt_zero,
    listAppellSlice,List.ofFn_zero,List.nil_append,Finset.sum_const,Finset.card_univ]
  simp

theorem orderedListConstant_mem_compatible (hφ : ContDiff ℝ 1 φ)
    (r : ℕ) (t : List (Fin n) → ℝ) (ht : ListTensorSymmetric t) :
    orderedConstantTensorField (φ := φ) (fun I : Fin r → Fin n => t (List.ofFn I)) ∈
      compatibleSymmetricTensorSubspace hφ r := by
  constructor
  · change orderedConstantTensorField (φ := φ) (fun I : Fin r → Fin n => t (List.ofFn I)) ∈
      orderedTensorSymmetricSubspace φ r
    rw [mem_orderedTensorSymmetricSubspace_iff]
    intro I J hIJ
    simp only [orderedConstantTensorField_apply,ht _ _ hIJ]
  · exact orderedConstantTensorField_mem_curl hφ _

theorem listAppellTensorField_mem_compatible {κ : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hμ : admissibleMeasure (potentialMeasure φ)) (r d : ℕ)
    (t : List (Fin n) → ℝ) (ht : ListTensorSymmetric t) :
    listAppellTensorField hμ r d t ∈ compatibleSymmetricTensorSubspace (hφ.of_le (by simp)) r := by
  induction d generalizing r with
  | zero => rw [listAppellTensorField_zero]; exact orderedListConstant_mem_compatible _ r t ht
  | succ d ih =>
      rw [←compatibleTensorPrimitive_listAppellTensorField hφ hκ hlower hμ r d t ht]
      exact compatibleTensorPrimitive_mem hφ hκ hlower _ (ih (r+1))

theorem listAppellTensorField_mem_centered {κ : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hμ : admissibleMeasure (potentialMeasure φ)) (r : ℕ) {d : ℕ} (hd : d ≠ 0)
    (t : List (Fin n) → ℝ) (ht : ListTensorSymmetric t) :
    listAppellTensorField hμ r d t ∈ centeredCompatibleTensorSubspace (hφ.of_le (by simp)) r := by
  rw [mem_centeredCompatibleTensorSubspace_iff]
  exact ⟨listAppellTensorField_mem_compatible hφ hκ hlower hμ r d t ht,
    listAppellTensorField_mean_zero hμ r hd t⟩

def tupleAppendEquiv (α : Type*) (d r : ℕ) :
    ((Fin d → α) × (Fin r → α)) ≃ (Fin (d+r) → α) where
  toFun p := Fin.append p.1 p.2
  invFun f := (fun i => f (Fin.castAdd r i),fun i => f (Fin.natAdd d i))
  left_inv p := by ext i <;> simp
  right_inv f := Fin.append_castAdd_natAdd

theorem listAppellSlice_norm_sum (r d : ℕ) (t : List (Fin n) → ℝ) :
    (∑ I : Fin r → Fin n, ∑ a : Fin d → Fin n, (listAppellSlice t I a)^2)=
      ∑ J : Fin (d+r) → Fin n, (t (List.ofFn J))^2 := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ p : (Fin d → Fin n) × (Fin r → Fin n), (t (List.ofFn p.1++List.ofFn p.2))^2 :=
      (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv (tupleAppendEquiv (Fin n) d r) _ _
      (fun p => by
        change t (List.ofFn p.1++List.ofFn p.2)^2=t (List.ofFn (Fin.append p.1 p.2))^2
        rw [List.ofFn_fin_append])

theorem listAppellTensorField_norm_sq_le (hμ : admissibleMeasure (potentialMeasure φ))
    (r d : ℕ) (t : List (Fin n) → ℝ) :
    ‖listAppellTensorField hμ r d t‖^2 ≤
      (d.factorial : ℝ)⁻¹^2 * ‖actualAppellObservation hμ d‖^2 *
        ‖orderedConstantTensorField (φ := φ) (fun J : Fin (d+r) → Fin n => t (List.ofFn J))‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2,orderedConstantTensorField_norm_sq]
  calc
    _ ≤ ∑ I : Fin r → Fin n, (d.factorial : ℝ)⁻¹^2 *
        (‖actualAppellObservation hμ d‖^2 * ∑ a : Fin d → Fin n, (listAppellSlice t I a)^2) := by
      apply Finset.sum_le_sum
      intro I hI
      simp only [listAppellTensorField_apply,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have hb := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (contractedAppellPolynomial_norm_le hμ d (listAppellSlice t I))
      simpa only [mul_pow,EuclideanSpace.real_norm_sq_eq] using hb
    _ = _ := by
      simp_rw [mul_assoc,←Finset.mul_sum]
      rw [listAppellSlice_norm_sum]

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.listAppellTensorField_zero
#print axioms KLS.DeterministicBridgeNext.listAppellTensorField_mem_centered
#print axioms KLS.DeterministicBridgeNext.listAppellTensorField_norm_sq_le
