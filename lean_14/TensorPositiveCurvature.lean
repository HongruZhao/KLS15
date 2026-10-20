import PositiveMatrixRowGram

/-! Literal constrained tensor curvature (5.8), proved basis-free.
A positive matrix is decomposed into genuine physical rank-one row squares,
and each rank-one correction is controlled by the actual Koszul row. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology MatrixOrder
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ}

def tensorTwoFormNormSq (f : TensorTwoFormIndex n (r + 1) → ℝ) : ℝ :=
  ∑ I : OrderedTensorIndex n (r + 1), ∑ i, ∑ j, (f (I, i, j)) ^ 2

def tensorTwoFormCurvatureCorrection (K : Matrix (Fin n) (Fin n) ℝ)
    (f : TensorTwoFormIndex n (r + 1) → ℝ) : ℝ :=
  tensorTwoFormExteriorCurvatureForm K f -
    (1 / (r + 2 : ℕ)) * tensorTwoFormAuxiliaryCurvatureForm K f

lemma tensorTwoFormCurvatureCorrection_zero (f : TensorTwoFormIndex n (r + 1) → ℝ) :
    tensorTwoFormCurvatureCorrection 0 f = 0 := by
  simp [tensorTwoFormCurvatureCorrection, tensorTwoFormExteriorCurvatureForm,
    tensorTwoFormAuxiliaryCurvatureForm, tensorAuxiliaryCurvatureForm]

lemma tensorTwoFormCurvatureCorrection_add
    (K L : Matrix (Fin n) (Fin n) ℝ) (f : TensorTwoFormIndex n (r + 1) → ℝ) :
    tensorTwoFormCurvatureCorrection (K + L) f =
      tensorTwoFormCurvatureCorrection K f + tensorTwoFormCurvatureCorrection L f := by
  unfold tensorTwoFormCurvatureCorrection tensorTwoFormExteriorCurvatureForm
    tensorTwoFormAuxiliaryCurvatureForm tensorAuxiliaryCurvatureForm
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  ring

lemma tensorTwoFormCurvatureCorrection_sum {τ : Type*} (s : Finset τ)
    (K : τ → Matrix (Fin n) (Fin n) ℝ) (f : TensorTwoFormIndex n (r + 1) → ℝ) :
    tensorTwoFormCurvatureCorrection (∑ t ∈ s, K t) f =
      ∑ t ∈ s, tensorTwoFormCurvatureCorrection (K t) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tensorTwoFormCurvatureCorrection_zero]
  | @insert t s ht ih =>
      rw [Finset.sum_insert ht, Finset.sum_insert ht, tensorTwoFormCurvatureCorrection_add, ih]

lemma tensorAuxiliaryCurvatureForm_scalar_identity (a : ℝ)
    (f : OrderedTensorIndex n (r + 1) → ℝ) :
    tensorAuxiliaryCurvatureForm (a • (1 : Matrix (Fin n) (Fin n) ℝ)) f =
      (r + 1 : ℕ) * a * ∑ I, (f I) ^ 2 := by
  unfold tensorAuxiliaryCurvatureForm
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Function.update_eq_self]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Finset.mul_sum, mul_assoc, pow_two]

lemma tensorTwoFormAuxiliaryCurvatureForm_scalar_identity (a : ℝ)
    (f : TensorTwoFormIndex n (r + 1) → ℝ) :
    tensorTwoFormAuxiliaryCurvatureForm (a • (1 : Matrix (Fin n) (Fin n) ℝ)) f =
      (r + 1 : ℕ) * a * tensorTwoFormNormSq f := by
  unfold tensorTwoFormAuxiliaryCurvatureForm
  simp_rw [tensorAuxiliaryCurvatureForm_scalar_identity]
  simp only [← Finset.mul_sum]
  unfold tensorTwoFormNormSq
  congr 1
  calc
    _ = ∑ i : Fin n, ∑ I : OrderedTensorIndex n (r + 1), ∑ j : Fin n, (f (I, i, j)) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

lemma tensorTwoFormExteriorCurvatureForm_scalar_identity (a : ℝ)
    (f : TensorTwoFormIndex n (r + 1) → ℝ) :
    tensorTwoFormExteriorCurvatureForm (a • (1 : Matrix (Fin n) (Fin n) ℝ)) f =
      2 * a * tensorTwoFormNormSq f := by
  have hrow (I : OrderedTensorIndex n (r + 1)) (i : Fin n) :
      (∑ j, ∑ k, (a • (1 : Matrix (Fin n) (Fin n) ℝ)) i j * f (I, i, k) * f (I, j, k)) =
      a * ∑ k, (f (I, i, k)) ^ 2 := by
    rw [Finset.sum_comm]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [mul_assoc, ← pow_two, ← Finset.mul_sum]
  unfold tensorTwoFormExteriorCurvatureForm tensorTwoFormNormSq
  simp_rw [hrow]
  simp only [← Finset.mul_sum]
  ring

lemma tensorTwoFormCurvatureCorrection_scalar_identity (a : ℝ)
    (f : TensorTwoFormIndex n (r + 1) → ℝ) :
    tensorTwoFormCurvatureCorrection (a • (1 : Matrix (Fin n) (Fin n) ℝ)) f =
      ((r + 3 : ℕ) / (r + 2 : ℕ) : ℝ) * a * tensorTwoFormNormSq f := by
  unfold tensorTwoFormCurvatureCorrection
  rw [tensorTwoFormExteriorCurvatureForm_scalar_identity,
    tensorTwoFormAuxiliaryCurvatureForm_scalar_identity]
  push_cast
  field_simp
  ring

/-- Positivity of the actual constrained correction for every positive
semidefinite physical matrix. The finite square-root factorization is
proved, and the literal bω=0 constraint supplies each rank-one estimate. -/
theorem tensorTwoFormCurvatureCorrection_nonneg
    (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.PosSemidef)
    (f : TensorTwoFormIndex n (r + 1) → ℝ) (hf : TensorTwoFormCompatible f) :
    0 ≤ tensorTwoFormCurvatureCorrection K f := by
  obtain ⟨v, hv⟩ := positiveMatrix_row_gram K hK
  have he : K = ∑ s : Fin n, (fun i j => v s i * v s j) := by
    ext i j
    simpa only [Finset.sum_apply] using hv i j
  rw [he, tensorTwoFormCurvatureCorrection_sum]
  exact Finset.sum_nonneg fun s _ => tensorTwoForm_rank_one_curvature_nonneg (v s) f hf

/-- The literal finite constrained curvature bound (5.8), with auxiliary
rank q=r+1 and physical constant (q+2)/(q+1). No multiplicity-basis,
functional-calculus, or operator-domain premise is assumed. -/
theorem tensorTwoFormCurvatureCorrection_lower
    (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.IsSymm)
    (f : TensorTwoFormIndex n (r + 1) → ℝ) (hf : TensorTwoFormCompatible f)
    {a : ℝ} (hlower : ∀ v : Fin n → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (K *ᵥ v)) :
    ((r + 3 : ℕ) / (r + 2 : ℕ) : ℝ) * a * tensorTwoFormNormSq f ≤
      tensorTwoFormCurvatureCorrection K f := by
  have he : K = a • (1 : Matrix (Fin n) (Fin n) ℝ) +
      (K - a • (1 : Matrix (Fin n) (Fin n) ℝ)) := by abel
  rw [he, tensorTwoFormCurvatureCorrection_add, tensorTwoFormCurvatureCorrection_scalar_identity]
  exact le_add_of_nonneg_right (tensorTwoFormCurvatureCorrection_nonneg _
    (matrix_sub_scalar_identity_posSemidef K hK hlower) f hf)

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorTwoFormCurvatureCorrection_lower
