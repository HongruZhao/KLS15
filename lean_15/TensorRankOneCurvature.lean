import WeightedTwoFormCore

/-! Basis-free positive rank-one curvature on the literal constrained
ordered tensor fiber. The proof uses the actual Koszul projection identity,
not a diagonal multiplicity realization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ}

/-- Literal auxiliary curvature summed over normalized exterior coefficients. -/
def tensorTwoFormAuxiliaryCurvatureForm (K : Fin n → Fin n → ℝ)
    (f : TensorTwoFormIndex n (r + 1) → ℝ) : ℝ :=
  ∑ i, ∑ j, tensorAuxiliaryCurvatureForm K (fun I => f (I, i, j))

/-- Literal exterior curvature in normalized ordered two-form coordinates. -/
def tensorTwoFormExteriorCurvatureForm (K : Fin n → Fin n → ℝ)
    (f : TensorTwoFormIndex n (r + 1) → ℝ) : ℝ :=
  2 * ∑ I : OrderedTensorIndex n (r + 1), ∑ i, ∑ j, ∑ k,
    K i j * f (I, i, k) * f (I, j, k)

/-- The actual exterior contraction by a fixed physical vector. -/
def tensorTwoFormInterior (v : Fin n → ℝ) (f : TensorTwoFormIndex n (r + 1) → ℝ) :
    EuclideanSpace ℝ (TensorOneFormIndex n (r + 1)) :=
  WithLp.toLp 2 (fun a => ∑ i, v i * f (a.1, i, a.2))

lemma tensorTwoFormInterior_auxiliarySymmetric (v : Fin n → ℝ)
    (f : TensorTwoFormIndex n (r + 1) → ℝ) (hf : TensorTwoFormCompatible f) :
    tensorOneFormAuxiliarySymmetric (tensorTwoFormInterior v f) := by
  intro I J hp i
  change (∑ l, v l * f (I, l, i)) = ∑ l, v l * f (J, l, i)
  apply Finset.sum_congr rfl
  intro l _
  rw [hf.1 I J hp l i]

lemma tensorTwoFormInterior_cons_difference (v : Fin n → ℝ)
    (f : TensorTwoFormIndex n (r + 1) → ℝ) (hf : TensorTwoFormCompatible f)
    (I : OrderedTensorIndex n r) (i j : Fin n) :
    tensorTwoFormInterior v f (Fin.cons i I, j) -
      tensorTwoFormInterior v f (Fin.cons j I, i) =
        ∑ l, v l * f (Fin.cons l I, i, j) := by
  change (∑ l, v l * f (Fin.cons i I, l, j)) -
    (∑ l, v l * f (Fin.cons j I, l, i)) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← mul_sub, tensorTwoFormCompatible_cons_difference hf I i j l]

lemma finite_rank_one_quadratic (v f : Fin n → ℝ) :
    (∑ i, ∑ j, (v i * v j) * f i * f j) = (∑ i, v i * f i) ^ 2 := by
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma tensorTwoFormExteriorCurvatureForm_rank_one (v : Fin n → ℝ)
    (f : TensorTwoFormIndex n (r + 1) → ℝ) :
    tensorTwoFormExteriorCurvatureForm (fun i j => v i * v j) f =
      2 * ‖tensorTwoFormInterior v f‖ ^ 2 := by
  unfold tensorTwoFormExteriorCurvatureForm
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs, Fintype.sum_prod_type, tensorTwoFormInterior, PiLp.toLp_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro I _
  calc
    _ = ∑ k, ∑ i, ∑ j, (v i * v j) * f (I, i, k) * f (I, j, k) := by
      exact (finite_triple_sum_last_to_first (fun i j k =>
        (v i * v j) * f (I, i, k) * f (I, j, k))).symm
    _ = _ := by simp_rw [finite_rank_one_quadratic]

lemma tensorTwoFormAuxiliaryCurvatureForm_rank_one (v : Fin n → ℝ)
    (f : TensorTwoFormIndex n (r + 1) → ℝ) (hf : TensorTwoFormCompatible f) :
    tensorTwoFormAuxiliaryCurvatureForm (fun i j => v i * v j) f =
      2 * tensorOneFormKoszulNormSq (tensorTwoFormInterior v f) := by
  unfold tensorTwoFormAuxiliaryCurvatureForm
  have he (i j : Fin n) := tensorAuxiliaryCurvatureForm_eq_rank_mul
    (fun i j => v i * v j) (fun I => f (I, i, j)) (fun I J hp => hf.1 I J hp i j)
  simp_rw [he, finite_rank_one_quadratic]
  simp only [← Finset.mul_sum]
  have horder : (∑ i, ∑ j, ∑ I : OrderedTensorIndex n r,
      (∑ l, v l * f (Fin.cons l I, i, j)) ^ 2) =
      ∑ I : OrderedTensorIndex n r, ∑ i, ∑ j,
        (∑ l, v l * f (Fin.cons l I, i, j)) ^ 2 := by
    calc
      _ = ∑ i : Fin n, ∑ I : OrderedTensorIndex n r, ∑ j : Fin n,
          (∑ l, v l * f (Fin.cons l I, i, j)) ^ 2 :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [horder]
  unfold tensorOneFormKoszulNormSq
  simp_rw [tensorTwoFormInterior_cons_difference v f hf]
  ring

lemma tensorOneFormKoszulNormSq_le
    (w : EuclideanSpace ℝ (TensorOneFormIndex n (r + 1)))
    (hw : tensorOneFormAuxiliarySymmetric w) :
    tensorOneFormKoszulNormSq w ≤ (r + 2 : ℕ) * ‖w‖ ^ 2 := by
  have hp := Submodule.norm_sq_eq_add_norm_sq_starProjection w
    (tensorOneFormSymmetricFiber n (r + 1))
  rw [Submodule.starProjection_orthogonal_val] at hp
  change ‖w‖ ^ 2 = ‖tensorOneFormProjection n (r + 1) w‖ ^ 2 +
    ‖w - tensorOneFormProjection n (r + 1) w‖ ^ 2 at hp
  rw [tensorOneFormProjection_defect w hw] at hp
  have hm : (0 : ℝ) < (r + 2 : ℕ) := by positivity
  have hn := sq_nonneg ‖tensorOneFormProjection n (r + 1) w‖
  have hb : (1 / (r + 2 : ℕ)) * tensorOneFormKoszulNormSq w ≤ ‖w‖ ^ 2 := by linarith
  have hz := mul_le_mul_of_nonneg_left hb (le_of_lt hm)
  simpa only [← mul_assoc, mul_one_div_cancel (ne_of_gt hm), one_mul] using hz

/-- The genuine constrained curvature correction is nonnegative for every
positive rank-one physical matrix. This is the basis-free core of (5.8). -/
theorem tensorTwoForm_rank_one_curvature_nonneg (v : Fin n → ℝ)
    (f : TensorTwoFormIndex n (r + 1) → ℝ) (hf : TensorTwoFormCompatible f) :
    0 ≤ tensorTwoFormExteriorCurvatureForm (fun i j => v i * v j) f -
      (1 / (r + 2 : ℕ)) * tensorTwoFormAuxiliaryCurvatureForm (fun i j => v i * v j) f := by
  rw [tensorTwoFormExteriorCurvatureForm_rank_one,
    tensorTwoFormAuxiliaryCurvatureForm_rank_one v f hf]
  have h := tensorOneFormKoszulNormSq_le (tensorTwoFormInterior v f)
    (tensorTwoFormInterior_auxiliarySymmetric v f hf)
  have hm : (0 : ℝ) < (r + 2 : ℕ) := by positivity
  have hz := mul_le_mul_of_nonneg_left h (le_of_lt (one_div_pos.mpr hm))
  have he : (1 / (r + 2 : ℕ)) * ((r + 2 : ℕ) * ‖tensorTwoFormInterior v f‖ ^ 2) =
      ‖tensorTwoFormInterior v f‖ ^ 2 := by field_simp
  rw [he] at hz
  nlinarith

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorTwoForm_rank_one_curvature_nonneg
