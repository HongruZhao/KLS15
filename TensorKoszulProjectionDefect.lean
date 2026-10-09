import TensorProjectionEnergy

/-! Exact physical Koszul defect of the genuine orthogonal projection.
The exterior norm uses the half of the ordered pair sum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ}

/-- Squared norm of b on an actual auxiliary-rank-(r+1) one-form.
The factor (r+1)/2 is exactly the √(r+1) annihilation normalization and
the normalized ordered two-form convention. -/
def tensorOneFormKoszulNormSq
    (w : EuclideanSpace ℝ (TensorOneFormIndex n (r + 1))) : ℝ :=
  ((r + 1 : ℕ) / 2 : ℝ) * ∑ I : OrderedTensorIndex n r, ∑ i, ∑ j,
    (w (Fin.cons i I, j) - w (Fin.cons j I, i)) ^ 2

lemma tensorOneFormKoszulNormSq_eq
    (w : EuclideanSpace ℝ (TensorOneFormIndex n (r + 1))) :
    tensorOneFormKoszulNormSq w =
      (r + 1 : ℕ) * (‖w‖ ^ 2 - tensorOneFormCross w) := by
  have he (I : OrderedTensorIndex n r) (i j : Fin n) :
      (w (Fin.cons i I, j) - w (Fin.cons j I, i)) ^ 2 =
      (w (Fin.cons i I, j)) ^ 2 + (w (Fin.cons j I, i)) ^ 2 -
        2 * (w (Fin.cons i I, j) * w (Fin.cons j I, i)) := by ring
  have hn : (∑ I : OrderedTensorIndex n r, ∑ i, ∑ j,
      (w (Fin.cons j I, i)) ^ 2) = ‖w‖ ^ 2 := by
    rw [tensorOneForm_norm_sq_eq_slices]
    exact Finset.sum_congr rfl (fun I _ => Finset.sum_comm)
  unfold tensorOneFormKoszulNormSq
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← tensorOneForm_norm_sq_eq_slices, hn]
  unfold tensorOneFormCross
  ring

lemma tensorOneFormProjection_norm_sq
    (w : EuclideanSpace ℝ (TensorOneFormIndex n (r + 1)))
    (hw : tensorOneFormAuxiliarySymmetric w) :
    ‖tensorOneFormProjection n (r + 1) w‖ ^ 2 =
      (1 / (r + 2 : ℕ)) * (‖w‖ ^ 2 + (r + 1 : ℕ) * tensorOneFormCross w) := by
  have he := (tensorOneFormSymmetricFiber n (r + 1)).re_inner_starProjection_eq_normSq w
  have hc : ‖(tensorOneFormSymmetricFiber n (r + 1)).orthogonalProjectionOnto w‖ =
      ‖tensorOneFormProjection n (r + 1) w‖ := by rfl
  rw [hc] at he
  have hi : inner ℝ w (tensorOneFormProjection n (r + 1) w) =
      ‖tensorOneFormProjection n (r + 1) w‖ ^ 2 := by
    simpa only [RCLike.re_to_real, real_inner_comm, tensorOneFormProjection] using he
  rw [← hi, tensorOneFormProjection_eq_symmetrization w hw]
  exact tensorOneForm_inner_symmetrization w hw

/-- The exact physical projection defect used in (5.6): the complement
energy equals the Koszul energy divided by the one-form total rank. -/
theorem tensorOneFormProjection_defect
    (w : EuclideanSpace ℝ (TensorOneFormIndex n (r + 1)))
    (hw : tensorOneFormAuxiliarySymmetric w) :
    ‖w - tensorOneFormProjection n (r + 1) w‖ ^ 2 =
      (1 / (r + 2 : ℕ)) * tensorOneFormKoszulNormSq w := by
  have hp := Submodule.norm_sq_eq_add_norm_sq_starProjection w
    (tensorOneFormSymmetricFiber n (r + 1))
  rw [Submodule.starProjection_orthogonal_val] at hp
  change ‖w‖ ^ 2 = ‖tensorOneFormProjection n (r + 1) w‖ ^ 2 +
    ‖w - tensorOneFormProjection n (r + 1) w‖ ^ 2 at hp
  rw [tensorOneFormProjection_norm_sq w hw] at hp
  rw [tensorOneFormKoszulNormSq_eq]
  have hm : (r + 2 : ℝ) ≠ 0 := by positivity
  push_cast at hp ⊢
  field_simp at hp ⊢
  nlinarith

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorOneFormProjection_norm_sq
#print axioms KLS.DeterministicBridgeIntegration.tensorOneFormProjection_defect
