import FirstOrderMatrixCalculus

/-! Actual cutoff product identities for maximal matrix differential
domains. The input need only satisfy the combined weak equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {ι ρ σ : Type*} [Fintype ι] [Fintype ρ] [Fintype σ]
  [DecidableEq ι] [DecidableEq ρ] [DecidableEq σ]

def matrixCutoffError (A : ρ → Fin n → ι → ℝ) (χ : Space n → ℝ)
    (f : ι → Space n → ℝ) (a : ρ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, A a i j * coordinateDerivative χ i x * f j x

theorem HasWeakMatrixDerivative.cutoff
    {A : ρ → Fin n → ι → ℝ} {f : ι → Space n → ℝ} {g : ρ → Space n → ℝ}
    (h : HasWeakMatrixDerivative A f g)
    (hf : ∀ j, LocallyIntegrable (f j) volume)
    (hg : ∀ a, LocallyIntegrable (g a) volume)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ) :
    HasWeakMatrixDerivative A (fun j x => χ x * f j x)
      (fun a x => χ x * g a x + matrixCutoffError A χ f a x) := by
  intro ψ hψ hcψ a
  have hi (i : Fin n) (j : ι) : Integrable
      (fun x => f j x * (χ x * coordinateDerivative ψ i x)) volume := by
    simpa only [smul_eq_mul, Pi.mul_apply] using (hf j).integrable_smul_right_of_hasCompactSupport
      (hχ.continuous.mul (contDiff_coordinateDerivative hψ (m := 0) (by simp) i).continuous)
      hcχ.mul_right
  have hj (i : Fin n) (j : ι) : Integrable
      (fun x => f j x * (coordinateDerivative χ i x * ψ x)) volume := by
    simpa only [smul_eq_mul, Pi.mul_apply] using (hf j).integrable_smul_right_of_hasCompactSupport
      ((contDiff_coordinateDerivative hχ (m := 0) (by simp) i).continuous.mul hψ.continuous)
      hcψ.mul_left
  have hgψ : Integrable (fun x => g a x * (χ x * ψ x)) volume := by
    simpa only [smul_eq_mul, Pi.mul_apply] using (hg a).integrable_smul_right_of_hasCompactSupport
      (hχ.continuous.mul hψ.continuous) hcχ.mul_right
  have he := h (fun x => χ x * ψ x) (hχ.mul hψ) hcχ.mul_right a
  have hsplit (i : Fin n) (j : ι) :
      (∫ x, f j x * coordinateDerivative (fun y => χ y * ψ y) i x) =
        (∫ x, f j x * (χ x * coordinateDerivative ψ i x)) +
          ∫ x, f j x * (coordinateDerivative χ i x * ψ x) := by
    rw [← integral_add (hi i j) (hj i j)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [coordinateDerivative_mul (hχ.differentiable (by simp) x)
        (hψ.differentiable (by simp) x)]
      ring
  simp only [hsplit, mul_add, Finset.sum_add_distrib] at he
  have hs (i : Fin n) (j : ι) : Integrable
      (fun x => (A a i j * coordinateDerivative χ i x * f j x) * ψ x) volume := by
    convert (hj i j).const_mul (A a i j) using 1
    funext x
    ring
  have hout :
      (∫ x, (χ x * g a x + matrixCutoffError A χ f a x) * ψ x) =
        (∫ x, g a x * (χ x * ψ x)) +
          ∑ i, ∑ j, A a i j * ∫ x, f j x * (coordinateDerivative χ i x * ψ x) := by
    have h1 : Integrable (fun x => χ x * g a x * ψ x) volume := by
      convert hgψ using 1
      funext x
      ring
    have h2 : Integrable (fun x => matrixCutoffError A χ f a x * ψ x) volume := by
      simpa only [matrixCutoffError, Finset.sum_mul] using
        integrable_finsetSum Finset.univ (fun i _ =>
          integrable_finsetSum Finset.univ (fun j _ => hs i j))
    rw [show (fun x => (χ x * g a x + matrixCutoffError A χ f a x) * ψ x) =
      (fun x => χ x * g a x * ψ x) + (fun x => matrixCutoffError A χ f a x * ψ x) by
      funext x; simp only [Pi.add_apply, add_mul]]
    change (∫ x, χ x * g a x * ψ x + matrixCutoffError A χ f a x * ψ x) = _
    rw [integral_add h1 h2]
    congr 1
    · apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    · simp only [matrixCutoffError, Finset.sum_mul]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hs i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hs i j)]
      apply Finset.sum_congr rfl
      intro j _
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
  rw [hout]
  have hr : (∑ i, ∑ j, A a i j * ∫ x, χ x * f j x * coordinateDerivative ψ i x) =
      ∑ i, ∑ j, A a i j * ∫ x, f j x * (χ x * coordinateDerivative ψ i x) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [hr]
  linarith

theorem cutoff_preserves_linear_constraint
    (C : σ → ι → ℝ) {f : ι → Space n → ℝ}
    (hC : ∀ a, (fun x => ∑ j, C a j * f j x) =ᵐ[volume] 0)
    (χ : Space n → ℝ) (a : σ) :
    (fun x => ∑ j, C a j * (χ x * f j x)) =ᵐ[volume] 0 := by
  filter_upwards [hC a] with x hx
  simp_rw [show ∀ j, C a j * (χ x * f j x) = χ x * (C a j * f j x) by intro j; ring]
  rw [← Finset.mul_sum, hx]
  simp

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.HasWeakMatrixDerivative.cutoff
#print axioms KLS.DeterministicBridgeIntegration.cutoff_preserves_linear_constraint
