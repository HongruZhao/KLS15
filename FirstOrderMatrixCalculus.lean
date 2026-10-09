import TensorGradientCompactCore
import KLS.WeakDerivativeMollification

/-! Literal constant-principal-matrix weak differential operators. These
identities apply simultaneously to a curl and a projected divergence,
without assuming individual coordinate weak derivatives of the input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Convolution Topology
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {ι ρ σ : Type*} [Fintype ι] [Fintype ρ] [Fintype σ]
  [DecidableEq ι] [DecidableEq ρ] [DecidableEq σ]

def matrixDifferential (A : ρ → Fin n → ι → ℝ) (f : ι → Space n → ℝ)
    (a : ρ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, A a i j * coordinateDerivative (f j) i x

def HasWeakMatrixDerivative (A : ρ → Fin n → ι → ℝ)
    (f : ι → Space n → ℝ) (g : ρ → Space n → ℝ) : Prop :=
  ∀ (ψ : Space n → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    ∀ a, (∫ x, g a x * ψ x) =
      -(∑ i, ∑ j, A a i j * ∫ x, f j x * coordinateDerivative ψ i x)

lemma matrixDifferential_hasWeakMatrixDerivative
    (A : ρ → Fin n → ι → ℝ) {f : ι → Space n → ℝ}
    (hf : ∀ j, ContDiff ℝ 1 (f j)) :
    HasWeakMatrixDerivative A f (matrixDifferential A f) := by
  intro ψ hψ hc a
  have hi (i : Fin n) (j : ι) : Integrable
      (fun x => (A a i j * coordinateDerivative (f j) i x) * ψ x) volume := by
    have hh := ((contDiff_coordinateDerivative (hf j) (m := 0) (by norm_num) i).continuous.const_mul
      (A a i j)).locallyIntegrable (μ := volume) |>.integrable_smul_right_of_hasCompactSupport hψ.continuous hc
    simpa only [smul_eq_mul] using hh
  have he (i : Fin n) (j : ι) :=
    hasLocalWeakCoordinateDerivative_of_locallyLipschitz (hf j).locallyLipschitz i
      ψ (hψ.of_le (by simp)) hc
  simp only [matrixDifferential, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [mul_assoc]
  rw [integral_const_mul, he i j]
  ring

/-- The entire constant-coefficient derivative combination commutes with
actual mollification. No coordinate-by-coordinate Sobolev premise occurs. -/
theorem HasWeakMatrixDerivative.mollify_eq
    {A : ρ → Fin n → ι → ℝ} {f : ι → Space n → ℝ} {g : ρ → Space n → ℝ}
    (h : HasWeakMatrixDerivative A f g)
    (hf : ∀ j, LocallyIntegrable (f j) volume)
    (hg : ∀ a, LocallyIntegrable (g a) volume) (k : ℕ) (a : ρ) (x : Space n) :
    matrixDifferential A (fun j => mollify k (f j)) a x = mollify k (g a) x := by
  let θ := mollifierKernel (n := n) k
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := mollifierKernel_contDiff k
  have hcθ : HasCompactSupport θ := mollifierKernel_hasCompactSupport k
  have he := h (fun y => θ (x - y))
    (hθ.comp (contDiff_const.sub contDiff_id))
    (hcθ.comp_homeomorph (Homeomorph.subLeft x)) a
  have hi (j : ι) (i : Fin n) :
      (∫ y, f j y * coordinateDerivative (fun z => θ (x - z)) i y) =
        -(coordinateDerivative (mollify k (f j)) i x) := by
    rw [show mollify k (f j) = KLS.scalarConvolution (f j) θ from rfl,
      coordinateDerivative_scalarConvolution (hf j) (hθ.of_le (by simp)) hcθ]
    unfold KLS.scalarConvolution
    rw [convolution_def, ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [coordinateDerivative_const_sub (hθ.differentiable (by simp))]
      simp
  have hgθ : (∫ y, g a y * θ (x - y)) = mollify k (g a) x := by
    unfold KLS.mollify KLS.scalarConvolution
    rw [convolution_def]
    rfl
  rw [hgθ] at he
  simp only [hi, mul_neg, Finset.sum_neg_distrib, neg_neg] at he
  exact he.symm

/-- Fixed linear fiber constraints survive actual convolution. This is
the constraint-preserving part of the Hodge graph-core approximation. -/
theorem mollify_preserves_linear_constraint
    (C : σ → ι → ℝ) {f : ι → Space n → ℝ}
    (hf : ∀ j, LocallyIntegrable (f j) volume)
    (hC : ∀ a, (fun x => ∑ j, C a j * f j x) =ᵐ[volume] 0)
    (k : ℕ) (a : σ) (x : Space n) :
    (∑ j, C a j * mollify k (f j) x) = 0 := by
  have hi (j : ι) : Integrable
      (fun y => (C a j * f j y) * mollifierKernel (n := n) k (x - y)) volume := by
    have hh := (hf j).integrable_smul_right_of_hasCompactSupport
      ((mollifierKernel_contDiff k).continuous.comp (continuous_const.sub continuous_id))
      ((mollifierKernel_hasCompactSupport k).comp_homeomorph (Homeomorph.subLeft x))
    simpa only [smul_eq_mul, mul_assoc, Function.comp_def, Pi.sub_apply, id_eq]
      using hh.const_mul (C a j)
  calc
    _ = ∑ j, ∫ y, (C a j * f j y) * mollifierKernel (n := n) k (x - y) := by
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [mul_assoc]
      rw [integral_const_mul]
      rfl
    _ = ∫ y, ∑ j, (C a j * f j y) * mollifierKernel (n := n) k (x - y) :=
      (integral_finsetSum _ (fun j _ => hi j)).symm
    _ = 0 := by
      have he : (fun y => ∑ j, (C a j * f j y) * mollifierKernel (n := n) k (x - y)) =ᵐ[volume] 0 := by
        filter_upwards [hC a] with y hy
        rw [← Finset.sum_mul, hy]
        simp
      rw [integral_congr_ae he]
      simp only [Pi.zero_apply, integral_zero]

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.HasWeakMatrixDerivative.mollify_eq
#print axioms KLS.DeterministicBridgeIntegration.mollify_preserves_linear_constraint
