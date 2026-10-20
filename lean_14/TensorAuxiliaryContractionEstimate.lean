import TensorAuxiliaryCurvature

/-! The literal auxiliary contraction estimate used in (5.7).
The proof applies the established weighted vector Hodge identity to actual
first-slot slices and discards their nonnegative curl energy. Thus the
physical rank coefficient and all-slot curvature are proved directly,
without a commutation-relation or operator-domain assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ} {φ : Space n → ℝ}

/-- The actual c = Σ aᵢ∂ᵢ* on a rank-(r+1) auxiliary tensor. -/
def tensorAuxiliaryContraction (φ : Space n → ℝ)
    (F : OrderedTensorIndex n (r + 1) → Space n → ℝ)
    (I : OrderedTensorIndex n r) (x : Space n) : ℝ :=
  -Real.sqrt (r + 1 : ℕ) * weightedVectorDivergence φ (fun i => F (Fin.cons i I)) x

def tensorAuxiliaryGradientEnergy (φ : Space n → ℝ)
    (F : OrderedTensorIndex n (r + 1) → Space n → ℝ) : ℝ :=
  ∑ a, ∑ i, ∫ x, (coordinateDerivative (F a) i x) ^ 2 ∂potentialMeasure φ

def tensorAuxiliaryContractionEnergy (φ : Space n → ℝ)
    (F : OrderedTensorIndex n (r + 1) → Space n → ℝ) : ℝ :=
  ∑ I, ∫ x, (tensorAuxiliaryContraction φ F I x) ^ 2 ∂potentialMeasure φ

lemma tensorAuxiliaryContractionEnergy_eq (F : OrderedTensorIndex n (r + 1) → Space n → ℝ) :
    tensorAuxiliaryContractionEnergy φ F = (r + 1 : ℕ) *
      ∑ I : OrderedTensorIndex n r,
        ∫ x, (weightedVectorDivergence φ (fun i => F (Fin.cons i I)) x) ^ 2 ∂potentialMeasure φ := by
  unfold tensorAuxiliaryContractionEnergy
  have he (I : OrderedTensorIndex n r) (x : Space n) :
      (tensorAuxiliaryContraction φ F I x) ^ 2 = (r + 1 : ℕ) *
        (weightedVectorDivergence φ (fun i => F (Fin.cons i I)) x) ^ 2 := by
    unfold tensorAuxiliaryContraction
    rw [mul_pow, neg_sq, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp_rw [he, integral_const_mul]
  rw [Finset.mul_sum]

lemma tensorAuxiliaryGradientEnergy_eq_slices
    (F : OrderedTensorIndex n (r + 1) → Space n → ℝ) :
    tensorAuxiliaryGradientEnergy φ F =
      ∑ I : OrderedTensorIndex n r, ∑ i, ∑ j,
        ∫ x, (coordinateDerivative (F (Fin.cons j I)) i x) ^ 2 ∂potentialMeasure φ := by
  unfold tensorAuxiliaryGradientEnergy
  symm
  have he : (∑ I : OrderedTensorIndex n r, ∑ i, ∑ j,
      ∫ x, (coordinateDerivative (F (Fin.cons j I)) i x) ^ 2 ∂potentialMeasure φ) =
      ∑ I : OrderedTensorIndex n r, ∑ j, ∑ i,
        ∫ x, (coordinateDerivative (F (Fin.cons j I)) i x) ^ 2 ∂potentialMeasure φ := by
    exact Finset.sum_congr rfl (fun I _ => Finset.sum_comm)
  rw [he, Finset.sum_comm]
  calc
    _ = ∑ p : Fin n × OrderedTensorIndex n r, ∑ i,
        ∫ x, (coordinateDerivative (F (Fin.cons p.1 p.2)) i x) ^ 2 ∂potentialMeasure φ :=
      (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (r + 1) => Fin n))
      _ _ (fun _ => rfl)

lemma integral_tensorAuxiliaryCurvatureForm
    (hφ : ContDiff ℝ 2 φ) {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hF : ∀ I, ContDiff ℝ 2 (F I)) (hc : ∀ I, HasCompactSupport (F I))
    (hs : classicalTensorSymmetric F) :
    (∫ x, tensorAuxiliaryCurvatureForm (coordinateHessian φ x) (fun a => F a x)
      ∂potentialMeasure φ) =
      (r + 1 : ℕ) * ∑ I : OrderedTensorIndex n r, ∑ i, ∑ j,
        ∫ x, coordinateHessian φ x i j * F (Fin.cons i I) x * F (Fin.cons j I) x
          ∂potentialMeasure φ := by
  have hC (I : OrderedTensorIndex n r) (i j : Fin n) :
      Integrable (fun x => coordinateHessian φ x i j * F (Fin.cons i I) x *
        F (Fin.cons j I) x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (((contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous.mul
        (hF _).continuous).mul (hF _).continuous) (hc _).mul_left.mul_right
  have he (x : Space n) := tensorAuxiliaryCurvatureForm_eq_rank_mul
    (coordinateHessian φ x) (fun a => F a x) (fun a b hab => congrFun (hs a b hab) x)
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun I _ =>
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hC I i j)))]
  congr 1
  apply Finset.sum_congr rfl
  intro I _
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hC I i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hC I i j)]

/-- The precise analytic auxiliary estimate in (5.7), with genuine
compact C² fields, actual weighted derivatives, and literal all-slot
curvature. No convexity or probability normalization is needed. -/
theorem tensorAuxiliaryContractionEnergy_le
    (hφ : ContDiff ℝ 2 φ) {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hF : ∀ I, ContDiff ℝ 2 (F I)) (hc : ∀ I, HasCompactSupport (F I))
    (hs : classicalTensorSymmetric F) :
    tensorAuxiliaryContractionEnergy φ F ≤
      (r + 1 : ℕ) * tensorAuxiliaryGradientEnergy φ F +
      ∫ x, tensorAuxiliaryCurvatureForm (coordinateHessian φ x) (fun a => F a x)
        ∂potentialMeasure φ := by
  rw [tensorAuxiliaryContractionEnergy_eq, tensorAuxiliaryGradientEnergy_eq_slices,
    integral_tensorAuxiliaryCurvatureForm hφ hF hc hs, ← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (r + 1) : (0 : ℝ) ≤ (r + 1 : ℕ))
  apply Finset.sum_le_sum
  intro I _
  have he := integral_weightedHodge_core hφ (fun i => hF (Fin.cons i I))
    (fun i => hc (Fin.cons i I))
  have hn : 0 ≤ (1 / 2 : ℝ) * ∑ i, ∑ j,
      ∫ x, (vectorCurl (fun i => F (Fin.cons i I)) i j x) ^ 2 ∂potentialMeasure φ :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      integral_nonneg fun _ => sq_nonneg _)
  linarith

/-- Exterior coefficient families sum without altering the exact physical
rank constant in the auxiliary contraction bound. -/
theorem tensorAuxiliaryContractionEnergy_family_le {τ : Type*} [Fintype τ]
    (hφ : ContDiff ℝ 2 φ) {F : τ → OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hF : ∀ a I, ContDiff ℝ 2 (F a I)) (hc : ∀ a I, HasCompactSupport (F a I))
    (hs : ∀ a, classicalTensorSymmetric (F a)) :
    (∑ a, tensorAuxiliaryContractionEnergy φ (F a)) ≤
      (r + 1 : ℕ) * (∑ a, tensorAuxiliaryGradientEnergy φ (F a)) +
      ∑ a, ∫ x, tensorAuxiliaryCurvatureForm (coordinateHessian φ x) (fun I => F a I x)
        ∂potentialMeasure φ := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => tensorAuxiliaryContractionEnergy_le hφ (hF a) (hc a) (hs a)

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorAuxiliaryContractionEnergy_le
#print axioms KLS.DeterministicBridgeIntegration.tensorAuxiliaryContractionEnergy_family_le
