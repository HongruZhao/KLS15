import TensorKoszulProjectionDefect

/-! The exact projected weighted-adjoint loss on the actual constrained
auxiliary-symmetric two-form fiber. This is the physical algebraic input
to (5.6); all derivatives and the orthogonal projection are concrete. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ} {φ : Space n → ℝ}

@[simp] lemma tensorAuxReplaceFirst_cons (I : OrderedTensorIndex n r) (a i : Fin n) :
    tensorAuxReplaceFirst (Fin.cons a I) i = Fin.cons i I := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [tensorAuxReplaceFirst]
  · simp [tensorAuxReplaceFirst]

lemma tensorTwoFormCompatible_cons_difference
    {f : TensorTwoFormIndex n (r + 1) → ℝ} (hf : TensorTwoFormCompatible f)
    (I : OrderedTensorIndex n r) (i j l : Fin n) :
    f (Fin.cons i I, l, j) - f (Fin.cons j I, l, i) = f (Fin.cons l I, i, j) := by
  have hc := hf.2.2 (Fin.cons i I) i j l
  simp only [tensorAuxReplaceFirst_cons] at hc
  have hq : Real.sqrt (r + 1 : ℕ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hz := (mul_eq_zero.mp hc).resolve_left hq
  have hi := hf.2.1 (Fin.cons i I) l j
  have hj := hf.2.1 (Fin.cons j I) l i
  linarith

lemma tensorTwoFormWeightedAdjoint_auxiliarySymmetric
    {f : TensorTwoFormIndex n r → Space n → ℝ}
    (hf : ∀ x, TensorTwoFormCompatible (fun z => f z x)) (x : Space n) :
    tensorOneFormAuxiliarySymmetric (tensorTwoFormWeightedAdjoint φ f x) := by
  intro I J hp i
  unfold tensorTwoFormWeightedAdjoint
  simp only [PiLp.toLp_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  have he : f (I, l, i) = f (J, l, i) := funext fun x => (hf x).1 I J hp l i
  rw [he]

lemma tensorTwoFormWeightedAdjoint_cons_difference
    {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hfd : ∀ z, Differentiable ℝ (f z))
    (hf : ∀ x, TensorTwoFormCompatible (fun z => f z x))
    (I : OrderedTensorIndex n r) (i j : Fin n) (x : Space n) :
    tensorTwoFormWeightedAdjoint φ f x (Fin.cons i I, j) -
      tensorTwoFormWeightedAdjoint φ f x (Fin.cons j I, i) =
        Real.sqrt 2 * ∑ l : Fin n,
          (-coordinateDerivative (f (Fin.cons l I, i, j)) l x +
            coordinateDerivative φ l x * f (Fin.cons l I, i, j) x) := by
  unfold tensorTwoFormWeightedAdjoint
  simp only [PiLp.toLp_apply]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  have he : f (Fin.cons i I, l, j) - f (Fin.cons j I, l, i) =
      f (Fin.cons l I, i, j) :=
    funext fun x => tensorTwoFormCompatible_cons_difference (hf x) I i j l
  have hd := congrArg (fun g : Space n → ℝ => coordinateDerivative g l x) he
  change coordinateDerivative (fun y => f (Fin.cons i I, l, j) y -
    f (Fin.cons j I, l, i) y) l x = coordinateDerivative (f (Fin.cons l I, i, j)) l x at hd
  rw [coordinateDerivative_sub (hfd _ x) (hfd _ x)] at hd
  have hv := congrFun he x
  dsimp only [Pi.sub_apply] at hv
  rw [← hd, ← hv]
  ring

lemma tensorAuxiliaryContraction_eq_star
    (F : OrderedTensorIndex n (r + 1) → Space n → ℝ)
    (I : OrderedTensorIndex n r) (x : Space n) :
    tensorAuxiliaryContraction φ F I x = Real.sqrt (r + 1 : ℕ) *
      ∑ l : Fin n, (-coordinateDerivative (F (Fin.cons l I)) l x +
        coordinateDerivative φ l x * F (Fin.cons l I) x) := by
  unfold tensorAuxiliaryContraction weightedVectorDivergence weightedDerivativeTest
  have hs : (∑ l : Fin n, (-coordinateDerivative (F (Fin.cons l I)) l x +
      coordinateDerivative φ l x * F (Fin.cons l I) x)) =
      -(∑ l : Fin n, (coordinateDerivative (F (Fin.cons l I)) l x -
        F (Fin.cons l I) x * coordinateDerivative φ l x)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hs]
  ring

lemma tensorTwoFormWeightedAdjoint_koszulNormSq
    {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hfd : ∀ z, Differentiable ℝ (f z))
    (hf : ∀ x, TensorTwoFormCompatible (fun z => f z x)) (x : Space n) :
    tensorOneFormKoszulNormSq (tensorTwoFormWeightedAdjoint φ f x) =
      ∑ I : OrderedTensorIndex n r, ∑ i, ∑ j,
        (tensorAuxiliaryContraction φ (fun a => f (a, i, j)) I x) ^ 2 := by
  unfold tensorOneFormKoszulNormSq
  simp_rw [tensorTwoFormWeightedAdjoint_cons_difference hfd hf,
    tensorAuxiliaryContraction_eq_star, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (Nat.cast_nonneg (r + 1))]
  simp only [← Finset.mul_sum]
  ring

/-- Exact pointwise projection loss for the literal weighted d₁* on F₂.
The physical factor is 1/(r+2), and the right side is the actual auxiliary
contraction energy. No domain-density or curvature assumption is present. -/
theorem tensorTwoFormWeightedAdjoint_projection_defect
    {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hfd : ∀ z, Differentiable ℝ (f z))
    (hf : ∀ x, TensorTwoFormCompatible (fun z => f z x)) (x : Space n) :
    ‖tensorTwoFormWeightedAdjoint φ f x -
      tensorOneFormProjection n (r + 1) (tensorTwoFormWeightedAdjoint φ f x)‖ ^ 2 =
      (1 / (r + 2 : ℕ)) * ∑ I : OrderedTensorIndex n r, ∑ i, ∑ j,
        (tensorAuxiliaryContraction φ (fun a => f (a, i, j)) I x) ^ 2 := by
  rw [tensorOneFormProjection_defect _ (tensorTwoFormWeightedAdjoint_auxiliarySymmetric hf x),
    tensorTwoFormWeightedAdjoint_koszulNormSq hfd hf x]

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorTwoFormWeightedAdjoint_projection_defect
