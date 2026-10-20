import TensorPositiveCurvature

/-! Actual compact constrained weighted Hodge form. The raw exterior
Bochner identity and the exact orthogonal-projection defect give the
physical auxiliary-rank constants. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ} {φ : Space n → ℝ}

lemma integrable_euclidean_norm_sq {ι : Type*} [Fintype ι]
    {f : Space n → EuclideanSpace ℝ ι}
    (hf : ∀ i, Integrable (fun x => (f x i) ^ 2) (potentialMeasure φ)) :
    Integrable (fun x => ‖f x‖ ^ 2) (potentialMeasure φ) := by
  simpa only [EuclideanSpace.real_norm_sq_eq] using
    integrable_finsetSum Finset.univ (fun i _ => hf i)

lemma integral_euclidean_norm_sq {ι : Type*} [Fintype ι]
    {f : Space n → EuclideanSpace ℝ ι}
    (hf : ∀ i, Integrable (fun x => (f x i) ^ 2) (potentialMeasure φ)) :
    (∫ x, ‖f x‖ ^ 2 ∂potentialMeasure φ) =
      ∑ i, ∫ x, (f x i) ^ 2 ∂potentialMeasure φ := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  exact integral_finsetSum Finset.univ (fun i _ => hf i)

lemma compact_coefficient_square_integrable (hφ : Continuous φ)
    {f : Space n → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun x => (f x) ^ 2) (potentialMeasure φ) :=
  integrable_potentialMeasure_of_continuous_hasCompactSupport hφ (hf.pow 2)
    (by simpa only [pow_two, Pi.mul_def] using hc.mul_right (f' := f))

lemma weightedVectorDivergence_continuous_compactCore
    (hφ : ContDiff ℝ 2 φ) {f : Fin n → Space n → ℝ}
    (hf : ∀ i, ContDiff ℝ 2 (f i)) : Continuous (weightedVectorDivergence φ f) := by
  unfold weightedVectorDivergence weightedDerivativeTest
  apply continuous_finsetSum
  intro i _
  exact ((contDiff_coordinateDerivative (hf i) (m := 0) (by norm_num) i).continuous).sub
    ((hf i).continuous.mul (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous)

lemma weightedVectorDivergence_compact_compactCore
    {f : Fin n → Space n → ℝ} (hc : ∀ i, HasCompactSupport (f i)) :
    HasCompactSupport (weightedVectorDivergence φ f) := by
  unfold weightedVectorDivergence weightedDerivativeTest
  apply compactSupport_finsetSum Finset.univ
  intro i _
  exact (hasCompactSupport_coordinateDerivative (hc i) i).sub (hc i).mul_right

lemma tensorTwoFormWeightedAdjoint_coefficient_continuous
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n r → Space n → ℝ}
    (hf : ∀ z, ContDiff ℝ 2 (f z)) (a : TensorOneFormIndex n r) :
    Continuous (fun x => tensorTwoFormWeightedAdjoint φ f x a) := by
  unfold tensorTwoFormWeightedAdjoint
  simp only [PiLp.toLp_apply]
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro i _
  exact ((contDiff_coordinateDerivative (hf _) (m := 0) (by norm_num) i).continuous.neg).add
    (((contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous).mul (hf _).continuous)

lemma tensorTwoFormWeightedAdjoint_coefficient_compact
    {f : TensorTwoFormIndex n r → Space n → ℝ}
    (hc : ∀ z, HasCompactSupport (f z)) (a : TensorOneFormIndex n r) :
    HasCompactSupport (fun x => tensorTwoFormWeightedAdjoint φ f x a) := by
  unfold tensorTwoFormWeightedAdjoint
  simp only [PiLp.toLp_apply]
  apply HasCompactSupport.mul_left
  apply compactSupport_finsetSum Finset.univ
  intro i _
  exact (hasCompactSupport_coordinateDerivative (hc _) i).neg.add (hc _).mul_left

lemma tensorProjectedAdjoint_coefficient_continuous
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n r → Space n → ℝ}
    (hf : ∀ z, ContDiff ℝ 2 (f z)) (a : TensorOneFormIndex n r) :
    Continuous (fun x => tensorOneFormProjection n r (tensorTwoFormWeightedAdjoint φ f x) a) := by
  simp_rw [tensorOneFormProjection_matrix_apply]
  apply continuous_finsetSum
  intro b _
  exact (tensorTwoFormWeightedAdjoint_coefficient_continuous hφ hf b).const_mul _

lemma tensorProjectedAdjoint_coefficient_compact
    {f : TensorTwoFormIndex n r → Space n → ℝ}
    (hc : ∀ z, HasCompactSupport (f z)) (a : TensorOneFormIndex n r) :
    HasCompactSupport (fun x => tensorOneFormProjection n r (tensorTwoFormWeightedAdjoint φ f x) a) := by
  simp_rw [tensorOneFormProjection_matrix_apply]
  apply compactSupport_finsetSum Finset.univ
  intro b _
  exact (tensorTwoFormWeightedAdjoint_coefficient_compact hc b).mul_left

def tensorTwoFormGradientEnergy (φ : Space n → ℝ)
    (f : TensorTwoFormIndex n (r + 1) → Space n → ℝ) : ℝ :=
  ∑ I : OrderedTensorIndex n (r + 1), twoFormGradientEnergy φ (fun i j => f (I, i, j))

def tensorTwoFormCurlEnergy (φ : Space n → ℝ)
    (f : TensorTwoFormIndex n (r + 1) → Space n → ℝ) : ℝ :=
  ∑ I : OrderedTensorIndex n (r + 1), twoFormCurlEnergy φ (fun i j => f (I, i, j))

def tensorTwoFormContractionEnergy (φ : Space n → ℝ)
    (f : TensorTwoFormIndex n (r + 1) → Space n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, tensorAuxiliaryContractionEnergy φ (fun I => f (I, i, j))

def tensorConstrainedHodgeEnergy (φ : Space n → ℝ)
    (f : TensorTwoFormIndex n (r + 1) → Space n → ℝ) : ℝ :=
  tensorTwoFormCurlEnergy φ f + ∫ x,
    ‖tensorOneFormProjection n (r + 1) (tensorTwoFormWeightedAdjoint φ f x)‖ ^ 2 ∂potentialMeasure φ

lemma tensorTwoFormWeightedAdjoint_norm_sq
    (f : TensorTwoFormIndex n (r + 1) → Space n → ℝ) (x : Space n) :
    ‖tensorTwoFormWeightedAdjoint φ f x‖ ^ 2 =
      2 * ∑ I : OrderedTensorIndex n (r + 1), ∑ j : Fin n,
        (weightedVectorDivergence φ (fun i => f (I, i, j)) x) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fintype.sum_prod_type, tensorTwoFormWeightedAdjoint, PiLp.toLp_apply,
    mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold weightedVectorDivergence weightedDerivativeTest
  have he (I : OrderedTensorIndex n (r + 1)) (j : Fin n) :
      (∑ i : Fin n, (-coordinateDerivative (f (I, i, j)) i x +
        coordinateDerivative φ i x * f (I, i, j) x)) =
      -(∑ i : Fin n, (coordinateDerivative (f (I, i, j)) i x -
        f (I, i, j) x * coordinateDerivative φ i x)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [he, neg_sq]
  simp only [Finset.mul_sum]

lemma integral_tensorTwoFormWeightedAdjoint_norm_sq
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ z, ContDiff ℝ 2 (f z)) (hc : ∀ z, HasCompactSupport (f z)) :
    (∫ x, ‖tensorTwoFormWeightedAdjoint φ f x‖ ^ 2 ∂potentialMeasure φ) =
      ∑ I : OrderedTensorIndex n (r + 1), twoFormAdjointEnergy φ (fun i j => f (I, i, j)) := by
  have hsq (I : OrderedTensorIndex n (r + 1)) (j : Fin n) :
      Integrable (fun x => (weightedVectorDivergence φ (fun i => f (I, i, j)) x) ^ 2)
        (potentialMeasure φ) :=
    compact_coefficient_square_integrable hφ.continuous
      (weightedVectorDivergence_continuous_compactCore hφ (fun i => hf _))
      (weightedVectorDivergence_compact_compactCore (fun i => hc _))
  simp_rw [tensorTwoFormWeightedAdjoint_norm_sq]
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun I _ =>
    integrable_finsetSum Finset.univ (fun j _ => hsq I j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hsq _ j)]
  simp only [twoFormAdjointEnergy, Finset.mul_sum]

lemma tensorTwoFormHodge_unprojected_identity
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ z, ContDiff ℝ 2 (f z)) (hc : ∀ z, HasCompactSupport (f z))
    (hs : ∀ I i j, f (I, i, j) = -f (I, j, i)) :
    tensorTwoFormCurlEnergy φ f +
      (∫ x, ‖tensorTwoFormWeightedAdjoint φ f x‖ ^ 2 ∂potentialMeasure φ) =
      tensorTwoFormGradientEnergy φ f +
        ∑ I : OrderedTensorIndex n (r + 1), twoFormCurvatureEnergy φ (fun i j => f (I, i, j)) := by
  rw [integral_tensorTwoFormWeightedAdjoint_norm_sq hφ hf hc]
  unfold tensorTwoFormCurlEnergy tensorTwoFormGradientEnergy
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun I _ => integral_weightedTwoFormHodge_core hφ
    (fun i j => hf _) (fun i j => hc _) (hs I))

lemma integral_tensorTwoForm_projection_loss
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ z, ContDiff ℝ 2 (f z)) (hc : ∀ z, HasCompactSupport (f z))
    (hF : ∀ x, TensorTwoFormCompatible (fun z => f z x)) :
    (∫ x, ‖tensorTwoFormWeightedAdjoint φ f x -
      tensorOneFormProjection n (r + 1) (tensorTwoFormWeightedAdjoint φ f x)‖ ^ 2
        ∂potentialMeasure φ) =
      (1 / (r + 2 : ℕ)) * tensorTwoFormContractionEnergy φ f := by
  have hsq (I : OrderedTensorIndex n r) (i j : Fin n) :
      Integrable (fun x => (tensorAuxiliaryContraction φ (fun a => f (a, i, j)) I x) ^ 2)
        (potentialMeasure φ) :=
    compact_coefficient_square_integrable hφ.continuous
      ((weightedVectorDivergence_continuous_compactCore hφ (fun l => hf _)).const_mul _)
      ((weightedVectorDivergence_compact_compactCore (fun l => hc _)).mul_left)
  simp_rw [tensorTwoFormWeightedAdjoint_projection_defect
    (fun z => (hf z).differentiable (by norm_num)) hF]
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun I _ =>
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hsq I i j)))]
  simp_rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hsq _ i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hsq _ _ j)]
  unfold tensorTwoFormContractionEnergy tensorAuxiliaryContractionEnergy
  congr 1
  calc
    _ = ∑ i : Fin n, ∑ I : OrderedTensorIndex n r, ∑ j : Fin n,
        ∫ x, (tensorAuxiliaryContraction φ (fun a => f (a, i, j)) I x) ^ 2 ∂potentialMeasure φ :=
      Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)

/-- Exact compact projected Hodge identity, including the actual auxiliary
contraction loss caused by the orthogonal one-form projection. -/
theorem tensorConstrainedHodgeEnergy_identity
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ z, ContDiff ℝ 2 (f z)) (hc : ∀ z, HasCompactSupport (f z))
    (hF : ∀ x, TensorTwoFormCompatible (fun z => f z x)) :
    tensorConstrainedHodgeEnergy φ f +
      (1 / (r + 2 : ℕ)) * tensorTwoFormContractionEnergy φ f =
      tensorTwoFormGradientEnergy φ f +
        ∑ I : OrderedTensorIndex n (r + 1), twoFormCurvatureEnergy φ (fun i j => f (I, i, j)) := by
  have hraw (a : TensorOneFormIndex n (r + 1)) :=
    compact_coefficient_square_integrable hφ.continuous
      (tensorTwoFormWeightedAdjoint_coefficient_continuous hφ hf a)
      (tensorTwoFormWeightedAdjoint_coefficient_compact hc a)
  have hproj (a : TensorOneFormIndex n (r + 1)) :=
    compact_coefficient_square_integrable hφ.continuous
      (tensorProjectedAdjoint_coefficient_continuous hφ hf a)
      (tensorProjectedAdjoint_coefficient_compact hc a)
  have hloss (a : TensorOneFormIndex n (r + 1)) :=
    compact_coefficient_square_integrable hφ.continuous
      ((tensorTwoFormWeightedAdjoint_coefficient_continuous hφ hf a).sub
        (tensorProjectedAdjoint_coefficient_continuous hφ hf a))
      ((tensorTwoFormWeightedAdjoint_coefficient_compact hc a).sub
        (tensorProjectedAdjoint_coefficient_compact hc a))
  have hpoint (x : Space n) : ‖tensorTwoFormWeightedAdjoint φ f x‖ ^ 2 =
      ‖tensorTwoFormWeightedAdjoint φ f x -
        tensorOneFormProjection n (r + 1) (tensorTwoFormWeightedAdjoint φ f x)‖ ^ 2 +
      ‖tensorOneFormProjection n (r + 1) (tensorTwoFormWeightedAdjoint φ f x)‖ ^ 2 := by
    simpa only [tensorOneFormProjection, Submodule.starProjection_orthogonal_val, add_comm] using
      Submodule.norm_sq_eq_add_norm_sq_starProjection (tensorTwoFormWeightedAdjoint φ f x)
        (tensorOneFormSymmetricFiber n (r + 1))
  have hint : (∫ x, ‖tensorTwoFormWeightedAdjoint φ f x‖ ^ 2 ∂potentialMeasure φ) =
      (1 / (r + 2 : ℕ)) * tensorTwoFormContractionEnergy φ f +
      (∫ x, ‖tensorOneFormProjection n (r + 1) (tensorTwoFormWeightedAdjoint φ f x)‖ ^ 2
        ∂potentialMeasure φ) := by
    have hli : Integrable (fun x => ‖tensorTwoFormWeightedAdjoint φ f x -
        tensorOneFormProjection n (r + 1) (tensorTwoFormWeightedAdjoint φ f x)‖ ^ 2)
        (potentialMeasure φ) := integrable_euclidean_norm_sq
          (f := fun x => tensorTwoFormWeightedAdjoint φ f x -
            tensorOneFormProjection n (r + 1) (tensorTwoFormWeightedAdjoint φ f x)) hloss
    have hpi : Integrable (fun x =>
        ‖tensorOneFormProjection n (r + 1) (tensorTwoFormWeightedAdjoint φ f x)‖ ^ 2)
        (potentialMeasure φ) := integrable_euclidean_norm_sq hproj
    calc
      _ = ∫ x, ‖tensorTwoFormWeightedAdjoint φ f x -
          tensorOneFormProjection n (r + 1) (tensorTwoFormWeightedAdjoint φ f x)‖ ^ 2 +
          ‖tensorOneFormProjection n (r + 1) (tensorTwoFormWeightedAdjoint φ f x)‖ ^ 2
          ∂potentialMeasure φ := integral_congr_ae (Eventually.of_forall hpoint)
      _ = _ := by rw [integral_add hli hpi, integral_tensorTwoForm_projection_loss hφ hf hc hF]
  have hid := tensorTwoFormHodge_unprojected_identity hφ hf hc
    (fun I i j => funext fun x => (hF x).2.1 I i j)
  unfold tensorConstrainedHodgeEnergy
  linarith

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorConstrainedHodgeEnergy_identity
