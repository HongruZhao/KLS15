import TensorTwoFormAlgebra

/-! The unprojected weighted Hodge identity on literal compact C²
exterior two-form coefficients, with the physical ordered-coordinate
normalizations. It reuses the actual weighted vector divergence identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {φ : Space n → ℝ}

lemma integral_finite_triple_sum {ι : Type*} [Fintype ι]
    {f : ι → ι → ι → Space n → ℝ}
    (hf : ∀ i j k, Integrable (f i j k) (potentialMeasure φ)) :
    (∫ x, ∑ i, ∑ j, ∑ k, f i j k x ∂potentialMeasure φ) =
      ∑ i, ∑ j, ∑ k, ∫ x, f i j k x ∂potentialMeasure φ := by
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
    (fun j _ => integrable_finsetSum Finset.univ (fun k _ => hf i j k)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => hf i j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun k _ => hf i j k)]

lemma finite_triple_sum_last_to_first {ι : Type*} [Fintype ι]
    (f : ι → ι → ι → ℝ) :
    (∑ k, ∑ i, ∑ j, f i j k) = ∑ i, ∑ j, ∑ k, f i j k := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)

def twoFormGradientEnergy (φ : Space n → ℝ) (f : Fin n → Fin n → Space n → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∫ x, (coordinateDerivative (f j k) i x) ^ 2 ∂potentialMeasure φ

def twoFormMixedEnergy (φ : Space n → ℝ) (f : Fin n → Fin n → Space n → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∫ x,
    coordinateDerivative (f i k) j x * coordinateDerivative (f j k) i x ∂potentialMeasure φ

def twoFormCurvatureEnergy (φ : Space n → ℝ) (f : Fin n → Fin n → Space n → ℝ) : ℝ :=
  2 * ∑ i, ∑ j, ∑ k, ∫ x, coordinateHessian φ x i j * f i k x * f j k x ∂potentialMeasure φ

def twoFormCurlEnergy (φ : Space n → ℝ) (f : Fin n → Fin n → Space n → ℝ) : ℝ :=
  (1 / 3 : ℝ) * ∑ i, ∑ j, ∑ k, ∫ x,
    (coordinateDerivative (f j k) i x - coordinateDerivative (f i k) j x +
      coordinateDerivative (f i j) k x) ^ 2 ∂potentialMeasure φ

def twoFormAdjointEnergy (φ : Space n → ℝ) (f : Fin n → Fin n → Space n → ℝ) : ℝ :=
  2 * ∑ k, ∫ x, (weightedVectorDivergence φ (fun i => f i k) x) ^ 2 ∂potentialMeasure φ

lemma twoForm_coordinateDerivative_skew
    {f : Fin n → Fin n → Space n → ℝ} (hs : ∀ i j, f i j = -f j i)
    (i j k : Fin n) (x : Space n) :
    coordinateDerivative (f j k) i x = -coordinateDerivative (f k j) i x := by
  rw [hs j k]
  simp only [coordinateDerivative, fderiv_neg, ContinuousLinearMap.neg_apply]

lemma twoFormCurlEnergy_eq
    (hφ : Continuous φ) {f : Fin n → Fin n → Space n → ℝ}
    (hf : ∀ i j, ContDiff ℝ 2 (f i j)) (hc : ∀ i j, HasCompactSupport (f i j))
    (hs : ∀ i j, f i j = -f j i) :
    twoFormCurlEnergy φ f = twoFormGradientEnergy φ f - 2 * twoFormMixedEnergy φ f := by
  have hd (i j k : Fin n) : Continuous (coordinateDerivative (f j k) i) :=
    (contDiff_coordinateDerivative (hf j k) (m := 0) (by norm_num) i).continuous
  have hA (i j k : Fin n) : Integrable
      (fun x => (coordinateDerivative (f j k) i x) ^ 2) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ ((hd i j k).pow 2)
      (by simpa only [pow_two, Pi.mul_def] using
        (hasCompactSupport_coordinateDerivative (hc j k) i).mul_right (f' := coordinateDerivative (f j k) i))
  have hM (i j k : Fin n) : Integrable
      (fun x => coordinateDerivative (f j k) i x * coordinateDerivative (f i k) j x)
        (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ ((hd i j k).mul (hd j i k))
      (hasCompactSupport_coordinateDerivative (hc j k) i).mul_right
  have hC (i j k : Fin n) : Integrable (fun x =>
      (coordinateDerivative (f j k) i x - coordinateDerivative (f i k) j x +
        coordinateDerivative (f i j) k x) ^ 2) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ
      ((((hd i j k).sub (hd j i k)).add (hd k i j)).pow 2)
      (by
        have ht := ((hasCompactSupport_coordinateDerivative (hc j k) i).sub
          (hasCompactSupport_coordinateDerivative (hc i k) j)).add
          (hasCompactSupport_coordinateDerivative (hc i j) k)
        simpa only [pow_two, Pi.mul_def, Pi.sub_apply, Pi.add_apply] using ht.mul_right (f' := fun x =>
          coordinateDerivative (f j k) i x - coordinateDerivative (f i k) j x +
            coordinateDerivative (f i j) k x))
  have hAs : Integrable (fun x => ∑ i, ∑ j, ∑ k,
      (coordinateDerivative (f j k) i x) ^ 2) (potentialMeasure φ) :=
    integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => integrable_finsetSum Finset.univ (fun k _ => hA i j k)))
  have hMs : Integrable (fun x => ∑ i, ∑ j, ∑ k,
      coordinateDerivative (f j k) i x * coordinateDerivative (f i k) j x)
      (potentialMeasure φ) :=
    integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => integrable_finsetSum Finset.univ (fun k _ => hM i j k)))
  have he : (∫ x, (1 / 3 : ℝ) * ∑ i, ∑ j, ∑ k,
      (coordinateDerivative (f j k) i x - coordinateDerivative (f i k) j x +
        coordinateDerivative (f i j) k x) ^ 2 ∂potentialMeasure φ) =
      ∫ x, (∑ i, ∑ j, ∑ k, (coordinateDerivative (f j k) i x) ^ 2) -
        2 * ∑ i, ∑ j, ∑ k, coordinateDerivative (f j k) i x * coordinateDerivative (f i k) j x
          ∂potentialMeasure φ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => exteriorTwoForm_kinetic_identity
      (fun i j k => coordinateDerivative (f j k) i x)
      (fun i j k => twoForm_coordinateDerivative_skew hs i j k x)
  rw [integral_const_mul, integral_finite_triple_sum hC,
    integral_sub hAs (hMs.const_mul 2), integral_const_mul,
    integral_finite_triple_sum hA, integral_finite_triple_sum hM] at he
  simpa only [twoFormCurlEnergy, twoFormGradientEnergy, twoFormMixedEnergy, mul_comm] using he

lemma twoFormAdjointEnergy_eq
    (hφ : ContDiff ℝ 2 φ) {f : Fin n → Fin n → Space n → ℝ}
    (hf : ∀ i j, ContDiff ℝ 2 (f i j)) (hc : ∀ i j, HasCompactSupport (f i j)) :
    twoFormAdjointEnergy φ f = 2 * twoFormMixedEnergy φ f + twoFormCurvatureEnergy φ f := by
  unfold twoFormAdjointEnergy
  simp_rw [integral_weightedVectorDivergence_sq hφ (fun i => hf i _) (fun i => hc i _)]
  rw [Finset.sum_add_distrib, mul_add]
  unfold twoFormMixedEnergy twoFormCurvatureEnergy
  congr 1
  · exact congrArg (fun z : ℝ => 2 * z) (finite_triple_sum_last_to_first _)
  · exact congrArg (fun z : ℝ => 2 * z) (finite_triple_sum_last_to_first _)

/-- Exact compact C² weighted exterior Hodge identity, including the
physical three-form and one-form normalization factors. -/
theorem integral_weightedTwoFormHodge_core
    (hφ : ContDiff ℝ 2 φ) {f : Fin n → Fin n → Space n → ℝ}
    (hf : ∀ i j, ContDiff ℝ 2 (f i j)) (hc : ∀ i j, HasCompactSupport (f i j))
    (hs : ∀ i j, f i j = -f j i) :
    twoFormCurlEnergy φ f + twoFormAdjointEnergy φ f =
      twoFormGradientEnergy φ f + twoFormCurvatureEnergy φ f := by
  rw [twoFormCurlEnergy_eq hφ.continuous hf hc hs, twoFormAdjointEnergy_eq hφ hf hc]
  ring

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.integral_weightedTwoFormHodge_core
