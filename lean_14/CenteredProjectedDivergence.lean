import CompactPotentialTensor

/-! Compact weighted adjoint divergences have zero component means. Their
actual projection onto Cᵣ is therefore the actual projection onto Gᵣ.
This identifies the paper's compact-potential Sᵣ on its literal test domain;
no density of its image is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ} {φ : Space n → ℝ}

lemma integral_weightedDerivativeTest_compact_eq_zero {f : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (j : Fin n) :
    (∫ x, weightedDerivativeTest φ f j x ∂potentialMeasure φ) = 0 := by
  have he := integral_coordinateDerivative_mul_compact_test hφ
    (contDiff_const : ContDiff ℝ 1 (fun _ : Space n => (1 : ℝ))) hf hc j
  have hz : coordinateDerivative (fun _ : Space n => (1 : ℝ)) j = 0 := by
    funext x
    simp [coordinateDerivative]
  simp only [hz, Pi.zero_apply, zero_mul, integral_zero, one_mul] at he
  exact neg_eq_zero.mp he.symm

theorem tensorAdjointDivergenceLp_integral_eq_zero
    {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hF : ∀ I, ContDiff ℝ 2 (F I))
    (hc : ∀ I, HasCompactSupport (F I)) (I : OrderedTensorIndex n r) :
    (∫ x, tensorAdjointDivergenceLp hφ hF hc I x ∂potentialMeasure φ) = 0 := by
  rw [integral_congr_ae (tensorAdjointDivergenceLp_ae hφ hF hc I)]
  have hi (j : Fin n) : Integrable (weightedDerivativeTest φ (F (Fin.cons j I)) j)
      (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (weightedDerivativeTest_continuous (hφ.of_le (by norm_num))
        ((hF (Fin.cons j I)).of_le (by norm_num)) j)
      (weightedDerivativeTest_hasCompactSupport (hc (Fin.cons j I)) j)
  change (∫ x, -(∑ j, weightedDerivativeTest φ (F (Fin.cons j I)) j x)
    ∂potentialMeasure φ) = 0
  rw [integral_neg, integral_finsetSum Finset.univ (fun j _ => hi j)]
  suffices (∑ j, ∫ x, weightedDerivativeTest φ (F (Fin.cons j I)) j x
    ∂potentialMeasure φ) = 0 by rw [this, neg_zero]
  apply Finset.sum_eq_zero
  intro j _
  exact integral_weightedDerivativeTest_compact_eq_zero (hφ.of_le (by norm_num))
    ((hF (Fin.cons j I)).of_le (by norm_num)) (hc (Fin.cons j I)) j

section Probability
variable [IsProbabilityMeasure (potentialMeasure φ)]

lemma orderedTensorMeanPart_inner_of_integral_zero (Y F : OrderedTensorField φ r)
    (hY : ∀ I, (∫ x, Y I x ∂potentialMeasure φ) = 0) :
    inner ℝ (orderedTensorMeanPart φ r F) Y = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro I _
  rw [orderedTensorMeanPart_apply, inner_smul_left, CenteredL2.inner_oneLp, hY I, mul_zero]

theorem tensorCompactProjection_mem_centered (hφ : ContDiff ℝ 1 φ)
    (Y : OrderedTensorField φ r)
    (hY : ∀ I, (∫ x, Y I x ∂potentialMeasure φ) = 0) :
    tensorCompactProjection hφ r Y ∈ centeredCompatibleTensorSubspace hφ r := by
  let P := tensorCompactProjection hφ r Y
  have hP : P ∈ compatibleSymmetricTensorSubspace hφ r :=
    Submodule.starProjection_apply_mem _ _
  have hM : orderedTensorMeanPart φ r P ∈ compatibleSymmetricTensorSubspace hφ r :=
    orderedTensorMeanPart_mem hφ P hP
  have he := (compatibleSymmetricTensorSubspace hφ r).starProjection_inner_eq_zero
    Y (orderedTensorMeanPart φ r P) hM
  change inner ℝ (Y - P) (orderedTensorMeanPart φ r P) = 0 at he
  have hYM : inner ℝ Y (orderedTensorMeanPart φ r P) = 0 :=
    (real_inner_comm _ _).trans (orderedTensorMeanPart_inner_of_integral_zero Y P hY)
  rw [inner_sub_left, hYM, zero_sub, neg_eq_zero] at he
  have hs : P = orderedTensorMeanPart φ r P + orderedTensorCenter φ r P := by
    change P = orderedTensorMeanPart φ r P + (P - orderedTensorMeanPart φ r P)
    abel
  have hn : inner ℝ P (orderedTensorMeanPart φ r P) =
      ‖orderedTensorMeanPart φ r P‖ ^ 2 := by
    calc
      _ = inner ℝ (orderedTensorMeanPart φ r P) P := real_inner_comm _ _
      _ = inner ℝ (orderedTensorMeanPart φ r P)
          (orderedTensorMeanPart φ r P + orderedTensorCenter φ r P) := congrArg _ hs
      _ = _ := by rw [inner_add_right, orderedTensorMeanPart_inner_center P,
        add_zero, real_inner_self_eq_norm_sq]
  have hz : orderedTensorMeanPart φ r P = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (orderedTensorMeanPart φ r P)]
  exact ⟨hP, hz⟩

theorem centeredTensorProjection_eq_compactProjection (hφ : ContDiff ℝ 1 φ)
    (Y : OrderedTensorField φ r)
    (hY : ∀ I, (∫ x, Y I x ∂potentialMeasure φ) = 0) :
    (centeredCompatibleTensorSubspace hφ r).starProjection Y = tensorCompactProjection hφ r Y := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (tensorCompactProjection_mem_centered hφ Y hY)
  intro Z hZ
  exact (compatibleSymmetricTensorSubspace hφ r).starProjection_inner_eq_zero Y Z hZ.1

theorem projectedTensorDivergence_mem_centered
    {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hF : ∀ I, ContDiff ℝ 2 (F I))
    (hc : ∀ I, HasCompactSupport (F I)) :
    projectedTensorDivergence hφ hF hc ∈
      centeredCompatibleTensorSubspace (hφ.of_le (by norm_num)) r :=
  tensorCompactProjection_mem_centered _ _ (tensorAdjointDivergenceLp_integral_eq_zero hφ hF hc)

theorem compactPotentialProjectedDivergence_mem_centered (hφ : ContDiff ℝ 2 φ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℕ) :
    compactPotentialProjectedDivergence hφ hψ hc r ∈
      centeredCompatibleTensorSubspace (hφ.of_le (by norm_num)) r :=
  projectedTensorDivergence_mem_centered _ _ _

end Probability
end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorAdjointDivergenceLp_integral_eq_zero
#print axioms KLS.DeterministicBridgeIntegration.tensorCompactProjection_mem_centered
#print axioms KLS.DeterministicBridgeIntegration.centeredTensorProjection_eq_compactProjection
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialProjectedDivergence_mem_centered
