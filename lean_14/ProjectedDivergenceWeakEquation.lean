import ActualCurvatureQuadraticReduction

/-! Orthogonality to the literal projected compact-potential divergences
gives the original weighted weak polyharmonic equation, before extra local
derivatives have been established. No integration by parts on the unknown
tensor is used in this step. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration
variable {n r : ℕ} {φ : Space n → ℝ}
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem compatible_tensor_projected_divergence_inner
    {F : OrderedTensorIndex n (r+1) → Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hF : ∀ I, ContDiff ℝ 2 (F I))
    (hc : ∀ I, HasCompactSupport (F I))
    (U : OrderedTensorField φ r)
    (hU : U ∈ compatibleSymmetricTensorSubspace (hφ.of_le (by norm_num)) r) :
    inner ℝ U (projectedTensorDivergence hφ hF hc) =
      -(∑ I : OrderedTensorIndex n r, ∑ j : Fin n,
        ∫ x, U I x*weightedDerivativeTest φ (F (Fin.cons j I)) j x ∂potentialMeasure φ) := by
  have hp := (compatibleSymmetricTensorSubspace (hφ.of_le (by norm_num)) r).starProjection_inner_eq_zero (tensorAdjointDivergenceLp hφ hF hc) U hU
  rw [inner_sub_left] at hp
  have he : inner ℝ U (projectedTensorDivergence hφ hF hc) =
      inner ℝ U (tensorAdjointDivergenceLp hφ hF hc) := by
    calc
      _ = inner ℝ (projectedTensorDivergence hφ hF hc) U := real_inner_comm _ _
      _ = inner ℝ (tensorAdjointDivergenceLp hφ hF hc) U := (sub_eq_zero.mp hp).symm
      _ = _ := real_inner_comm _ _
  rw [he,PiLp.inner_apply,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro I _
  rw [L2.inner_def]
  have hi (j : Fin n) : Integrable (fun x => U I x*
      weightedDerivativeTest φ (F (Fin.cons j I)) j x) (potentialMeasure φ) :=
    (Lp.memLp (U I)).integrable_mul (memLp_weightedDerivativeTest
      (hφ.of_le (by norm_num)) ((hF (Fin.cons j I)).of_le (by norm_num))
      (hc (Fin.cons j I)) j)
  rw [←integral_finsetSum Finset.univ (fun j _ => hi j),←integral_neg]
  apply integral_congr_ae
  filter_upwards [tensorAdjointDivergenceLp_ae hφ hF hc I] with x hx
  simp only [hx,tensorAdjointDivergence,RCLike.inner_apply,conj_trivial,
    neg_mul,Finset.sum_mul,mul_comm]

theorem density_weightedDerivativeTest_eq_coordinateDerivative
    {f : Space n → ℝ} (hφ : ContDiff ℝ 1 φ) (hf : ContDiff ℝ 1 f)
    (i : Fin n) (x : Space n) :
    weightedDerivativeTest φ f i x*Real.exp (-φ x) =
      coordinateDerivative (fun y => Real.exp (-φ y)*f y) i x := by
  have hdφ := hφ.differentiable (by norm_num) x
  have hdf := hf.differentiable (by norm_num) x
  have hρ : DifferentiableAt ℝ (fun y => Real.exp (-φ y)) x := by
    simpa only [Pi.neg_apply] using hdφ.neg.exp
  rw [coordinateDerivative_mul hρ hdf]
  change (coordinateDerivative f i x-f x*coordinateDerivative φ i x)*Real.exp (-φ x) =
    fderiv ℝ (fun y => Real.exp (-φ y)) x (EuclideanSpace.single i 1)*f x+
      Real.exp (-φ x)*coordinateDerivative f i x
  rw [fderiv_exp_neg_apply hdφ]
  change _= -(Real.exp (-φ x)*coordinateDerivative φ i x)*f x+_
  ring

variable [IsProbabilityMeasure (potentialMeasure φ)]

theorem compact_potential_orthogonality_weak_equation
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (U : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r)
    (horth : ∀ (ψ : Space n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
      (hc : HasCompactSupport ψ), inner ℝ U (compactPotentialDivergenceHilbert hφ hψ hc r)=0)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    (∑ I : OrderedTensorIndex n r, ∑ j : Fin n, ∫ x,
      U.val I x*coordinateDerivative
        (fun y => Real.exp (-φ y)*coordinatePotentialTensor ψ (r+1) (Fin.cons j I) y) j x)=0 := by
  have he := compatible_tensor_projected_divergence_inner
    (hφ.of_le (by simp))
    (fun I => (coordinatePotentialTensor_contDiff hψ (r+1) I).of_le (by simp))
    (coordinatePotentialTensor_hasCompactSupport hc (r+1)) U.val U.property.1
  have hz := horth ψ hψ hc
  change inner ℝ U.val (projectedTensorDivergence (hφ.of_le (by simp))
    (fun I => (coordinatePotentialTensor_contDiff hψ (r+1) I).of_le (by simp))
    (coordinatePotentialTensor_hasCompactSupport hc (r+1)))=0 at hz
  rw [he,neg_eq_zero] at hz
  convert hz using 1
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_potentialMeasure hφ.continuous.measurable]
  apply integral_congr_ae
  filter_upwards with x
  rw [mul_assoc,density_weightedDerivativeTest_eq_coordinateDerivative
    (hφ.of_le (by simp))
    ((coordinatePotentialTensor_contDiff hψ (r+1) (Fin.cons j I)).of_le (by simp))]

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.compact_potential_orthogonality_weak_equation
