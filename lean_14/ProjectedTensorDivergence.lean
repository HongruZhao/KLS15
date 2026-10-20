import CompatibleTensorOperators
import TensorDivergenceCurl

/-! Literal compact tensor divergences and their actual orthogonal
projection onto Cᵣ. The norm identity is the paper's equation 5.3, including
the genuine projection correction. No correction estimate is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ} {φ : Space n → ℝ}

lemma compactSupport_finsetSum {ι : Type*} (s : Finset ι) {f : ι → Space n → ℝ}
    (hc : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : (fun x => ∑ i ∈ (∅ : Finset ι), f i x) = (0 : Space n → ℝ) := by
      funext x
      simp
    rw [he]
    exact HasCompactSupport.zero
  | @insert i s hi ih =>
    have he : (fun x => ∑ j ∈ insert i s, f j x) = f i + (fun x => ∑ j ∈ s, f j x) := by
      funext x
      simp only [Finset.sum_insert hi, Pi.add_apply]
    rw [he]
    exact (hc i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hc j (Finset.mem_insert_of_mem hj)))

def compactTensorLp (hφ : Continuous φ) (F : OrderedTensorIndex n r → Space n → ℝ)
    (hF : ∀ I, Continuous (F I)) (hc : ∀ I, HasCompactSupport (F I)) :
    OrderedTensorField φ r :=
  WithLp.toLp 2 (fun I => (memLp_of_continuous_hasCompactSupport hφ (hF I) (hc I)).toLp (F I))

lemma compactTensorLp_ae (hφ : Continuous φ) (F : OrderedTensorIndex n r → Space n → ℝ)
    (hF : ∀ I, Continuous (F I)) (hc : ∀ I, HasCompactSupport (F I)) (I : OrderedTensorIndex n r) :
    (compactTensorLp hφ F hF hc I : Space n → ℝ) =ᵐ[potentialMeasure φ] F I :=
  (memLp_of_continuous_hasCompactSupport hφ (hF I) (hc I)).coeFn_toLp

lemma contDiff_tensorAdjointDivergence {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hF : ∀ I, ContDiff ℝ 2 (F I)) (I : OrderedTensorIndex n r) :
    ContDiff ℝ 1 (tensorAdjointDivergence φ F I) :=
  (ContDiff.sum (fun j _ => contDiff_weightedDerivativeTest hφ (hF (Fin.cons j I)) j)).neg

lemma hasCompactSupport_tensorAdjointDivergence
    {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hc : ∀ I, HasCompactSupport (F I)) (I : OrderedTensorIndex n r) :
    HasCompactSupport (tensorAdjointDivergence φ F I) := by
  have hs := compactSupport_finsetSum (n := n) Finset.univ
    (fun j _ => weightedDerivativeTest_hasCompactSupport (φ := φ) (hc (Fin.cons j I)) j)
  have hs' : HasCompactSupport
      (fun x => ∑ j, weightedDerivativeTest φ (F (Fin.cons j I)) j x) := by simpa using hs
  exact hs'.neg

def tensorAdjointDivergenceLp {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hF : ∀ I, ContDiff ℝ 2 (F I))
    (hc : ∀ I, HasCompactSupport (F I)) : OrderedTensorField φ r :=
  compactTensorLp hφ.continuous (tensorAdjointDivergence φ F)
    (fun I => (contDiff_tensorAdjointDivergence hφ hF I).continuous)
    (hasCompactSupport_tensorAdjointDivergence hc)

lemma tensorAdjointDivergenceLp_ae {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hF : ∀ I, ContDiff ℝ 2 (F I))
    (hc : ∀ I, HasCompactSupport (F I)) (I : OrderedTensorIndex n r) :
    (tensorAdjointDivergenceLp hφ hF hc I : Space n → ℝ) =ᵐ[potentialMeasure φ]
      tensorAdjointDivergence φ F I :=
  compactTensorLp_ae hφ.continuous _ _ _ I

def tensorCompactProjection (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    OrderedTensorField φ r →L[ℝ] OrderedTensorField φ r :=
  (compatibleSymmetricTensorSubspace hφ r).starProjection

def projectedTensorDivergence {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hF : ∀ I, ContDiff ℝ 2 (F I))
    (hc : ∀ I, HasCompactSupport (F I)) : OrderedTensorField φ r :=
  tensorCompactProjection (hφ.of_le (by norm_num)) r (tensorAdjointDivergenceLp hφ hF hc)

theorem tensorAdjointDivergenceLp_norm_sq
    {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hF : ∀ I, ContDiff ℝ 2 (F I))
    (hc : ∀ I, HasCompactSupport (F I)) (hcomp : classicalTensorCompatible F) :
    ‖tensorAdjointDivergenceLp hφ hF hc‖ ^ 2 =
      (∑ I : OrderedTensorIndex n r, ∑ i, ∑ j, ∫ x,
        (coordinateDerivative (F (Fin.cons j I)) i x) ^ 2 ∂potentialMeasure φ) +
      ∑ I : OrderedTensorIndex n r, ∑ i, ∑ j, ∫ x,
        coordinateHessian φ x i j * F (Fin.cons i I) x * F (Fin.cons j I) x
          ∂potentialMeasure φ := by
  rw [PiLp.norm_sq_eq_of_L2, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I _
  have hn : ‖tensorAdjointDivergenceLp hφ hF hc I‖ ^ 2 =
      ∫ x, (weightedVectorDivergence φ (fun j => F (Fin.cons j I)) x) ^ 2
        ∂potentialMeasure φ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [tensorAdjointDivergenceLp_ae hφ hF hc I] with x hx
    simp only [hx, tensorAdjointDivergence, weightedVectorDivergence,
      RCLike.inner_apply, conj_trivial, neg_mul_neg, pow_two]
  have he := integral_weightedHodge_core hφ (fun j => hF (Fin.cons j I))
    (fun j => hc (Fin.cons j I))
  have hz (i j : Fin n) (x : Space n) :
      vectorCurl (fun j => F (Fin.cons j I)) i j x = 0 := by
    have hd := (hcomp I).coordinateDerivative_eq (fun j => hF (Fin.cons j I)) j i
    simp only [vectorCurl, congrFun hd x, sub_self]
  simp only [hz, zero_pow (by norm_num : 2 ≠ 0), integral_zero, Finset.sum_const_zero,
    mul_zero, add_zero] at he
  exact hn.trans he

/-- Exact physical ordered-index identity 5.3. The final correction is the
actual norm of the orthogonal projection residual, not a chosen error term. -/
theorem projectedTensorDivergence_norm_sq
    {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hF : ∀ I, ContDiff ℝ 2 (F I))
    (hc : ∀ I, HasCompactSupport (F I)) (hcomp : classicalTensorCompatible F) :
    ‖projectedTensorDivergence hφ hF hc‖ ^ 2 =
      (∑ I : OrderedTensorIndex n r, ∑ i, ∑ j, ∫ x,
        (coordinateDerivative (F (Fin.cons j I)) i x) ^ 2 ∂potentialMeasure φ) +
      (∑ I : OrderedTensorIndex n r, ∑ i, ∑ j, ∫ x,
        coordinateHessian φ x i j * F (Fin.cons i I) x * F (Fin.cons j I) x
          ∂potentialMeasure φ) -
      ‖tensorAdjointDivergenceLp hφ hF hc - projectedTensorDivergence hφ hF hc‖ ^ 2 := by
  have he := Submodule.norm_sq_eq_add_norm_sq_starProjection (tensorAdjointDivergenceLp hφ hF hc)
    (compatibleSymmetricTensorSubspace (hφ.of_le (by norm_num)) r)
  rw [Submodule.starProjection_orthogonal_val] at he
  rw [tensorAdjointDivergenceLp_norm_sq hφ hF hc hcomp] at he
  change _ = ‖projectedTensorDivergence hφ hF hc‖ ^ 2 +
    ‖tensorAdjointDivergenceLp hφ hF hc - projectedTensorDivergence hφ hF hc‖ ^ 2 at he
  linarith

theorem projectedTensorDivergence_graph_pairing
    {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hF : ∀ I, ContDiff ℝ 2 (F I))
    (hc : ∀ I, HasCompactSupport (F I))
    (U : TensorPrimitive (φ := φ) (OrderedTensorIndex n r))
    (hU : finitePrimitiveValue (OrderedTensorIndex n r) U ∈
      compatibleSymmetricTensorSubspace (hφ.of_le (by norm_num)) r) :
    inner ℝ (finitePrimitiveValue (OrderedTensorIndex n r) U)
      (projectedTensorDivergence hφ hF hc) =
      ∑ I : OrderedTensorIndex n r, ∑ j, ∫ x,
        weightedH1Derivative φ j (U I) x * F (Fin.cons j I) x ∂potentialMeasure φ := by
  have hp := (compatibleSymmetricTensorSubspace (hφ.of_le (by norm_num)) r).starProjection_inner_eq_zero
    (tensorAdjointDivergenceLp hφ hF hc)
      (finitePrimitiveValue (OrderedTensorIndex n r) U) hU
  rw [inner_sub_left] at hp
  have he : inner ℝ (finitePrimitiveValue (OrderedTensorIndex n r) U)
      (projectedTensorDivergence hφ hF hc) =
      inner ℝ (finitePrimitiveValue (OrderedTensorIndex n r) U)
        (tensorAdjointDivergenceLp hφ hF hc) := by
    calc
      _ = inner ℝ (projectedTensorDivergence hφ hF hc)
          (finitePrimitiveValue (OrderedTensorIndex n r) U) := real_inner_comm _ _
      _ = inner ℝ (tensorAdjointDivergenceLp hφ hF hc)
          (finitePrimitiveValue (OrderedTensorIndex n r) U) := (sub_eq_zero.mp hp).symm
      _ = _ := real_inner_comm _ _
  rw [he, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro I _
  rw [L2.inner_def]
  have hδ (j : Fin n) := memLp_weightedDerivativeTest (hφ.of_le (by norm_num))
    ((hF (Fin.cons j I)).of_le (by norm_num)) (hc (Fin.cons j I)) j
  have hI (j : Fin n) : Integrable (fun x => weightedH1Value φ (U I) x *
      weightedDerivativeTest φ (F (Fin.cons j I)) j x) (potentialMeasure φ) :=
    (Lp.memLp (weightedH1Value φ (U I))).integrable_mul (hδ j)
  calc
    _ = -(∫ x, ∑ j, weightedH1Value φ (U I) x *
        weightedDerivativeTest φ (F (Fin.cons j I)) j x ∂potentialMeasure φ) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [tensorAdjointDivergenceLp_ae hφ hF hc I] with x hx
      change inner ℝ (weightedH1Value φ (U I) x) (tensorAdjointDivergenceLp hφ hF hc I x) = _
      simp only [hx, tensorAdjointDivergence, RCLike.inner_apply, conj_trivial,
        neg_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j, -(∫ x, weightedH1Value φ (U I) x *
        weightedDerivativeTest φ (F (Fin.cons j I)) j x ∂potentialMeasure φ) := by
      rw [integral_finsetSum Finset.univ (fun j _ => hI j), Finset.sum_neg_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (weightedCenteredGradientGraph_weak_identity (hφ.of_le (by norm_num)) (U I)
        ((hF (Fin.cons j I)).of_le (by norm_num)) (hc (Fin.cons j I)) j).symm

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorAdjointDivergenceLp_norm_sq
#print axioms KLS.DeterministicBridgeIntegration.projectedTensorDivergence_norm_sq
#print axioms KLS.DeterministicBridgeIntegration.projectedTensorDivergence_graph_pairing
