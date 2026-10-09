import CompatibleTensorSpace
import KLS.LocalLipschitzWeakDerivative

/-! The actual higher tensor divergence/curl commutator. Ordinary
distributional compatibility is upgraded to pointwise compatibility only
after genuine C² regularity is supplied. Every derivative of F then cancels,
leaving the actual Hessian of the potential (paper equation 5.4). -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ}

theorem DistributionallyCurlFree.coordinateDerivative_eq
    {F : Fin n → Space n → ℝ} (hcurl : DistributionallyCurlFree F)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (i j : Fin n) :
    coordinateDerivative (F i) j = coordinateDerivative (F j) i := by
  have hd (k l : Fin n) : Continuous (coordinateDerivative (F k) l) :=
    (contDiff_coordinateDerivative (hF k) (m := 0) (by norm_num) l).continuous
  have hae : coordinateDerivative (F i) j =ᵐ[volume] coordinateDerivative (F j) i := by
    apply ae_eq_of_integral_contDiff_smul_eq (hd i j).locallyIntegrable (hd j i).locallyIntegrable
    intro ψ hψ hc
    have hi := hasLocalWeakCoordinateDerivative_of_locallyLipschitz
      ((hF i).of_le (by norm_num) : ContDiff ℝ 1 (F i)).locallyLipschitz j
      ψ (hψ.of_le (by simp)) hc
    have hj := hasLocalWeakCoordinateDerivative_of_locallyLipschitz
      ((hF j).of_le (by norm_num) : ContDiff ℝ 1 (F j)).locallyLipschitz i
      ψ (hψ.of_le (by simp)) hc
    have he := neg_injective (hi.symm.trans ((hcurl ψ hψ hc i j).trans hj))
    simpa only [smul_eq_mul, mul_comm] using he
  exact MeasureTheory.Measure.eq_of_ae_eq hae (hd i j) (hd j i)

def classicalTensorSymmetric (F : OrderedTensorIndex n r → Space n → ℝ) : Prop :=
  ∀ I J, List.Perm (List.ofFn I) (List.ofFn J) → F I = F J

def classicalTensorCompatible (F : OrderedTensorIndex n (r + 1) → Space n → ℝ) : Prop :=
  ∀ I : OrderedTensorIndex n r, DistributionallyCurlFree (fun i x => F (Fin.cons i I) x)

lemma classicalTensorSymmetric_swap
    {F : OrderedTensorIndex n (r + 2) → Space n → ℝ}
    (hF : classicalTensorSymmetric F) (I : OrderedTensorIndex n r) (i j : Fin n) :
    F (Fin.cons i (Fin.cons j I)) = F (Fin.cons j (Fin.cons i I)) := by
  apply hF
  simpa only [List.ofFn_cons] using List.Perm.swap j i (List.ofFn I)

/-- Positive weighted adjoint divergence, ∑ⱼ(-∂ⱼ+φⱼ)FⱼI.
Its sign is the opposite of the earlier vector-divergence convention. -/
def tensorAdjointDivergence (φ : Space n → ℝ)
    (F : OrderedTensorIndex n (r + 1) → Space n → ℝ)
    (I : OrderedTensorIndex n r) (x : Space n) : ℝ :=
  -(∑ j, weightedDerivativeTest φ (F (Fin.cons j I)) j x)

lemma coordinateDerivative_tensorAdjointDivergence {φ : Space n → ℝ}
    {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hF : ∀ I, ContDiff ℝ 2 (F I))
    (I : OrderedTensorIndex n r) (k : Fin n) (x : Space n) :
    coordinateDerivative (tensorAdjointDivergence φ F I) k x =
      -(∑ j, coordinateDerivative (weightedDerivativeTest φ (F (Fin.cons j I)) j) k x) := by
  have hd (j : Fin n) := (contDiff_weightedDerivativeTest hφ (hF (Fin.cons j I)) j).differentiable
    (by norm_num) x
  have hs : DifferentiableAt ℝ
      (fun y => ∑ j, weightedDerivativeTest φ (F (Fin.cons j I)) j y) x :=
    DifferentiableAt.fun_sum (fun j _ => hd j)
  have he := hs.hasFDerivAt.neg.fderiv
  change fderiv ℝ (tensorAdjointDivergence φ F I) x =
    -fderiv ℝ (fun y => ∑ j, weightedDerivativeTest φ (F (Fin.cons j I)) j y) x at he
  unfold coordinateDerivative
  rw [he]
  change -coordinateDerivative
    (fun y => ∑ j, weightedDerivativeTest φ (F (Fin.cons j I)) j y) k x = _
  rw [coordinateDerivative_sum hd]
  rfl

/-- Exact equation 5.4 for every genuinely distributionally compatible,
classically symmetric C² tensor field. No derivative or density property
of a constrained operator is a premise. -/
theorem tensorAdjointDivergence_curl {φ : Space n → ℝ}
    {F : OrderedTensorIndex n (r + 2) → Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hF : ∀ I, ContDiff ℝ 2 (F I))
    (hsym : classicalTensorSymmetric F) (hcomp : classicalTensorCompatible F)
    (I : OrderedTensorIndex n r) (k l : Fin n) (x : Space n) :
    coordinateDerivative (tensorAdjointDivergence φ F (Fin.cons l I)) k x -
        coordinateDerivative (tensorAdjointDivergence φ F (Fin.cons k I)) l x =
      ∑ j, (coordinateHessian φ x k j * F (Fin.cons j (Fin.cons l I)) x -
        coordinateHessian φ x l j * F (Fin.cons j (Fin.cons k I)) x) := by
  have hc (j : Fin n) : coordinateDerivative (F (Fin.cons j (Fin.cons l I))) k =
      coordinateDerivative (F (Fin.cons j (Fin.cons k I))) l := by
    rw [classicalTensorSymmetric_swap hsym I j l,
      classicalTensorSymmetric_swap hsym I j k]
    exact (hcomp (Fin.cons j I)).coordinateDerivative_eq
      (fun i => hF (Fin.cons i (Fin.cons j I))) l k
  rw [coordinateDerivative_tensorAdjointDivergence hφ hF,
    coordinateDerivative_tensorAdjointDivergence hφ hF]
  simp_rw [coordinateDerivative_weightedDerivativeTest hφ (hF _), hc]
  simp only [Finset.sum_sub_distrib]
  have he (a : Fin n) (J : OrderedTensorIndex n (r + 1)) :
      (∑ j, F (Fin.cons j J) x * coordinateHessian φ x a j) =
        ∑ j, coordinateHessian φ x a j * F (Fin.cons j J) x := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, he]
  ring

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.DistributionallyCurlFree.coordinateDerivative_eq
#print axioms KLS.DeterministicBridgeIntegration.tensorAdjointDivergence_curl
