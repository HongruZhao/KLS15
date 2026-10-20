import ActualCurvatureQuadraticReduction
import TensorCurvatureCoupling

/-! Literal compact-potential Bochner identity and actual projected norm
split (5.3), with the gradient energy identified as the next potential
tensor norm. Rank zero has identity projection and gives (5.2) directly. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
variable {n r : ℕ} {φ ψ : Space n → ℝ}

 theorem sum_ordered_tensor_cons (f : OrderedTensorIndex n (r+1) → ℝ) :
     (∑ I : OrderedTensorIndex n r, ∑ i : Fin n, f (Fin.cons i I))=∑ J, f J := by
   rw [Finset.sum_comm]
   calc
     _ = ∑ p : Fin n × OrderedTensorIndex n r, f (Fin.cons p.1 p.2) := (Fintype.sum_prod_type _).symm
     _ = _ := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (r+1) => Fin n)) _ _ (fun _ => rfl)

 theorem compactTensorLp_norm_sq_integral (hφ : Continuous φ)
     (F : OrderedTensorIndex n r → Space n → ℝ) (hF : ∀ I, Continuous (F I))
     (hc : ∀ I, HasCompactSupport (F I)) :
     ‖compactTensorLp hφ F hF hc‖^2=∑ I, ∫ x, (F I x)^2 ∂potentialMeasure φ := by
   rw [PiLp.norm_sq_eq_of_L2]
   apply Finset.sum_congr rfl
   intro I _
   rw [←real_inner_self_eq_norm_sq,L2.inner_def]
   apply integral_congr_ae
   filter_upwards [compactTensorLp_ae hφ F hF hc I] with x hx
   simp only [hx,RCLike.inner_apply,conj_trivial,pow_two]

 theorem compactPotentialTensorLp_gradient_norm_sq
     (hφ : Continuous φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℕ) :
     (∑ I : OrderedTensorIndex n r, ∑ i, ∑ j, ∫ x,
       (coordinateDerivative (coordinatePotentialTensor ψ (r+1) (Fin.cons j I)) i x)^2
         ∂potentialMeasure φ) = ‖compactPotentialTensorLp hφ hψ hc (r+2)‖^2 := by
   rw [compactPotentialTensorLp,compactTensorLp_norm_sq_integral]
   simp_rw [←coordinatePotentialTensor_cons]
   rw [Finset.sum_comm]
   calc
     _ = ∑ i : Fin n, ∑ J : OrderedTensorIndex n (r+1), ∫ x,
       (coordinatePotentialTensor ψ (r+2) (Fin.cons i J) x)^2 ∂potentialMeasure φ := by
       apply Finset.sum_congr rfl
       intro i _
       exact sum_ordered_tensor_cons (r := r)
         (fun J => ∫ x, (coordinatePotentialTensor ψ (r+2) (Fin.cons i J) x)^2 ∂potentialMeasure φ)
     _ = _ := by
       rw [Finset.sum_comm]
       exact sum_ordered_tensor_cons (r := r+1)
         (fun J => ∫ x, (coordinatePotentialTensor ψ (r+2) J x)^2 ∂potentialMeasure φ)

 def compactPotentialCurvatureEnergy (φ ψ : Space n → ℝ) (r : ℕ) : ℝ :=
   ∫ x, tensorPhysicalCurvatureForm (coordinateHessian φ x)
     (fun I => coordinatePotentialTensor ψ (r+1) I x) ∂potentialMeasure φ

 theorem compactPotentialCurvatureEnergy_eq_sum
     (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℕ) :
     compactPotentialCurvatureEnergy φ ψ r =
       ∑ I : OrderedTensorIndex n r, ∑ i, ∑ j, ∫ x,
         coordinateHessian φ x i j*coordinatePotentialTensor ψ (r+1) (Fin.cons i I) x*
           coordinatePotentialTensor ψ (r+1) (Fin.cons j I) x ∂potentialMeasure φ := by
   have hint (I : OrderedTensorIndex n r) (i j : Fin n) :
       Integrable (fun x => coordinateHessian φ x i j*coordinatePotentialTensor ψ (r+1) (Fin.cons i I) x*
         coordinatePotentialTensor ψ (r+1) (Fin.cons j I) x) (potentialMeasure φ) :=
     integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
       (((contDiff_coordinateHessian hφ (m := 0) (by simp) i j).continuous.mul
         (coordinatePotentialTensor_contDiff hψ (r+1) (Fin.cons i I)).continuous).mul
         (coordinatePotentialTensor_contDiff hψ (r+1) (Fin.cons j I)).continuous)
       ((coordinatePotentialTensor_hasCompactSupport hc (r+1) (Fin.cons i I)).mul_left.mul_right)
   unfold compactPotentialCurvatureEnergy tensorPhysicalCurvatureForm
   rw [integral_finsetSum Finset.univ (fun I _ => integrable_finsetSum Finset.univ
     (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hint I i j)))]
   simp_rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
     (fun j _ => hint _ i j)),integral_finsetSum Finset.univ (fun j _ => hint _ _ j)]

 theorem compactPotentialAdjointDivergence_bochner_identity
     (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℕ) :
     ‖tensorAdjointDivergenceLp hφ
       (fun I => (coordinatePotentialTensor_contDiff hψ (r+1) I).of_le (by simp))
       (coordinatePotentialTensor_hasCompactSupport hc (r+1))‖^2 =
       ‖compactPotentialTensorLp hφ.continuous hψ hc (r+2)‖^2+compactPotentialCurvatureEnergy φ ψ r := by
   rw [tensorAdjointDivergenceLp_norm_sq hφ _ _ (coordinatePotentialTensor_compatible hψ r),
     compactPotentialTensorLp_gradient_norm_sq hφ.continuous hψ hc r,
     compactPotentialCurvatureEnergy_eq_sum hφ hψ hc r]

 theorem compactPotentialProjectedDivergence_bochner_split
     (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℕ) :
     ‖compactPotentialProjectedDivergence hφ hψ hc r‖^2 =
       ‖compactPotentialTensorLp hφ.continuous hψ hc (r+2)‖^2+compactPotentialCurvatureEnergy φ ψ r-
       ‖tensorAdjointDivergenceLp hφ
         (fun I => (coordinatePotentialTensor_contDiff hψ (r+1) I).of_le (by simp))
         (coordinatePotentialTensor_hasCompactSupport hc (r+1))-
         compactPotentialProjectedDivergence hφ hψ hc r‖^2 := by
   unfold compactPotentialProjectedDivergence
   rw [projectedTensorDivergence_norm_sq hφ _ _ (coordinatePotentialTensor_compatible hψ r),
     compactPotentialTensorLp_gradient_norm_sq hφ.continuous hψ hc r,
     compactPotentialCurvatureEnergy_eq_sum hφ hψ hc r]

 theorem tensorCompactProjection_zero_eq (hφ : ContDiff ℝ 1 φ) (Y : OrderedTensorField φ 0) :
     tensorCompactProjection hφ 0 Y=Y := by
   apply (compatibleSymmetricTensorSubspace hφ 0).starProjection_eq_self_iff.mpr
   constructor
   · change Y ∈ orderedTensorSymmetricSubspace φ 0
     rw [mem_orderedTensorSymmetricSubspace_iff]
     intro I J _
     rw [Subsingleton.elim I J]
   · trivial

 theorem compactPotentialProjectedDivergence_zero_eq_raw
     (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
     compactPotentialProjectedDivergence hφ hψ hc 0=
       tensorAdjointDivergenceLp hφ
         (fun I => (coordinatePotentialTensor_contDiff hψ 1 I).of_le (by simp))
         (coordinatePotentialTensor_hasCompactSupport hc 1) := by
   exact tensorCompactProjection_zero_eq _ _

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialAdjointDivergence_bochner_identity
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialProjectedDivergence_bochner_split
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialProjectedDivergence_zero_eq_raw
