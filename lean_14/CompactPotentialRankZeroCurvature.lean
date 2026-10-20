import CompactPotentialBochnerSplit

/-! Physical Hessian energy lower bound in ordered coordinates and the
literal rank-zero case of compact curvature (5.2). No Hodge correction is
needed at rank zero because C₀ is the entire scalar tensor space. -/
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

 theorem tensorPhysicalCurvatureForm_lower_allRanks
     (K : Matrix (Fin n) (Fin n) ℝ) (F : OrderedTensorIndex n (r+1) → ℝ) {a : ℝ}
     (hlower : ∀ v : Fin n → ℝ, a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (K *ᵥ v)) :
     a*(∑ J, (F J)^2) ≤ tensorPhysicalCurvatureForm K F := by
   have hi (I : OrderedTensorIndex n r) :
       a*(∑ i, (F (Fin.cons i I))^2) ≤
         ∑ i, ∑ j, K i j*F (Fin.cons i I)*F (Fin.cons j I) := by
     have hv := hlower (fun i => F (Fin.cons i I))
     simpa only [dotProduct,Matrix.mulVec,Finset.mul_sum,pow_two,mul_assoc,mul_left_comm,mul_comm] using hv
   have hs := Finset.sum_le_sum (fun I (_ : I ∈ Finset.univ) => hi I)
   rw [←Finset.mul_sum,sum_ordered_tensor_cons (fun J => (F J)^2)] at hs
   exact hs

 theorem integrable_compactTensorPhysicalCurvatureForm
     (hφ : ContDiff ℝ 2 φ) (F : OrderedTensorIndex n (r+1) → Space n → ℝ)
     (hF : ∀ I, Continuous (F I)) (hc : ∀ I, HasCompactSupport (F I)) :
     Integrable (fun x => tensorPhysicalCurvatureForm (coordinateHessian φ x) (fun I => F I x))
       (potentialMeasure φ) := by
   unfold tensorPhysicalCurvatureForm
   apply integrable_finsetSum Finset.univ
   intro I _
   apply integrable_finsetSum Finset.univ
   intro i _
   apply integrable_finsetSum Finset.univ
   intro j _
   exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
     (((contDiff_coordinateHessian hφ (m := 0) (by simp) i j).continuous.mul
       (hF (Fin.cons i I))).mul (hF (Fin.cons j I)))
     ((hc (Fin.cons i I)).mul_left.mul_right)

 theorem compactPotentialCurvatureEnergy_lower
     (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℕ)
     {a : ℝ} (hlower : ∀ x (v : Fin n → ℝ),
       a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
     a*‖compactPotentialTensorLp hφ.continuous hψ hc (r+1)‖^2 ≤ compactPotentialCurvatureEnergy φ ψ r := by
   have hsq (I : OrderedTensorIndex n (r+1)) :
       Integrable (fun x => (coordinatePotentialTensor ψ (r+1) I x)^2) (potentialMeasure φ) :=
     integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
       ((coordinatePotentialTensor_contDiff hψ (r+1) I).continuous.pow 2)
       (by simpa only [pow_two,Pi.mul_def] using
         ((coordinatePotentialTensor_hasCompactSupport hc (r+1) I).mul_right (f' := coordinatePotentialTensor ψ (r+1) I)))
   have he : (∫ x, ∑ I : OrderedTensorIndex n (r+1),
       (coordinatePotentialTensor ψ (r+1) I x)^2 ∂potentialMeasure φ)=
       ‖compactPotentialTensorLp hφ.continuous hψ hc (r+1)‖^2 := by
     rw [integral_finsetSum Finset.univ (fun I _ => hsq I)]
     exact (compactTensorLp_norm_sq_integral hφ.continuous _ _ _).symm
   calc
     _ = ∫ x, a*(∑ I : OrderedTensorIndex n (r+1),
       (coordinatePotentialTensor ψ (r+1) I x)^2) ∂potentialMeasure φ := by
         rw [integral_const_mul,he]
     _ ≤ _ := integral_mono
       ((integrable_finsetSum Finset.univ (fun I _ => hsq I)).const_mul a)
       (integrable_compactTensorPhysicalCurvatureForm hφ _
         (fun I => (coordinatePotentialTensor_contDiff hψ (r+1) I).continuous)
         (coordinatePotentialTensor_hasCompactSupport hc (r+1)))
       (fun x => tensorPhysicalCurvatureForm_lower_allRanks _ _ (hlower x))

 theorem compactPotentialProjectedDivergence_rank_zero_curvature
     (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
     {a : ℝ} (hlower : ∀ x (v : Fin n → ℝ),
       a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
     ‖compactPotentialTensorLp hφ.continuous hψ hc 2‖^2+
       a*‖compactPotentialTensorLp hφ.continuous hψ hc 1‖^2 ≤
       ‖compactPotentialProjectedDivergence hφ hψ hc 0‖^2 := by
   rw [compactPotentialProjectedDivergence_zero_eq_raw,
     compactPotentialAdjointDivergence_bochner_identity hφ hψ hc 0]
   have hb := compactPotentialCurvatureEnergy_lower hφ hψ hc 0 hlower
   linarith

variable [IsProbabilityMeasure (potentialMeasure φ)]

 theorem compactPotentialDivergenceHilbert_bochner_split
     (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℕ) :
     ‖compactPotentialDivergenceHilbert hφ hψ hc r‖^2 =
       ‖compactPotentialTensorLp hφ.continuous hψ hc (r+2)‖^2+compactPotentialCurvatureEnergy φ ψ r-
       ‖tensorAdjointDivergenceLp (hφ.of_le (by simp))
         (fun I => (coordinatePotentialTensor_contDiff hψ (r+1) I).of_le (by simp))
         (coordinatePotentialTensor_hasCompactSupport hc (r+1))-
         compactPotentialProjectedDivergence (hφ.of_le (by simp)) hψ hc r‖^2 := by
   exact compactPotentialProjectedDivergence_bochner_split (hφ.of_le (by simp)) hψ hc r

 theorem compactPotentialDivergenceHilbert_rank_zero_curvature
     (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
     {a : ℝ} (hlower : ∀ x (v : Fin n → ℝ),
       a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
     ‖compactPotentialTensorLp hφ.continuous hψ hc 2‖^2+
       a*‖compactPotentialTensorLp hφ.continuous hψ hc 1‖^2 ≤
       ‖compactPotentialDivergenceHilbert hφ hψ hc 0‖^2 := by
   exact compactPotentialProjectedDivergence_rank_zero_curvature (hφ.of_le (by simp)) hψ hc hlower

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.tensorPhysicalCurvatureForm_lower_allRanks
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialCurvatureEnergy_lower
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialDivergenceHilbert_rank_zero_curvature

#print axioms KLS.DeterministicBridgeIntegration.compactPotentialDivergenceHilbert_bochner_split
