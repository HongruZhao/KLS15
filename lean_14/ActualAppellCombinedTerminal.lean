import ActualAppellTerminalSplit
import ActualEnergyQuotientMaximum

/-! The linear-test cancellation at a genuine maximizer and the exact
lower-degree remainder estimates. This preserves both terminal cumulants
before bounding them, as required in manuscript (3.20). -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem actualAppellEnergy_eq_tensor_norm_sq {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) (d : ℕ) : actualAppellEnergy μ f d = ‖fullClassAppellTensor d f‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

 theorem actualAppell_tensor_inner_array {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) (d : ℕ) (v : (Fin d → Fin n) → ℝ) :
    inner ℝ (fullClassAppellTensor d f)
      (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d → Fin n)) = actualAppellCoefficient μ f d ⬝ᵥ v := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,fullClassAppellTensor,
    star_trivial]
  exact dotProduct_comm _ _

 theorem fullClassAppellTensor_linear_observable {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hiso : IsIsotropic μ) (b : Space n) (d : ℕ) :
    fullClassAppellTensor d (isotropicLinearObservable hiso b) =
      WithLp.toLp 2 (actualAppellCoefficient μ (fun x => inner ℝ x b) d) := by
  apply PiLp.ext
  intro a
  exact actualAppellCoefficient_congr_ae (isotropicLinearObservable_coe hiso b) d a

 theorem actualAppell_weighted_terminal_le
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ)
    (hunit : ‖f‖=1) (k : ℕ) {h q : ℝ} (hh : 0 < h) (hq : 0 ≤ q)
    (hstat : ∀ ell : Lp ℝ 2 μ,
      inner ℝ (fullClassAppellTensor (k+1) f) (fullClassAppellTensor (k+1) ell)+
        actualAppellEnergy μ f (k+1)*q/h*
          inner ℝ (fullClassAppellTensor k f) (fullClassAppellTensor k ell) =
        actualAppellEnergy μ f (k+1)*(1+(actualAppellEnergy μ f k/h)*q)*inner ℝ f ell) :
    (actualAppellCoefficient μ f (k+1) ⬝ᵥ actualAppellCoefficient μ
        (fun x => inner ℝ x (affineProjectionVector hμ.isotropic f)) (k+1))+
      actualAppellEnergy μ f (k+1)*q/h*
        (actualAppellCoefficient μ f k ⬝ᵥ actualAppellCoefficient μ
          (fun x => inner ℝ x (affineProjectionVector hμ.isotropic f)) k) ≤
      actualAppellEnergy μ f (k+1)*(1+(actualAppellEnergy μ f k/h)*q) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hs := hstat (isotropicLinearObservable hμ.isotropic (affineProjectionVector hμ.isotropic f))
  rw [fullClassAppellTensor_linear_observable,fullClassAppellTensor_linear_observable,
    actualAppell_tensor_inner_array,actualAppell_tensor_inner_array,
    inner_isotropicLinearObservable_projection] at hs
  rw [hs]
  have hb : ‖affineProjectionVector hμ.isotropic f‖^2 ≤ 1 := by
    simpa only [hunit,one_pow] using affineProjectionVector_norm_sq_le_full hμ.isotropic f
  have hp : 0 ≤ actualAppellEnergy μ f (k+1)*(1+(actualAppellEnergy μ f k/h)*q) := by
    exact mul_nonneg (actualAppellEnergy_nonneg _ _ _)
      (by have hy : 0 ≤ actualAppellEnergy μ f k/h :=
            div_nonneg (actualAppellEnergy_nonneg _ _ _) hh.le
          linarith [mul_nonneg hy hq])
  exact mul_le_of_le_one_right hp hb

 theorem actualAppellProperRemainder_pairing_le
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ)
    (hunit : ‖f‖=1) {d k : ℕ} (hd : d ≤ k+1) {h : ℕ → ℝ}
    (hh : ∀ r : ℕ, 1 ≤ r → r ≤ k → 0 ≤ h r)
    (hprevious : ∀ r : ℕ, 1 ≤ r → r ≤ k → ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualAppellEnergy μ g r ≤ h r*(∫ x, (g x)^2 ∂μ)) :
    actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d ≤
      Real.sqrt (actualAppellEnergy μ f d)*actualLowerConvolution h d := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hu : (∫ x, (f x)^2 ∂μ) = 1 := by
    have hn : ‖f‖^2 = ∫ x, (f x)^2 ∂μ := by
      rw [←real_inner_self_eq_norm_sq,L2.inner_def]
      simp only [RCLike.inner_apply,conj_trivial,pow_two]
    rw [← hn,hunit,one_pow]
  have hb := actualAppellProperRemainder_norm_le hμ (Lp.memLp f) hu hd hh hprevious
  have hn : ‖fullClassAppellTensor d f‖ = Real.sqrt (actualAppellEnergy μ f d) := by
    rw [actualAppellEnergy_eq_tensor_norm_sq,Real.sqrt_sq (norm_nonneg _)]
  rw [← actualAppell_tensor_inner_array]
  exact (real_inner_le_norm _ _).trans (by rw [hn]; exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _))

 theorem actualAppell_weighted_drift_pairing_le
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ)
    (hunit : ‖f‖=1) {k : ℕ} (hk : 2 ≤ k) {h : ℕ → ℝ} (hhk : 0 < h k)
    (hh : ∀ r : ℕ, 1 ≤ r → r ≤ k → 0 ≤ h r)
    (hprevious : ∀ r : ℕ, 1 ≤ r → r ≤ k → ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualAppellEnergy μ g r ≤ h r*(∫ x, (g x)^2 ∂μ)) {q : ℝ} (hq : 0 ≤ q)
    (hstat : ∀ ell : Lp ℝ 2 μ,
      inner ℝ (fullClassAppellTensor (k+1) f) (fullClassAppellTensor (k+1) ell)+
        actualAppellEnergy μ f (k+1)*q/(h k)*
          inner ℝ (fullClassAppellTensor k f) (fullClassAppellTensor k ell) =
        actualAppellEnergy μ f (k+1)*(1+(actualAppellEnergy μ f k/(h k))*q)*inner ℝ f ell) :
    (actualAppellCoefficient μ f (k+1) ⬝ᵥ actualAppellLowerDriftTensor μ f (k+1))+
      actualAppellEnergy μ f (k+1)*q/(h k)*
        (actualAppellCoefficient μ f k ⬝ᵥ actualAppellLowerDriftTensor μ f k) ≤
      actualAppellEnergy μ f (k+1)*(1+(actualAppellEnergy μ f k/(h k))*q)+
        Real.sqrt (actualAppellEnergy μ f (k+1))*actualLowerConvolution h (k+1)+
        actualAppellEnergy μ f (k+1)*q/(h k)*
          Real.sqrt (actualAppellEnergy μ f k)*actualLowerConvolution h k := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have ht := actualAppell_weighted_terminal_le hμ f hunit k hhk hq hstat
  have hj := actualAppellProperRemainder_pairing_le hμ f hunit (show k+1 ≤ k+1 from le_rfl) hh hprevious
  have hl := actualAppellProperRemainder_pairing_le hμ f hunit (show k ≤ k+1 by omega) hh hprevious
  have hw : 0 ≤ actualAppellEnergy μ f (k+1)*q/(h k) :=
    div_nonneg (mul_nonneg (actualAppellEnergy_nonneg _ _ _) hq) hhk.le
  have hm := mul_le_mul_of_nonneg_left hl hw
  rw [actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f (by omega),
    actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f hk,
    dotProduct_add,dotProduct_add]
  nlinarith

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualAppell_weighted_drift_pairing_le
