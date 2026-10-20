import ActualWeightedAppellHeat
import CanonicalAppellPolynomials
import KLS.ProbabilityMeanCentering

/-! Literal mean subtraction preserves all positive Appell coefficients.
The actual weighted maximum consequently controls the true variance. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration KLS.TensorEnergy
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem actualAppellCoefficient_sub_const (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (c : ℝ) {d : ℕ} (hd : d ≠ 0)
    (a : Fin d → Fin n) :
    actualAppellCoefficient μ (fun x => f x-c) d a=actualAppellCoefficient μ f d a := by
  rw [actualAppellCoefficient_sub hLC hf (memLp_const c),
    actualAppellCoefficient_const_fullClass hLC c hd,sub_zero]

theorem actualWeightedAppellEnergy_sub_const (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (c K : ℝ) (N : ℕ) :
    actualWeightedAppellEnergy μ (fun x => f x-c) K N=
      actualWeightedAppellEnergy μ f K N := by
  unfold actualWeightedAppellEnergy
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  unfold actualAppellEnergy
  apply Finset.sum_congr rfl
  intro a ha
  rw [actualAppellCoefficient_sub_const hLC hf c (by have := (Finset.mem_Icc.mp hd).1; omega)]

theorem actualCovarianceAppellEnergy_sub_const (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (c : ℝ) {d : ℕ} (hd : d ≠ 0) :
    actualCovarianceAppellEnergy μ (fun x => f x-c) d=
      actualCovarianceAppellEnergy μ f d := by
  unfold actualCovarianceAppellEnergy
  congr 1
  funext a
  exact actualAppellCoefficient_sub_const hLC hf c hd a

theorem actualAppellCoefficient_zero_eq_mean (f : Space n → ℝ)
    (a : Fin 0 → Fin n) : actualAppellCoefficient μ f 0 a=∫ x,f x ∂μ := by
  simp [actualAppellCoefficient,iteratedFDeriv_zero_apply,exponentialTilt_zero]

theorem actualCovarianceAppellEnergy_zero_eq_mean_sq (f : Space n → ℝ) :
    actualCovarianceAppellEnergy μ f 0=(∫ x,f x ∂μ)^2 := by
  classical
  simp [actualCovarianceAppellEnergy,tensorMetric,tensorMatrix,tensorMatrixFamily,Matrix.mulVec,
    dotProduct,actualAppellCoefficient_zero_eq_mean,pow_two]

theorem actualWeightedAppellPairing_oneLp (hLC : measureLogConcave μ)
    (f : Lp ℝ 2 μ) (K : ℝ) (N : ℕ) :
    actualWeightedAppellPairing f (CenteredL2.oneLp μ) K N=0 := by
  classical
  unfold actualWeightedAppellPairing
  apply Finset.sum_eq_zero
  intro d hd
  have he : fullClassAppellTensor d (CenteredL2.oneLp μ)=0 := by
    apply PiLp.ext
    intro a
    change actualAppellCoefficient μ (CenteredL2.oneLp μ) d a=0
    rw [actualAppellCoefficient_congr_ae (CenteredL2.oneLp_ae μ)]
    exact actualAppellCoefficient_const_fullClass hLC 1
      (by have := (Finset.mem_Icc.mp hd).1; omega) a
  rw [he,inner_zero_right,mul_zero]

theorem actual_weighted_maximum_mean_zero (hLC : measureLogConcave μ)
    (f : Lp ℝ 2 μ) {K M : ℝ} {N : ℕ} (hM : 0<M)
    (hstat : ∀ ell : Lp ℝ 2 μ,actualWeightedAppellPairing f ell K N=M*inner ℝ f ell) :
    (∫ x,f x ∂μ)=0 := by
  have hs := hstat (CenteredL2.oneLp μ)
  rw [actualWeightedAppellPairing_oneLp hLC,real_inner_comm,
    CenteredL2.inner_oneLp] at hs
  exact (mul_eq_zero.mp hs.symm).resolve_left (ne_of_gt hM)

theorem actual_weighted_global_variance_bound (hLC : measureLogConcave μ)
    {K M : ℝ} {N : ℕ}
    (hglobal : ∀ g : Lp ℝ 2 μ,actualWeightedAppellEnergy μ g K N ≤ M*‖g‖^2)
    (f : Lp ℝ 2 μ) :
    actualWeightedAppellEnergy μ f K N ≤ M*(‖f‖^2-(∫ x,f x ∂μ)^2) := by
  have he : actualWeightedAppellEnergy μ (CenteredL2.center μ f) K N=
      actualWeightedAppellEnergy μ f K N := by
    rw [actualWeightedAppellEnergy_congr_ae (CenteredL2.center_ae μ f)]
    exact actualWeightedAppellEnergy_sub_const hLC (Lp.memLp f) _ K N
  have hb := hglobal (CenteredL2.center μ f)
  rw [he,CenteredL2.norm_center_sq] at hb
  exact hb

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualWeightedAppellEnergy_sub_const
#print axioms KLS.DeterministicBridgeNext.actualCovarianceAppellEnergy_zero_eq_mean_sq
#print axioms KLS.DeterministicBridgeNext.actual_weighted_maximum_mean_zero
#print axioms KLS.DeterministicBridgeNext.actual_weighted_global_variance_bound
