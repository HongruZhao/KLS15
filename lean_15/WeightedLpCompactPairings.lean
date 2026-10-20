import TensorExteriorOperatorChain

/-! Exact density cancellation for genuine compact scalar tests and their
weighted derivatives. These identities use arbitrary weighted L² coefficients. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology LinearPMap
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {φ ψ : Space n → ℝ}

lemma finiteMatrixLp_inner_right {ι : Type*} [Fintype ι]
    (v : CenteredL2.Family (potentialMeasure φ) ι) (f : ι → Space n → ℝ)
    (hf : ∀ j, MemLp (f j) 2 (potentialMeasure φ)) :
    inner ℝ v (finiteMatrixLp f hf) = ∑ j, ∫ x, v j x * f j x ∂potentialMeasure φ := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hf j).coeFn_toLp] with x hx
  simp only [finiteMatrixLp, RCLike.inner_apply, conj_trivial, hx]
  ring

lemma integral_weightedCompactTest_mul (hφ : Continuous φ)
    (v : Lp ℝ 2 (potentialMeasure φ)) (c : ℝ) :
    (∫ x, v x * (c * (ψ x * Real.exp (φ x))) ∂potentialMeasure φ) =
      c * ∫ x, v x * ψ x := by
  rw [integral_potentialMeasure hφ.measurable]
  have he (x : Space n) : v x * (c * (ψ x * Real.exp (φ x))) * Real.exp (-φ x) =
      c * (v x * ψ x) := by
    calc
      _ = c*(v x*ψ x)*(Real.exp (φ x)*Real.exp (-φ x)) := by ring
      _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  simp_rw [he]
  exact integral_const_mul _ _

lemma coordinateDerivative_weightedCompactTest (hφ : ContDiff ℝ 1 φ)
    (hψ : ContDiff ℝ 1 ψ) (i : Fin n) (x : Space n) :
    coordinateDerivative (fun y => ψ y * Real.exp (φ y)) i x =
      Real.exp (φ x) * (coordinateDerivative ψ i x + ψ x * coordinateDerivative φ i x) := by
  have hh := weightedDerivativeTest_exp_mul hφ hψ i x
  dsimp only [weightedDerivativeTest] at hh
  linarith

lemma integral_weightedCompactTest_derivative (hφ : ContDiff ℝ 1 φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (v : Lp ℝ 2 (potentialMeasure φ)) (i : Fin n) :
    (∫ x, v x * coordinateDerivative (fun y => ψ y * Real.exp (φ y)) i x ∂potentialMeasure φ) =
      (∫ x, v x * coordinateDerivative ψ i x) +
      ∫ x, v x * coordinateDerivative φ i x * ψ x := by
  have hl := KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure (Lp.memLp v) hφ.continuous
  have hI : Integrable (fun x => v x * coordinateDerivative ψ i x) volume := by
    simpa only [smul_eq_mul] using hl.integrable_smul_right_of_hasCompactSupport
      (contDiff_coordinateDerivative hψ (m := 0) (by simp) i).continuous
      (hasCompactSupport_coordinateDerivative hc i)
  have hJ : Integrable (fun x => v x * coordinateDerivative φ i x * ψ x) volume := by
    have hh := hl.integrable_smul_right_of_hasCompactSupport
      ((contDiff_coordinateDerivative hφ (m := 0) (by simp) i).continuous.mul hψ.continuous) hc.mul_left
    simpa only [smul_eq_mul, Pi.mul_apply, mul_assoc] using hh
  rw [integral_potentialMeasure hφ.continuous.measurable, ← integral_add hI hJ]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [coordinateDerivative_weightedCompactTest hφ (hψ.of_le (by simp))]
    calc
      _ = (v x*coordinateDerivative ψ i x+v x*coordinateDerivative φ i x*ψ x)*
          (Real.exp (φ x)*Real.exp (-φ x)) := by ring
      _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.integral_weightedCompactTest_derivative
