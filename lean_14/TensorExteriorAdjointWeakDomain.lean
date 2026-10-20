import TensorProjectedAdjointTestPairing
import TensorHodgeWeakMatrixSums

/-! Identification of the actual Hilbert adjoint with the projected
ordinary distributional weighted divergence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology LinearPMap
namespace KLS.DeterministicBridgeIntegration
variable {n q : ℕ} {φ ψ : Space n → ℝ}

lemma tensorHodgeDrift_test_integrable (hφ : ContDiff ℝ 1 φ)
    {f : TensorTwoFormIndex n q → Space n → ℝ}
    (hf : ∀ z, MemLp (f z) 2 (potentialMeasure φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (a : TensorOneFormIndex n q) :
    Integrable (fun x => matrixZeroth (fun a => tensorHodgeDriftMatrix φ q (Sum.inr a)) f a x * ψ x) volume := by
  have hi (z : TensorTwoFormIndex n q) : Integrable
      (fun x => tensorHodgeDriftMatrix φ q (Sum.inr a) z x * f z x * ψ x) volume := by
    have hh := (KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure (hf z) hφ.continuous).integrable_smul_right_of_hasCompactSupport
        ((tensorHodgeDriftMatrix_continuous hφ q (Sum.inr a) z).mul hψ.continuous) hc.mul_left
    convert hh using 1
    funext x
    simp only [smul_eq_mul, Pi.mul_apply]
    ring
  simp only [matrixZeroth, Finset.sum_mul]
  exact integrable_finsetSum Finset.univ (fun z _ => hi z)

lemma tensorHodgeDrift_test_integral (hφ : ContDiff ℝ 1 φ)
    {f : TensorTwoFormIndex n q → Space n → ℝ}
    (hf : ∀ z, MemLp (f z) 2 (potentialMeasure φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (a : TensorOneFormIndex n q) :
    (∫ x, matrixZeroth (fun a => tensorHodgeDriftMatrix φ q (Sum.inr a)) f a x * ψ x) =
      Real.sqrt 2 * ∑ I, ∑ i, ∑ j, tensorOneFormProjectionMatrix a (I,j) *
        ∫ x, f (I,i,j) x * coordinateDerivative φ i x * ψ x := by
  have hi (z : TensorTwoFormIndex n q) : Integrable
      (fun x => tensorHodgeDriftMatrix φ q (Sum.inr a) z x * f z x * ψ x) volume := by
    have hh := (KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure (hf z) hφ.continuous).integrable_smul_right_of_hasCompactSupport
        ((tensorHodgeDriftMatrix_continuous hφ q (Sum.inr a) z).mul hψ.continuous) hc.mul_left
    convert hh using 1
    funext x
    simp only [smul_eq_mul, Pi.mul_apply]
    ring
  simp only [matrixZeroth, Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun z _ => hi z)]
  simp only [Fintype.sum_prod_type, tensorHodgeDriftMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : (fun x => Real.sqrt 2 * tensorOneFormProjectionMatrix a (I,j) *
      coordinateDerivative φ i x * f (I,i,j) x * ψ x) =
      fun x => (Real.sqrt 2 * tensorOneFormProjectionMatrix a (I,j)) *
        (f (I,i,j) x * coordinateDerivative φ i x * ψ x) := by funext x; ring
  rw [he, integral_const_mul]
  ring

/-- Every element of the true Hilbert adjoint domain satisfies the actual
projected weighted divergence equation against all ordinary compact C∞ tests. -/
theorem tensorExteriorOne_adjoint_hasWeakProjectedDivergence
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (w : (tensorExteriorOneOperator (hφ.of_le (by simp)) q).adjoint.domain) :
    HasWeakMatrixFirstOrder
      (fun a => tensorHodgeDerivativeMatrix n q (Sum.inr a))
      (fun a => tensorHodgeDriftMatrix φ q (Sum.inr a))
      (fun z x => (w : TensorTwoFormL2 φ q).val z x)
      (fun a x => ((tensorExteriorOneOperator (hφ.of_le (by simp)) q).adjoint w).val a x) := by
  intro ψ hψ hc a
  have hv : Integrable (fun x => ((tensorExteriorOneOperator (hφ.of_le (by simp)) q).adjoint w).val a x * ψ x)
      volume := by
    simpa only [smul_eq_mul] using
      (KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure
        (Lp.memLp (((tensorExteriorOneOperator (hφ.of_le (by simp)) q).adjoint w).val a)) hφ.continuous).integrable_smul_right_of_hasCompactSupport hψ.continuous hc
  have hd := tensorHodgeDrift_test_integrable (hφ.of_le (by simp))
    (fun z => Lp.memLp ((w : TensorTwoFormL2 φ q).val z)) hψ hc a
  have he : (fun x => (((tensorExteriorOneOperator (hφ.of_le (by simp)) q).adjoint w).val a x -
      matrixZeroth (fun a => tensorHodgeDriftMatrix φ q (Sum.inr a))
        (fun z x => (w : TensorTwoFormL2 φ q).val z x) a x) * ψ x) =
      (fun x => ((tensorExteriorOneOperator (hφ.of_le (by simp)) q).adjoint w).val a x * ψ x -
        matrixZeroth (fun a => tensorHodgeDriftMatrix φ q (Sum.inr a))
          (fun z x => (w : TensorTwoFormL2 φ q).val z x) a x * ψ x) := by funext x; ring
  rw [he, integral_sub hv hd, tensorExteriorOne_adjoint_distributional_pairing hφ w hψ hc a,
    tensorHodgeDrift_test_integral (hφ.of_le (by simp))
      (fun z => Lp.memLp ((w : TensorTwoFormL2 φ q).val z)) hψ hc a,
    tensorHodgeDerivativeMatrix_inr_sum]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorExteriorOne_adjoint_hasWeakProjectedDivergence
