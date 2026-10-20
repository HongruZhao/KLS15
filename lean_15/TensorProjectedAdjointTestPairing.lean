import TensorProjectedAdjointTests
import TensorAdjointFinitePairing

/-! Density-cancelled ordinary distributional pairing for the literal
weighted Hilbert adjoint. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology LinearPMap
namespace KLS.DeterministicBridgeIntegration
variable {n q : ℕ} {φ ψ : Space n → ℝ}

lemma tensorProjectedCompactTest_coordinateDerivative
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (a b : TensorOneFormIndex n q) (i : Fin n) (x : Space n) :
    coordinateDerivative (tensorProjectedCompactTest a ψ φ b) i x =
      tensorOneFormProjectionMatrix b a *
        coordinateDerivative (fun y => ψ y * Real.exp (φ y)) i x := by
  exact coordinateDerivative_smul ((hψ.mul hφ.exp).differentiable (by simp) x) _ i

lemma tensorProjectedCompactTest_differential_integral
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (a : TensorOneFormIndex n q)
    (v : Lp ℝ 2 (potentialMeasure φ)) (I : OrderedTensorIndex n q) (i j : Fin n) :
    (∫ x, v x * tensorExteriorOneDifferential (tensorProjectedCompactTest a ψ φ) (I,i,j) x
      ∂potentialMeasure φ) = (1 / Real.sqrt 2) *
      (tensorOneFormProjectionMatrix (I,j) a *
        ((∫ x, v x * coordinateDerivative ψ i x) + ∫ x, v x * coordinateDerivative φ i x * ψ x) -
       tensorOneFormProjectionMatrix (I,i) a *
        ((∫ x, v x * coordinateDerivative ψ j x) + ∫ x, v x * coordinateDerivative φ j x * ψ x)) := by
  let θ := fun x => ψ x * Real.exp (φ x)
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := hψ.mul hφ.exp
  have hθc : HasCompactSupport θ := hc.mul_right
  have hint (l : Fin n) : Integrable (fun x => v x * coordinateDerivative θ l x) (potentialMeasure φ) :=
    (Lp.memLp v).integrable_mul (memLp_of_continuous_hasCompactSupport hφ.continuous
      (contDiff_coordinateDerivative hθ (m := 0) (by simp) l).continuous
      (hasCompactSupport_coordinateDerivative hθc l))
  have he : (fun x => v x * tensorExteriorOneDifferential (tensorProjectedCompactTest a ψ φ) (I,i,j) x) =
      fun x => (1 / Real.sqrt 2) *
        (tensorOneFormProjectionMatrix (I,j) a * (v x * coordinateDerivative θ i x) -
         tensorOneFormProjectionMatrix (I,i) a * (v x * coordinateDerivative θ j x)) := by
    funext x
    dsimp only [tensorExteriorOneDifferential]
    rw [tensorProjectedCompactTest_coordinateDerivative hφ hψ,
      tensorProjectedCompactTest_coordinateDerivative hφ hψ]
    dsimp only [θ]
    ring
  rw [he, integral_const_mul,
    integral_sub ((hint i).const_mul _) ((hint j).const_mul _), integral_const_mul, integral_const_mul]
  rw [integral_weightedCompactTest_derivative (hφ.of_le (by simp)) hψ hc,
    integral_weightedCompactTest_derivative (hφ.of_le (by simp)) hψ hc]

lemma tensorTwoFormL2_integral_skew (w : TensorTwoFormL2 φ q) (hφ : Continuous φ)
    (I : OrderedTensorIndex n q) (i j : Fin n) (η : Space n → ℝ) :
    (∫ x, w.val (I,j,i) x * η x) = -(∫ x, w.val (I,i,j) x * η x) := by
  have hm : finiteMatrixLp (fun z x => w.val z x) (fun z => Lp.memLp (w.val z)) ∈
      tensorTwoFormL2Subspace φ q := by rw [finiteMatrixLp_coe_eq]; exact w.property
  have hs := (finiteMatrixLp_mem_twoForm_iff (fun z => Lp.memLp (w.val z))).mp hm
  have he : (fun x => w.val (I,j,i) x * η x) =ᵐ[volume]
      (fun x => -(w.val (I,i,j) x * η x)) := by
    have hsk : (fun x => w.val (I,j,i) x) =ᵐ[potentialMeasure φ]
        (fun x => -w.val (I,i,j) x) := hs.mono (fun x hx => hx.2.1 I j i)
    filter_upwards [(volume_absolutelyContinuous_potentialMeasure hφ).ae_eq hsk] with x hx
    rw [hx]
    ring
  rw [integral_congr_ae he, integral_neg]

theorem tensorExteriorOne_adjoint_distributional_pairing
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (w : (tensorExteriorOneOperator (hφ.of_le (by simp)) q).adjoint.domain)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (a : TensorOneFormIndex n q) :
    (∫ x, ((tensorExteriorOneOperator (hφ.of_le (by simp)) q).adjoint w).val a x * ψ x) =
      Real.sqrt 2 * ∑ I, ∑ i, ∑ j, tensorOneFormProjectionMatrix a (I,j) *
        ((∫ x, (w : TensorTwoFormL2 φ q).val (I,i,j) x * coordinateDerivative ψ i x) +
         ∫ x, (w : TensorTwoFormL2 φ q).val (I,i,j) x * coordinateDerivative φ i x * ψ x) := by
  have hp := tensorExteriorOne_adjoint_compact_pairing (hφ.of_le (by simp)) w
    (tensorProjectedCompactTest a ψ φ) (tensorProjectedCompactTest_contDiff hφ hψ a)
    (tensorProjectedCompactTest_compact hc a) (tensorProjectedCompactTest_fiber a)
  rw [tensorProjectedCompactTest_inner hφ.continuous hψ.continuous hc a,
    finiteMatrixLp_inner_right] at hp
  simp only [Fintype.sum_prod_type] at hp
  simp_rw [tensorProjectedCompactTest_differential_integral hφ hψ hc a] at hp
  let t : TensorTwoFormIndex n q → Fin n → ℝ := fun z i =>
    (∫ x, (w : TensorTwoFormL2 φ q).val z x * coordinateDerivative ψ i x) +
    ∫ x, (w : TensorTwoFormL2 φ q).val z x * coordinateDerivative φ i x * ψ x
  have ht (I : OrderedTensorIndex n q) (i j k : Fin n) : t (I,j,i) k = -t (I,i,j) k := by
    dsimp only [t]
    rw [tensorTwoFormL2_integral_skew _ hφ.continuous I i j (coordinateDerivative ψ k),
      show (∫ x, (w : TensorTwoFormL2 φ q).val (I,j,i) x * coordinateDerivative φ k x * ψ x) =
        -(∫ x, (w : TensorTwoFormL2 φ q).val (I,i,j) x * coordinateDerivative φ k x * ψ x) by
          simpa only [mul_assoc] using tensorTwoFormL2_integral_skew
            (w : TensorTwoFormL2 φ q) hφ.continuous I i j
              (fun x => coordinateDerivative φ k x * ψ x)]
    ring
  exact hp.trans (tensorExterior_adjoint_pair_sum t ht a)

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorExteriorOne_adjoint_distributional_pairing
