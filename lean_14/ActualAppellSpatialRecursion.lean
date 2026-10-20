import CanonicalAppellPolynomials
import KLS.WeightedEigenClassical

/-! The genuine adjoint Appell polynomials satisfy the literal spatial
derivative recursion. It is proved from weighted compact-test integration by
parts and the actual tilt identity, rather than assumed as a formal sequence. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ}
variable [IsProbabilityMeasure (potentialMeasure φ)]

def basisAppellDerivativePolynomial (hμ : admissibleMeasure (potentialMeasure φ))
    (d : ℕ) (a : Fin (d+1) → Fin n) (j : Fin n) : MvPolynomial (Fin n) ℝ :=
  ∑ k : Fin (d+1), (if a k=j then (1 : ℝ) else 0) •
    actualBasisAppellPolynomial hμ d (fun l => a (k.succAbove l))

theorem basisAppellDerivativePolynomial_eval (hμ : admissibleMeasure (potentialMeasure φ))
    (d : ℕ) (a : Fin (d+1) → Fin n) (j : Fin n) (x : Space n) :
    polynomialEval (basisAppellDerivativePolynomial hμ d a j) x =
      ∑ k : Fin (d+1), (if a k=j then (1 : ℝ) else 0) *
        polynomialEval (actualBasisAppellPolynomial hμ d (fun l => a (k.succAbove l))) x := by
  change (MvPolynomial.eval (fun l => x l)) (∑ k : Fin (d+1),
      (if a k=j then (1 : ℝ) else 0) •
        actualBasisAppellPolynomial hμ d (fun l => a (k.succAbove l))) = _
  rw [MvPolynomial.eval_sum]
  simp only [MvPolynomial.smul_eval]
  rfl

theorem basisAppellDerivativePolynomial_pairing
    (hμ : admissibleMeasure (potentialMeasure φ))
    (d : ℕ) (a : Fin (d+1) → Fin n) (j : Fin n)
    {ψ : Space n → ℝ} (hψ : MemLp ψ 2 (potentialMeasure φ)) :
    (∫ x, polynomialEval (basisAppellDerivativePolynomial hμ d a j) x*ψ x
      ∂potentialMeasure φ) =
      ∑ k : Fin (d+1), (if a k=j then (1 : ℝ) else 0) *
        actualAppellCoefficient (potentialMeasure φ) ψ d (fun l => a (k.succAbove l)) := by
  have hI (k : Fin (d+1)) : Integrable (fun x =>
      (if a k=j then (1 : ℝ) else 0) *
        (polynomialEval (actualBasisAppellPolynomial hμ d (fun l => a (k.succAbove l))) x*ψ x))
      (potentialMeasure φ) := by
    have hi := (polynomialEval_memLp_two hμ.logConcave
      (actualBasisAppellPolynomial hμ d (fun l => a (k.succAbove l)))).integrable_mul hψ
    exact hi.const_mul (if a k=j then (1 : ℝ) else 0)
  simp_rw [basisAppellDerivativePolynomial_eval,Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum Finset.univ (fun k _ => hI k)]
  simp_rw [integral_const_mul,actualBasisAppellPolynomial_pairing hμ d _ hψ]

theorem actualBasisAppellPolynomial_pderiv {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hμ : admissibleMeasure (potentialMeasure φ))
    (d : ℕ) (a : Fin (d+1) → Fin n) (j : Fin n) :
    MvPolynomial.pderiv j (actualBasisAppellPolynomial hμ (d+1) a) =
      basisAppellDerivativePolynomial hμ d a j := by
  let p := actualBasisAppellPolynomial hμ (d+1) a
  let q := basisAppellDerivativePolynomial hμ d a j
  have hae : polynomialEval (MvPolynomial.pderiv j p) =ᵐ[potentialMeasure φ]
      polynomialEval q := by
    apply ae_eq_of_integral_contDiff_smul_eq
      (polynomialEval_continuous _).locallyIntegrable
      (polynomialEval_continuous _).locallyIntegrable
    intro ψ hψ hc
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have hψ2 := memLp_of_continuous_hasCompactSupport hφ.continuous hψ.continuous hc
    have hD := memLp_weightedDerivativeTest (hφ.of_le (by norm_num)) hψ1 hc j
    have hi := integral_coordinateDerivative_mul_compact_test (hφ.of_le (by norm_num))
      ((polynomialEval_contDiff p).of_le (by simp)) hψ1 hc j
    have hs := actualAppellCoefficient_weightedDerivativeTest hφ hκ hlower hψ1 hc j d a
    have hp := actualBasisAppellPolynomial_pairing hμ (d+1) a hD.neg
    have hq := basisAppellDerivativePolynomial_pairing hμ d a j hψ2
    have hneg : (∫ x, polynomialEval p x*(-weightedDerivativeTest φ ψ j x)
        ∂potentialMeasure φ) =
        -(∫ x, polynomialEval p x*weightedDerivativeTest φ ψ j x ∂potentialMeasure φ) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only; ring
    simp_rw [coordinateDerivative_polynomialEval] at hi
    have he : (∫ x, polynomialEval (MvPolynomial.pderiv j p) x*ψ x
        ∂potentialMeasure φ) = ∫ x, polynomialEval q x*ψ x ∂potentialMeasure φ := by
      calc
        _ = ∫ x, polynomialEval p x*(-weightedDerivativeTest φ ψ j x)
            ∂potentialMeasure φ := hi.trans hneg.symm
        _ = _ := hp.trans (hs.trans hq.symm)
    simpa only [smul_eq_mul,mul_comm] using he
  have hz : polynomialEval (MvPolynomial.pderiv j p-q) =ᵐ[potentialMeasure φ] 0 := by
    filter_upwards [hae] with x hx
    change (MvPolynomial.eval (fun l => x l)) (MvPolynomial.pderiv j p-q)=0
    calc
      _ = (MvPolynomial.eval (fun l => x l)) (MvPolynomial.pderiv j p)-
          (MvPolynomial.eval (fun l => x l)) q :=
        MvPolynomial.eval_sub (MvPolynomial.pderiv j p) (fun l => x l)
      _ = 0 := sub_eq_zero.mpr hx
  exact sub_eq_zero.mp (polynomial_eq_zero_of_ae_eval_zero hμ _ hz)

theorem actualBasisAppellPolynomial_spatial_recursion {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hμ : admissibleMeasure (potentialMeasure φ))
    (d : ℕ) (a : Fin (d+1) → Fin n) (j : Fin n) (x : Space n) :
    coordinateDerivative (polynomialEval (actualBasisAppellPolynomial hμ (d+1) a)) j x =
      ∑ k : Fin (d+1), (if a k=j then (1 : ℝ) else 0) *
        polynomialEval (actualBasisAppellPolynomial hμ d (fun l => a (k.succAbove l))) x := by
  rw [coordinateDerivative_polynomialEval,
    actualBasisAppellPolynomial_pderiv hφ hκ hlower hμ,basisAppellDerivativePolynomial_eval]

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualBasisAppellPolynomial_pderiv
#print axioms KLS.DeterministicBridgeNext.actualBasisAppellPolynomial_spatial_recursion
