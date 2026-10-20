import KLSConstantImprovement.ActualSourceSkewGradientCancellation
import KLSConstantImprovement.SourceHookMainCharge

/-! Actual compact-source binding for the constant-hook null correction.
The score is grad(phi) under exp(-phi)dy and the scalar test is C3 and
compact. Coordinate IBP and integral third-order symmetry are proved from
these actual functions. No moment-map, response, graph-range or numerical
budget premise is substituted. Natural noncompact limits stay separate. -/
noncomputable section
open MeasureTheory Finset KLS
open scoped BigOperators ContDiff
namespace KLSConstantImprovement.ActualSourceHookNullPairing
open KLSConstantImprovement.ActualSourceSkewGradientCancellation

def sourceScoreHessianPair {n : ℕ} (φ u : KLS.Space n → ℝ)
    (i j k : Fin n) : ℝ :=
  ∫ x, coordinateDerivative φ i x * coordinateHessian u x j k
    ∂potentialMeasure φ

theorem compact_source_score_hessian_pair {n : ℕ} {φ u : KLS.Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hu : ContDiff ℝ 3 u)
    (hc : HasCompactSupport u) (i j k : Fin n) :
    sourceScoreHessianPair φ u i j k =
      ∫ x, coordinateHessian (coordinateDerivative u k) x i j
        ∂potentialMeasure φ := by
  have hdk : ContDiff ℝ 2 (coordinateDerivative u k) :=
    contDiff_coordinateDerivative hu (by norm_num) k
  have h := source_score_gradient_coordinate hφ hdk
    (hasCompactSupport_coordinateDerivative hc k) j i
  simpa only [sourceScoreHessianPair, coordinateHessian,
    coordinateDerivative] using h

theorem compact_source_score_hessian_symmetric {n : ℕ} {φ u : KLS.Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hu : ContDiff ℝ 3 u)
    (hc : HasCompactSupport u) :
    (∀ i j k, sourceScoreHessianPair φ u i j k =
      sourceScoreHessianPair φ u j i k) ∧
    (∀ i j k, sourceScoreHessianPair φ u i j k =
      sourceScoreHessianPair φ u i k j) := by
  constructor
  · intro i j k
    have hdk : ContDiff ℝ 2 (coordinateDerivative u k) :=
      contDiff_coordinateDerivative hu (by norm_num) k
    calc
      _ = ∫ x, coordinateHessian (coordinateDerivative u k) x i j
          ∂potentialMeasure φ := compact_source_score_hessian_pair hφ hu hc i j k
      _ = ∫ x, coordinateHessian (coordinateDerivative u k) x j i
          ∂potentialMeasure φ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x =>
          ((coordinateHessian_symmetric hdk x).apply i j).symm
      _ = _ := (compact_source_score_hessian_pair hφ hu hc j i k).symm
  · intro i j k
    unfold sourceScoreHessianPair
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change coordinateDerivative φ i x * coordinateHessian u x j k =
        coordinateDerivative φ i x * coordinateHessian u x k j
      exact congrArg (fun v : ℝ => coordinateDerivative φ i x * v)
        (((coordinateHessian_symmetric (hu.of_le (by norm_num)) x).apply j k).symm)

/-- This is the actual source integral <C_X,Hess u>=0 for every constant
zero-symmetrization tensor C and compact scalar test u. -/
theorem compact_source_hook_null_pairing {n : ℕ} {φ u : KLS.Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hu : ContDiff ℝ 3 u)
    (hc : HasCompactSupport u)
    (C : Fin n → Fin n → Fin n → ℝ)
    (hHook : ∀ i j k, C i j k + C j i k + C k i j = 0) :
    (∫ x, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      C i j k * coordinateDerivative φ k x * coordinateHessian u x i j
      ∂potentialMeasure φ) = 0 := by
  have hdφ (k : Fin n) : Continuous (coordinateDerivative φ k) :=
    (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) k).continuous
  have hHu (i j : Fin n) : Continuous (fun x => coordinateHessian u x i j) :=
    (contDiff_coordinateHessian hu (m := 0) (by norm_num) i j).continuous
  have hi (i j k : Fin n) : Integrable (fun x =>
      C i j k * coordinateDerivative φ k x * coordinateHessian u x i j)
      (potentialMeasure φ) := by
    simpa only [mul_assoc, Pi.mul_apply] using
      (integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
        ((hdφ k).mul (hHu i j))
        (hasCompactSupport_coordinateHessian hc i j).mul_left).const_mul (C i j k)
  have hfinite :
      (∫ x, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        C i j k * coordinateDerivative φ k x * coordinateHessian u x i j
        ∂potentialMeasure φ) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        C i j k * sourceScoreHessianPair φ u k i j := by
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun k _ => hi i j k)))]
    apply Finset.sum_congr rfl
    intro i h_i
    rw [integral_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun k _ => hi i j k))]
    apply Finset.sum_congr rfl
    intro j h_j
    rw [integral_finsetSum Finset.univ (fun k _ => hi i j k)]
    apply Finset.sum_congr rfl
    intro k h_k
    have heq : (fun x => C i j k * coordinateDerivative φ k x * coordinateHessian u x i j) =
        (fun x => C i j k * (coordinateDerivative φ k x * coordinateHessian u x i j)) := by
      funext x
      ring
    rw [heq, integral_const_mul]
    rfl
  rw [hfinite]
  have hs := compact_source_score_hessian_symmetric hφ hu hc
  apply KLSConstantImprovement.SourceHookMainCharge.constant_hook_third_pair_zero
    C (fun i j k => sourceScoreHessianPair φ u k i j) hHook
  · intro i j k
    exact hs.2 k i j
  · intro i j k
    calc
      _ = sourceScoreHessianPair φ u i k j := hs.1 k i j
      _ = sourceScoreHessianPair φ u i j k := hs.2 i k j
      _ = _ := hs.1 i j k

end KLSConstantImprovement.ActualSourceHookNullPairing
#print axioms KLSConstantImprovement.ActualSourceHookNullPairing.compact_source_score_hessian_pair
#print axioms KLSConstantImprovement.ActualSourceHookNullPairing.compact_source_score_hessian_symmetric
#print axioms KLSConstantImprovement.ActualSourceHookNullPairing.compact_source_hook_null_pairing
