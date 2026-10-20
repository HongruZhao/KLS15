import KLS.WeightedCompactSupport
import KLSConstantImprovement.SourceHookMainCharge

/-! Variable source hooks give actual null multipliers for compact scalar
Hessians. Their source derivative is retained in X*C-div(C); dropping it
would change the field. The potential is any finite C1 function, each
coefficient is C1, and the scalar test is C3 and compact. No numerical
projection charge or noncompact field domain is assumed or concluded. -/
noncomputable section
open MeasureTheory Finset KLS
open scoped BigOperators ContDiff
namespace KLSConstantImprovement.ActualVariableSourceHookNullPairing

def coordinateThird {n : ℕ} (u : KLS.Space n → ℝ) (x : KLS.Space n)
    (i j k : Fin n) : ℝ :=
  coordinateDerivative (fun y => coordinateHessian u y i j) k x

theorem coordinateThird_symmetric {n : ℕ} {u : KLS.Space n → ℝ}
    (hu : ContDiff ℝ 3 u) (x : KLS.Space n) :
    (∀ i j k, coordinateThird u x i j k = coordinateThird u x j i k) ∧
    (∀ i j k, coordinateThird u x i j k = coordinateThird u x i k j) := by
  have hswap (i j : Fin n) :
      (fun y => coordinateHessian u y i j) =
      (fun y => coordinateHessian u y j i) := by
    funext y
    exact ((coordinateHessian_symmetric (hu.of_le (by norm_num)) y).apply i j).symm
  constructor
  · intro i j k
    exact congrArg (fun f : KLS.Space n → ℝ => coordinateDerivative f k x) (hswap i j)
  · intro i j k
    have hdj : ContDiff ℝ 2 (coordinateDerivative u j) :=
      contDiff_coordinateDerivative hu (by norm_num) j
    have hdk : ContDiff ℝ 2 (coordinateDerivative u k) :=
      contDiff_coordinateDerivative hu (by norm_num) k
    calc
      _ = coordinateHessian (coordinateDerivative u j) x k i := rfl
      _ = coordinateHessian (coordinateDerivative u j) x i k :=
        ((coordinateHessian_symmetric hdj x).apply k i).symm
      _ = coordinateDerivative (fun y => coordinateHessian u y k j) i x := rfl
      _ = coordinateDerivative (fun y => coordinateHessian u y j k) i x :=
        congrArg (fun f : KLS.Space n → ℝ => coordinateDerivative f i x) (hswap k j)
      _ = coordinateHessian (coordinateDerivative u k) x i j := rfl
      _ = coordinateHessian (coordinateDerivative u k) x j i :=
        ((coordinateHessian_symmetric hdk x).apply i j).symm
      _ = _ := rfl

/-- The differentiated multiplier stays in the exact weighted IBP identity. -/
theorem compact_variable_score_hessian_ibp {n : ℕ} {φ u c : KLS.Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hu : ContDiff ℝ 3 u)
    (hc : HasCompactSupport u) (hcoef : ContDiff ℝ 1 c)
    (i j k : Fin n) :
    (∫ x, (c x * coordinateDerivative φ k x - coordinateDerivative c k x) *
      coordinateHessian u x i j ∂potentialMeasure φ) =
    ∫ x, c x * coordinateThird u x i j k ∂potentialMeasure φ := by
  have hg : ContDiff ℝ 1 (fun x => coordinateHessian u x i j) :=
    contDiff_coordinateHessian hu (by norm_num) i j
  have hgc := hasCompactSupport_coordinateHessian hc i j
  have hdg : Continuous (fun x => coordinateThird u x i j k) :=
    (contDiff_coordinateDerivative hg (m := 0) (by norm_num) k).continuous
  have hdc : Continuous (coordinateDerivative c k) :=
    (contDiff_coordinateDerivative hcoef (m := 0) (by norm_num) k).continuous
  have hdφ : Continuous (coordinateDerivative φ k) :=
    (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) k).continuous
  have hfg : Integrable (fun x => c x * coordinateHessian u x i j)
      (potentialMeasure φ) := by
    have hactual := integrable_potentialMeasure_of_continuous_hasCompactSupport
      hφ.continuous (hcoef.continuous.mul hg.continuous) hgc.mul_left
    change Integrable (fun x => c x * coordinateHessian u x i j) (potentialMeasure φ) at hactual
    exact hactual
  have hdfg : Integrable (fun x => coordinateDerivative c k x * coordinateHessian u x i j)
      (potentialMeasure φ) := by
    have hactual := integrable_potentialMeasure_of_continuous_hasCompactSupport
      hφ.continuous (hdc.mul hg.continuous) hgc.mul_left
    change Integrable (fun x => coordinateDerivative c k x * coordinateHessian u x i j)
      (potentialMeasure φ) at hactual
    exact hactual
  have hfdg : Integrable (fun x => c x * coordinateThird u x i j k)
      (potentialMeasure φ) := by
    have hactual := integrable_potentialMeasure_of_continuous_hasCompactSupport
      hφ.continuous (hcoef.continuous.mul hdg)
      (hasCompactSupport_coordinateDerivative hgc k).mul_left
    change Integrable (fun x => c x * coordinateThird u x i j k) (potentialMeasure φ) at hactual
    exact hactual
  have hfgdφ : Integrable (fun x => c x * coordinateHessian u x i j * coordinateDerivative φ k x)
      (potentialMeasure φ) := by
    have hactual := integrable_potentialMeasure_of_continuous_hasCompactSupport
      hφ.continuous ((hcoef.continuous.mul hg.continuous).mul hdφ) hgc.mul_left.mul_right
    change Integrable (fun x => c x * coordinateHessian u x i j * coordinateDerivative φ k x)
      (potentialMeasure φ) at hactual
    exact hactual
  have h := integral_mul_fderiv_potentialMeasure
    (f := c) (g := fun x => coordinateHessian u x i j)
    (hφ.differentiable (by norm_num)) (hcoef.differentiable (by norm_num))
    (hg.differentiable (by norm_num)) (EuclideanSpace.single k 1)
    hfg
    (by simpa only [coordinateDerivative] using hdfg)
    (by simpa only [coordinateDerivative, coordinateThird] using hfdg)
    (by simpa only [coordinateDerivative] using hfgdφ)
  calc
    _ = (∫ x, c x * coordinateHessian u x i j * coordinateDerivative φ k x
          ∂potentialMeasure φ) -
        ∫ x, coordinateDerivative c k x * coordinateHessian u x i j
          ∂potentialMeasure φ := by
      calc
        _ = ∫ x, c x * coordinateHessian u x i j * coordinateDerivative φ k x -
            coordinateDerivative c k x * coordinateHessian u x i j ∂potentialMeasure φ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by ring
        _ = _ := integral_sub hfgdφ hdfg
    _ = _ := by
      simpa only [coordinateDerivative, coordinateThird] using h.symm

/-- Every pointwise zero-symmetrization tensor field supplies an actual
scalar-Hessian null field, with its derivative term included. -/
theorem compact_variable_source_hook_null_pairing {n : ℕ} {φ u : KLS.Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hu : ContDiff ℝ 3 u)
    (hc : HasCompactSupport u)
    (C : Fin n → Fin n → Fin n → KLS.Space n → ℝ)
    (hC : ∀ i j k, ContDiff ℝ 1 (C i j k))
    (hHook : ∀ x i j k, C i j k x + C j i k x + C k i j x = 0) :
    (∫ x, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (C i j k x * coordinateDerivative φ k x - coordinateDerivative (C i j k) k x) *
      coordinateHessian u x i j ∂potentialMeasure φ) = 0 := by
  have hi (i j k : Fin n) : Integrable (fun x =>
      (C i j k x * coordinateDerivative φ k x - coordinateDerivative (C i j k) k x) *
      coordinateHessian u x i j) (potentialMeasure φ) := by
    have hscore : Continuous (coordinateDerivative φ k) :=
      (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) k).continuous
    have hdC : Continuous (coordinateDerivative (C i j k) k) :=
      (contDiff_coordinateDerivative (hC i j k) (m := 0) (by norm_num) k).continuous
    have hH : Continuous (fun x => coordinateHessian u x i j) :=
      (contDiff_coordinateHessian hu (m := 0) (by norm_num) i j).continuous
    exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((((hC i j k).continuous.mul hscore).sub hdC).mul hH)
      (hasCompactSupport_coordinateHessian hc i j).mul_left
  have hthird (i j k : Fin n) : Integrable (fun x =>
      C i j k x * coordinateThird u x i j k) (potentialMeasure φ) := by
    have hH : ContDiff ℝ 1 (fun x => coordinateHessian u x i j) :=
      contDiff_coordinateHessian hu (by norm_num) i j
    have hdH : Continuous (fun x => coordinateThird u x i j k) :=
      (contDiff_coordinateDerivative hH (m := 0) (by norm_num) k).continuous
    exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hC i j k).continuous.mul hdH)
      (hasCompactSupport_coordinateDerivative
        (hasCompactSupport_coordinateHessian hc i j) k).mul_left
  have hsum :
      (∫ x, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (C i j k x * coordinateDerivative φ k x - coordinateDerivative (C i j k) k x) *
        coordinateHessian u x i j ∂potentialMeasure φ) =
      ∫ x, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        C i j k x * coordinateThird u x i j k ∂potentialMeasure φ := by
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun k _ => hi i j k)))]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun k _ => hthird i j k)))]
    apply Finset.sum_congr rfl
    intro i h_i
    rw [integral_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun k _ => hi i j k))]
    rw [integral_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun k _ => hthird i j k))]
    apply Finset.sum_congr rfl
    intro j h_j
    rw [integral_finsetSum Finset.univ (fun k _ => hi i j k)]
    rw [integral_finsetSum Finset.univ (fun k _ => hthird i j k)]
    apply Finset.sum_congr rfl
    intro k h_k
    exact compact_variable_score_hessian_ibp hφ hu hc (hC i j k) i j k
  rw [hsum]
  have hzero : (fun x => ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      C i j k x * coordinateThird u x i j k) = fun _ => (0:ℝ) := by
    funext x
    have hs := coordinateThird_symmetric hu x
    exact KLSConstantImprovement.SourceHookMainCharge.constant_hook_third_pair_zero
      (fun i j k => C i j k x) (coordinateThird u x) (hHook x) hs.1 hs.2
  rw [hzero, integral_zero]

end KLSConstantImprovement.ActualVariableSourceHookNullPairing
#print axioms KLSConstantImprovement.ActualVariableSourceHookNullPairing.coordinateThird_symmetric
#print axioms KLSConstantImprovement.ActualVariableSourceHookNullPairing.compact_variable_score_hessian_ibp
#print axioms KLSConstantImprovement.ActualVariableSourceHookNullPairing.compact_variable_source_hook_null_pairing
