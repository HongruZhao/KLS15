import KLS.WhitenedFamilyMoments
import KLS.RegularMomentMapQuadratic
import KLS.PositiveMatrixPerturbation

/-! Genuine whitening continuity from exactly the first and second coordinate
moments.  No convergence premise for every unbounded continuous function is
used.  Higher finite moments may be supplied individually. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology ENNReal BigOperators
namespace KLSConstantImprovement.ActualSecondMomentWhitening405
open KLS
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
variable {ν : ℕ → Measure (Space n)} [∀ k, IsProbabilityMeasure (ν k)]
variable (hν : ∀ k, measureLogConcave (ν k))
variable (hfirst : ∀ i : Fin n, Tendsto (fun k => ∫ x : Space n, x i ∂ν k) atTop (𝓝 0))
variable (hsecond : ∀ i j : Fin n, Tendsto (fun k => ∫ x : Space n, x i*x j ∂ν k)
  atTop (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) i j)))
include hμ hν hfirst hsecond

theorem covarianceMatrix_tendsto_one :
    Tendsto (fun k => covarianceMatrix (ν k)) atTop
      (𝓝 (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hc (k : ℕ) (a : Fin n) : MemLp (fun x : Space n => x a) 2 (ν k) :=
    (EuclideanSpace.proj (𝕜 := ℝ) a).comp_memLp' ((hν k).memLp_id)
  have heq (k : ℕ) : covarianceMatrix (ν k) i j =
      (∫ x : Space n, x i * x j ∂ν k) -
        (∫ x : Space n, x i ∂ν k) * (∫ x : Space n, x j ∂ν k) := by
    rw [covarianceMatrix_apply ((hν k).memLp_id), covariance_eq_sub (hc k i) (hc k j)]
    rfl
  simpa only [← heq, zero_mul, sub_zero] using
    (hsecond i j).sub ((hfirst i).mul (hfirst j))

theorem whiteningMatrix_tendsto_one :
    Tendsto (fun k => inverseSqrtMatrix (covarianceMatrix (ν k))) atTop
      (𝓝 (1 : Matrix (Fin n) (Fin n) ℝ)) :=
  tendsto_inverseSqrtMatrix_one (covarianceMatrix_tendsto_one hμ hν hfirst hsecond)
    (Eventually.of_forall fun k => covarianceMatrix_posSemidef (ν k))

theorem eventually_covarianceMatrix_posDef :
    ∀ᶠ k in atTop, (covarianceMatrix (ν k)).PosDef :=
  eventually_posDef_of_tendsto_one (covarianceMatrix_tendsto_one hμ hν hfirst hsecond)
    (Eventually.of_forall fun _ => covarianceMatrix_posSemidef _)

theorem whiteningCoefficient_tendsto (i : Fin n) (j : Option (Fin n)) :
    Tendsto (fun k =>
      let Q := inverseSqrtMatrix (covarianceMatrix (ν k))
      affineCoordinateCoefficient Q (-matrixAction Q (∫ x, x ∂ν k)) i j)
      atTop (𝓝 (affineCoordinateCoefficient 1 0 i j)) := by
  have hQ := whiteningMatrix_tendsto_one hμ hν hfirst hsecond
  have hQij (a b : Fin n) := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hQ a)) b
  cases j with
  | some j => exact hQij i j
  | none =>
    have hm (a : Fin n) : Tendsto (fun k => (∫ x, x ∂ν k) a) atTop (𝓝 (0 : ℝ)) := by
      have heq (k : ℕ) : (∫ x, x ∂ν k) a = ∫ x : Space n, x a ∂ν k :=
        ((EuclideanSpace.proj a).integral_comp_comm
          ((hν k).memLp_id.integrable (by norm_num))).symm
      simpa only [heq] using hfirst a
    have hh := (tendsto_finsetSum Finset.univ fun a _ => (hQij i a).mul (hm a)).neg
    simpa only [affineCoordinateCoefficient, PiLp.neg_apply, matrixAction_apply,
      mul_zero, Finset.sum_const_zero, neg_zero, PiLp.zero_apply] using hh

theorem eventually_whiteningMatrix_norm_le_two :
    ∀ᶠ k in atTop, ‖matrixAction (inverseSqrtMatrix (covarianceMatrix (ν k)))‖ ≤ 2 := by
  have hlim := continuous_matrixAction.norm.continuousAt.tendsto.comp
    (whiteningMatrix_tendsto_one hμ hν hfirst hsecond)
  have hI : ‖matrixAction (1 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    simp only [matrixAction_one_apply, one_mul]
    exact le_rfl
  exact (hlim.eventually (eventually_lt_nhds (lt_of_le_of_lt hI (by norm_num)))).mono
    fun _ h => h.le

theorem eventually_whitened_admissible :
    ∀ᶠ k in atTop, admissibleMeasure (whitenedMeasure (ν k)) := by
  filter_upwards [eventually_covarianceMatrix_posDef hμ hν hfirst hsecond] with k hk
  exact ⟨inferInstance, (hν k).whitenedMeasure, whitenedMeasure_isIsotropic ((hν k).memLp_id) hk⟩

theorem coordinate_moment_whitened_tendsto
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → Fin n)
    (hprod : ∀ s : ι → Option (Fin n),
      Tendsto (fun k => ∫ x, ∏ a, coordinateWithConstant (s a) x ∂ν k) atTop
        (𝓝 (∫ x, ∏ a, coordinateWithConstant (s a) x ∂μ))) :
    Tendsto (fun k => ∫ x, ∏ a, x (r a) ∂whitenedMeasure (ν k)) atTop
      (𝓝 (∫ x, ∏ a, x (r a) ∂μ)) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have heq (k : ℕ) := (hν k).integral_prod_affineMatrixMeasure r
    (inverseSqrtMatrix (covarianceMatrix (ν k)))
    (-matrixAction (inverseSqrtMatrix (covarianceMatrix (ν k))) (∫ x, x ∂ν k))
  simp_rw [whitenedMeasure, heq]
  have hh := tendsto_finsetSum (Finset.univ : Finset (ι → Option (Fin n))) fun s _ =>
    (tendsto_finsetProd Finset.univ fun a _ =>
      whiteningCoefficient_tendsto hμ hν hfirst hsecond (r a) (s a)).mul (hprod s)
  have hid := hμ.logConcave.integral_prod_affineMatrixMeasure r 1 0
  rw [affineMatrixMeasure_one_zero] at hid
  simpa only [← hid] using hh

end KLSConstantImprovement.ActualSecondMomentWhitening405
#print axioms KLSConstantImprovement.ActualSecondMomentWhitening405.covarianceMatrix_tendsto_one
#print axioms KLSConstantImprovement.ActualSecondMomentWhitening405.whiteningCoefficient_tendsto
#print axioms KLSConstantImprovement.ActualSecondMomentWhitening405.eventually_whitened_admissible
#print axioms KLSConstantImprovement.ActualSecondMomentWhitening405.coordinate_moment_whitened_tendsto
