import ActualWeightedAppellMaximizer

/-! Both actual test-function stationarity and actual law-family maximality
at the same constructed weighted maximum. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration KLSBelow25 KLS.TensorEnergy
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem actual_weighted_test_stationarity {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) (f : Lp ℝ 2 μ)
    (K : ℝ) (hunit : ‖f‖=1)
    (hglobal : ∀ g : Lp ℝ 2 μ, actualWeightedAppellEnergy μ g K N ≤
      actualWeightedAppellEnergy μ f K N*‖g‖^2) (ell : Lp ℝ 2 μ) :
    actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell := by
  let b := actualWeightedAppellPairing f ell K N-
    actualWeightedAppellEnergy μ f K N*inner ℝ f ell
  let c := actualWeightedAppellEnergy μ ell K N-
    actualWeightedAppellEnergy μ f K N*‖ell‖^2
  have hquad (t : ℝ) : 2*t*b+t^2*c ≤ 0 := by
    have h := hglobal (f+t • ell)
    rw [actualWeightedAppellEnergy_add_smul hLC,norm_add_sq_real,norm_smul,
      Real.norm_eq_abs,mul_pow,sq_abs,hunit] at h
    simp only [inner_smul_right,one_pow] at h
    dsimp [b,c]
    nlinarith
  have hlocal : IsLocalMax (fun t : ℝ => 2*t*b+t^2*c) 0 := by
    apply Eventually.of_forall
    intro t
    simpa using hquad t
  have hd : HasDerivAt (fun t : ℝ => 2*t*b+t^2*c) (2*b) 0 := by
    convert (((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const b).add
      (((hasDerivAt_id (0:ℝ)).pow 2).mul_const c) using 1 <;> norm_num <;> rfl
  have hzero := hlocal.hasDerivAt_eq_zero hd
  dsimp [b] at hzero
  linarith

theorem actualWeightedCovarianceAppellEnergy_isotropic {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hiso : IsIsotropic μ) (f : Space n → ℝ) (K : ℝ) :
    actualWeightedCovarianceAppellEnergy μ f K N=actualWeightedAppellEnergy μ f K N := by
  unfold actualWeightedCovarianceAppellEnergy actualWeightedAppellEnergy
  exact Finset.sum_congr rfl fun d hd => congrArg (_ * ·)
    (actualCovarianceAppellEnergy_isotropic hiso f)

theorem actualWeightedCovarianceAppellEnergy_whitening {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (hp : (covarianceMatrix μ).PosDef) {f : Space n → ℝ} (hf : MemLp f 2 μ) (K : ℝ) :
    actualWeightedAppellEnergy (whitenedMeasure μ)
      (fun y => f ((actualWhiteningEquiv μ hp).symm y)) K N=
    actualWeightedCovarianceAppellEnergy μ f K N := by
  unfold actualWeightedAppellEnergy actualWeightedCovarianceAppellEnergy
  exact Finset.sum_congr rfl fun d hd => congrArg (_ * ·)
    (actualAppellEnergy_whitening hLC hp hf)

theorem actual_weighted_tilt_family_bound {n N : ℕ} {K : ℝ}
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ)
    (hglobal : ∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν : Measure (Space n)))
      (g : Lp ℝ 2 (ν : Measure (Space n))),
      actualWeightedAppellEnergy (ν : Measure (Space n)) g K N ≤ M*‖g‖^2) :
    ∃ r : ℝ, 0<r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      actualWeightedCovarianceAppellEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
        (polynomialEval p) K N ≤
      M*(∫ x, (polynomialEval p x)^2 ∂actualDampedTiltLaw (μ : Measure (Space n)) z s) := by
  obtain ⟨r,hr,hfamily⟩ := exists_local_actual_damped_whitening hμ
  refine ⟨r,hr,?_⟩
  intro z hz s hs
  obtain ⟨hprob,hsupp,hpos,hadm⟩ := hfamily z hz s hs
  letI : IsProbabilityMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s) := hprob
  have hLC := actualDampedTiltLaw_logConcave hμ z hs
  have hf := polynomialEval_memLp_two hLC p
  let ν : ProbabilityMeasure (Space n) := ⟨_,hadm.isProb⟩
  let g := (actual_whitening_test_memLp hpos hf).toLp
    (fun y => polynomialEval p ((actualWhiteningEquiv
      (actualDampedTiltLaw (μ : Measure (Space n)) z s) hpos).symm y))
  have hg : (g : Space n → ℝ) =ᵐ[whitenedMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s)]
      fun y => polynomialEval p ((actualWhiteningEquiv
        (actualDampedTiltLaw (μ : Measure (Space n)) z s) hpos).symm y) :=
    (actual_whitening_test_memLp hpos hf).coeFn_toLp
  have hn : ‖g‖^2=∫ x, (polynomialEval p x)^2 ∂actualDampedTiltLaw (μ : Measure (Space n)) z s := by
    rw [actualLp_norm_sq_eq_integral]
    calc
      _ = ∫ y, (polynomialEval p ((actualWhiteningEquiv
          (actualDampedTiltLaw (μ : Measure (Space n)) z s) hpos).symm y))^2
          ∂whitenedMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s) :=
        integral_congr_ae (hg.fun_comp (fun t : ℝ => t^2))
      _ = _ := actual_whitening_test_L2_energy _ hpos _
  have hm := hglobal ν hadm g
  change actualWeightedAppellEnergy
    (whitenedMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s)) g K N ≤ M*‖g‖^2 at hm
  rw [actualWeightedAppellEnergy_congr_ae hg,
    actualWeightedCovarianceAppellEnergy_whitening hLC hpos hf,hn] at hm
  exact hm

theorem exists_actual_weighted_both_optimalities {n N : ℕ} {K : ℝ} (hK : 0<K)
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n))) :
    ∃ (μ : ProbabilityMeasure (Space n)) (hμ : admissibleMeasure (μ : Measure (Space n)))
      (c : DegreeIndex n N → ℝ),
      let f := polynomialLp hμ.logConcave (boundedDegreePolynomial c)
      let M := actualWeightedAppellEnergy (μ : Measure (Space n)) f K N
      ‖f‖=1 ∧
      (∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν : Measure (Space n)))
        (g : Lp ℝ 2 (ν : Measure (Space n))), actualWeightedAppellEnergy (ν : Measure (Space n))
          g K N ≤ M*‖g‖^2) ∧
      (∀ ell : Lp ℝ 2 (μ : Measure (Space n)), actualWeightedAppellPairing f ell K N=
        M*inner ℝ f ell) ∧
      ∃ r : ℝ, 0<r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
        actualWeightedCovarianceAppellEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
          (polynomialEval (boundedDegreePolynomial c)) K N ≤
        M*(∫ x, (polynomialEval (boundedDegreePolynomial c) x)^2
          ∂actualDampedTiltLaw (μ : Measure (Space n)) z s) := by
  obtain ⟨μ,hμ,c,hunit,hglobal⟩ := exists_actual_weighted_L2_maximizer hK hμ₀
  refine ⟨μ,hμ,c,hunit,hglobal,?_,?_⟩
  · exact actual_weighted_test_stationarity hμ.logConcave _ K hunit (hglobal μ hμ)
  · exact actual_weighted_tilt_family_bound hμ (boundedDegreePolynomial c) _ hglobal

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_weighted_test_stationarity
#print axioms KLS.DeterministicBridgeNext.exists_actual_weighted_both_optimalities
