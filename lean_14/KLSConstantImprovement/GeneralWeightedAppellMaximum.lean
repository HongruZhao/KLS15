import KLSConstantImprovement.GeneralWeightedAppellEnergy

/-! Arbitrary finite positive-degree weights: actual all-law/L2 attainment,
stationarity, and normalized tilted-law maximality. Original compact Gram
polynomial machinery and whitening theorems supply every analytic premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLSConstantImprovement.GeneralWeighted
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration KLSBelow25 KLS.TensorEnergy
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

theorem exists_normalized_polynomial_maximizer {n N : ℕ}
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n)))
    (w : ℕ → ℝ) :
    ∃ z∈normalizedPolynomialPairs (degreeExponent n N),
      ∀ y∈normalizedPolynomialPairs (degreeExponent n N),
        energy (y.1 : Measure (Space n))
          (polynomialEval (boundedDegreePolynomial y.2)) w N ≤
        energy (z.1 : Measure (Space n))
          (polynomialEval (boundedDegreePolynomial z.2)) w N :=
  (isCompact_boundedDegree_normalizedPolynomialPairs n N).exists_isMaxOn
    (normalizedPolynomialPairs_nonempty_of_admissible hμ₀)
    (energy_polynomial_continuousOn w)

theorem polynomial_bound_of_normalized_maximum {n N : ℕ} {w : ℕ → ℝ} (hw : ∀ d, 2 ≤ d → 0 ≤ w d)
    (z : ProbabilityMeasure (Space n) × (DegreeIndex n N → ℝ))
    (hz : z∈normalizedPolynomialPairs (degreeExponent n N))
    (hmax : ∀ y∈normalizedPolynomialPairs (degreeExponent n N),
      energy (y.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial y.2)) w N ≤
      energy (z.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial z.2)) w N)
    {ν : ProbabilityMeasure (Space n)} (hν : admissibleMeasure (ν : Measure (Space n)))
    (c : DegreeIndex n N → ℝ) :
    energy (ν : Measure (Space n))
      (polynomialLp hν.logConcave (boundedDegreePolynomial c)) w N ≤
    energy (z.1 : Measure (Space n))
      (polynomialEval (boundedDegreePolynomial z.2)) w N*
        ‖polynomialLp hν.logConcave (boundedDegreePolynomial c)‖^2 := by
  let p := polynomialLp hν.logConcave (boundedDegreePolynomial c)
  have hnonneg := energy_nonneg (z.1 : Measure (Space n))
    (polynomialEval (boundedDegreePolynomial z.2)) w hw N
  by_cases hp : p=0
  · change energy _ p _ _ ≤ _*‖p‖^2
    rw [hp,energy_zero hν.logConcave]
    simp
  · obtain ⟨a,ha,han⟩ := normalize_actual_polynomial_pair hν c hp
    have hm := hmax (ν,a • c) han
    rw [←energy_polynomialLp hν.logConcave] at hm
    change energy (ν : Measure (Space n))
      (polynomialLp hν.logConcave (polynomialCombination (degreeExponent n N) (a • c))) w N ≤ _ at hm
    rw [polynomialLp_combination_smul,energy_smul hν.logConcave] at hm
    have hn : a^2*‖p‖^2=1 := by
      have h := (polynomialCoefficientEnergy_eq_norm_sq _ hν (a • c)).symm.trans han.2
      change ‖polynomialLp hν.logConcave (polynomialCombination (degreeExponent n N) (a • c))‖^2=1 at h
      rw [polynomialLp_combination_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at h
      exact h
    have hp2 : 0<‖p‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hp)
    have hm' := mul_le_mul_of_nonneg_right hm hp2.le
    change _*energy _ p _ _*‖p‖^2 ≤ _ at hm'
    have hid : a^2*energy (ν : Measure (Space n)) p w N*‖p‖^2=
        energy (ν : Measure (Space n)) p w N := by
      calc
        _ = (a^2*‖p‖^2)*energy (ν : Measure (Space n)) p w N := by ring
        _ = _ := by rw [hn,one_mul]
    rw [hid] at hm'
    exact hm'

theorem L2_bound_of_normalized_maximum {n N : ℕ} {w : ℕ → ℝ} (hw : ∀ d, 2 ≤ d → 0 ≤ w d)
    (z : ProbabilityMeasure (Space n) × (DegreeIndex n N → ℝ))
    (hz : z∈normalizedPolynomialPairs (degreeExponent n N))
    (hmax : ∀ y∈normalizedPolynomialPairs (degreeExponent n N),
      energy (y.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial y.2)) w N ≤
      energy (z.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial z.2)) w N)
    {ν : ProbabilityMeasure (Space n)} (hν : admissibleMeasure (ν : Measure (Space n)))
    (g : Lp ℝ 2 (ν : Measure (Space n))) :
    energy (ν : Measure (Space n)) g w N ≤
      energy (z.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial z.2)) w N*‖g‖^2 := by
  obtain ⟨c,hcnorm,hce⟩ := exists_actual_polynomial_Appell_energy_projection (d:=N) hν g
  have he : energy (ν : Measure (Space n))
      (polynomialLp hν.logConcave (boundedDegreePolynomial c)) w N=
        energy (ν : Measure (Space n)) g w N := by
    rw [energy_polynomialLp]
    unfold energy
    apply Finset.sum_congr rfl
    intro d hd
    rw [hce d (Finset.mem_Icc.mp hd).2]
  have hb := polynomial_bound_of_normalized_maximum hw z hz hmax hν c
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hcnorm)
    (energy_nonneg _ _ w hw N))

theorem exists_L2_maximizer {n N : ℕ} {w : ℕ → ℝ} (hw : ∀ d, 2 ≤ d → 0 ≤ w d)
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n))) :
    ∃ (μ : ProbabilityMeasure (Space n)) (hμ : admissibleMeasure (μ : Measure (Space n)))
      (c : DegreeIndex n N → ℝ),
      let f := polynomialLp hμ.logConcave (boundedDegreePolynomial c)
      ‖f‖=1 ∧
      ∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν : Measure (Space n)))
        (g : Lp ℝ 2 (ν : Measure (Space n))),
        energy (ν : Measure (Space n)) g w N ≤
          energy (μ : Measure (Space n)) f w N*‖g‖^2 := by
  obtain ⟨z,hz,hm⟩ := exists_normalized_polynomial_maximizer hμ₀ w
  have hn : ‖polynomialLp hz.1.logConcave (boundedDegreePolynomial z.2)‖^2=1 :=
    (polynomialCoefficientEnergy_eq_norm_sq _ hz.1 z.2).symm.trans hz.2
  refine ⟨z.1,hz.1,z.2,by nlinarith [norm_nonneg (polynomialLp hz.1.logConcave
    (boundedDegreePolynomial z.2))],?_⟩
  intro ν hν g
  simpa only [energy_polynomialLp] using
    L2_bound_of_normalized_maximum hw z hz hm hν g


theorem test_stationarity {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) (f : Lp ℝ 2 μ)
    (w : ℕ → ℝ) (hunit : ‖f‖=1)
    (hglobal : ∀ g : Lp ℝ 2 μ, energy μ g w N ≤
      energy μ f w N*‖g‖^2) (ell : Lp ℝ 2 μ) :
    pairing f ell w N=
      energy μ f w N*inner ℝ f ell := by
  let b := pairing f ell w N-
    energy μ f w N*inner ℝ f ell
  let c := energy μ ell w N-
    energy μ f w N*‖ell‖^2
  have hquad (t : ℝ) : 2*t*b+t^2*c ≤ 0 := by
    have h := hglobal (f+t • ell)
    rw [energy_add_smul hLC,norm_add_sq_real,norm_smul,
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

theorem covarianceEnergy_isotropic {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hiso : IsIsotropic μ) (f : Space n → ℝ) (w : ℕ → ℝ) :
    covarianceEnergy μ f w N=energy μ f w N := by
  unfold covarianceEnergy energy
  exact Finset.sum_congr rfl fun d hd => congrArg (_ * ·)
    (actualCovarianceAppellEnergy_isotropic hiso f)

theorem covarianceEnergy_whitening {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (hp : (covarianceMatrix μ).PosDef) {f : Space n → ℝ} (hf : MemLp f 2 μ) (w : ℕ → ℝ) :
    energy (whitenedMeasure μ)
      (fun y => f ((actualWhiteningEquiv μ hp).symm y)) w N=
    covarianceEnergy μ f w N := by
  unfold energy covarianceEnergy
  exact Finset.sum_congr rfl fun d hd => congrArg (_ * ·)
    (actualAppellEnergy_whitening hLC hp hf)

theorem tilt_family_bound {n N : ℕ} {w : ℕ → ℝ}
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ)
    (hglobal : ∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν : Measure (Space n)))
      (g : Lp ℝ 2 (ν : Measure (Space n))),
      energy (ν : Measure (Space n)) g w N ≤ M*‖g‖^2) :
    ∃ r : ℝ, 0<r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      covarianceEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
        (polynomialEval p) w N ≤
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
  change energy
    (whitenedMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s)) g w N ≤ M*‖g‖^2 at hm
  rw [energy_congr_ae hg,
    covarianceEnergy_whitening hLC hpos hf,hn] at hm
  exact hm

theorem exists_both_optimalities {n N : ℕ} {w : ℕ → ℝ} (hw : ∀ d, 2 ≤ d → 0 ≤ w d)
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n))) :
    ∃ (μ : ProbabilityMeasure (Space n)) (hμ : admissibleMeasure (μ : Measure (Space n)))
      (c : DegreeIndex n N → ℝ),
      let f := polynomialLp hμ.logConcave (boundedDegreePolynomial c)
      let M := energy (μ : Measure (Space n)) f w N
      ‖f‖=1 ∧
      (∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν : Measure (Space n)))
        (g : Lp ℝ 2 (ν : Measure (Space n))), energy (ν : Measure (Space n))
          g w N ≤ M*‖g‖^2) ∧
      (∀ ell : Lp ℝ 2 (μ : Measure (Space n)), pairing f ell w N=
        M*inner ℝ f ell) ∧
      ∃ r : ℝ, 0<r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
        covarianceEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
          (polynomialEval (boundedDegreePolynomial c)) w N ≤
        M*(∫ x, (polynomialEval (boundedDegreePolynomial c) x)^2
          ∂actualDampedTiltLaw (μ : Measure (Space n)) z s) := by
  obtain ⟨μ,hμ,c,hunit,hglobal⟩ := exists_L2_maximizer hw hμ₀
  refine ⟨μ,hμ,c,hunit,hglobal,?_,?_⟩
  · exact test_stationarity hμ.logConcave _ w hunit (hglobal μ hμ)
  · exact tilt_family_bound hμ (boundedDegreePolynomial c) _ hglobal

end KLSConstantImprovement.GeneralWeighted
#print axioms KLSConstantImprovement.GeneralWeighted.exists_L2_maximizer
#print axioms KLSConstantImprovement.GeneralWeighted.test_stationarity
#print axioms KLSConstantImprovement.GeneralWeighted.covarianceEnergy_whitening
#print axioms KLSConstantImprovement.GeneralWeighted.exists_both_optimalities
