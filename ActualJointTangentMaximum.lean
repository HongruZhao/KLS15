import ActualJointPolynomialMaximum

/-! The existing constructed global all-law/all-L2 optimum gives a genuine
joint normalized-tilt/test local maximum, including arbitrary-degree
polynomial perturbations. No joint Hessian or mixed-block sign is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped ContDiff Topology BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25 KLS.TensorEnergy
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

 theorem actual_joint_all_L2_tilt_family_bound
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (p : MvPolynomial (Fin n) ℝ) (h : ℝ) (φ : ℝ → ℝ)
    (hmax : ∀ (ν : ProbabilityMeasure (Space n))
      (hν : admissibleMeasure (ν : Measure (Space n))) (g : Lp ℝ 2 (ν : Measure (Space n))),
      coefficientQuotient (fullClassAppellLinearMap hν.logConcave k)
        (fullClassAppellLinearMap hν.logConcave (k+1)) h φ g ≤
      coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
        (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ (polynomialLp hμ.logConcave p)) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      ∀ g : Space n → ℝ, MemLp g 2 (actualDampedTiltLaw (μ : Measure (Space n)) z s) →
        actualCovarianceAppellQuotient (actualDampedTiltLaw (μ : Measure (Space n)) z s)
          g k h φ ≤ actualCovarianceAppellQuotient (μ : Measure (Space n))
            (polynomialEval p) k h φ := by
  obtain ⟨r,hr,hfamily⟩ := exists_local_actual_damped_whitening hμ
  refine ⟨r,hr,?_⟩
  intro z hz s hs g hg
  obtain ⟨hprob,hsupp,hpos,hadm⟩ := hfamily z hz s hs
  letI : IsProbabilityMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s) := hprob
  have hLC := actualDampedTiltLaw_logConcave hμ z hs
  let ν : ProbabilityMeasure (Space n) := ⟨_,hadm.isProb⟩
  have hm := hmax ν hadm ((actual_whitening_test_memLp hpos hg).toLp
    (fun y => g ((actualWhiteningEquiv (actualDampedTiltLaw
      (μ : Measure (Space n)) z s) hpos).symm y)))
  rw [← actual_covariance_quotient_eq_whitened hLC hpos hg] at hm
  exact hm.trans_eq (actual_covariance_polynomial_quotient_isotropic hμ p h φ).symm

 theorem actual_polynomial_joint_tangent_localMax
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (p q : MvPolynomial (Fin n) ℝ) {h : ℝ} (hh : 0 < h) {φ : ℝ → ℝ}
    (hφ : ConcaveOn ℝ (Icc 0 1) φ)
    (hφpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < φ u)
    (hprevious : ∀ (ν : Measure (Space n)), admissibleMeasure ν → ∀ f : Space n → ℝ,
      MemLp f 2 ν → actualAppellEnergy ν f k ≤ h*(∫ x, (f x)^2 ∂ν))
    (hunit : (∫ x, (polynomialEval p x)^2 ∂(μ : Measure (Space n)))=1)
    {d : ℝ} (hd : HasDerivAt φ d
      (actualCovarianceAppellEnergy (μ : Measure (Space n)) (polynomialEval p) k/h))
    (hmax : ∀ (ν : ProbabilityMeasure (Space n))
      (hν : admissibleMeasure (ν : Measure (Space n))) (g : Lp ℝ 2 (ν : Measure (Space n))),
      coefficientQuotient (fullClassAppellLinearMap hν.logConcave k)
        (fullClassAppellLinearMap hν.logConcave (k+1)) h φ g ≤
      coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
        (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ (polynomialLp hμ.logConcave p)) :
    let X := actualCovarianceAppellEnergy (μ : Measure (Space n)) (polynomialEval p) (k+1)
    let u := actualCovarianceAppellEnergy (μ : Measure (Space n)) (polynomialEval p) k/h
    let w := -(X/φ u)*(d/h)
    let lam := (X/φ u)*(φ u-u*d)
    IsLocalMax (actualJointTangentQuadratic (μ : Measure (Space n))
      (polynomialEval p) (polynomialEval q) k w lam) 0 := by
  dsimp only
  let f := polynomialEval p
  let g := polynomialEval q
  let X := actualCovarianceAppellEnergy (μ : Measure (Space n)) f (k+1)
  let u := actualCovarianceAppellEnergy (μ : Measure (Space n)) f k/h
  let w := -(X/φ u)*(d/h)
  let lam := (X/φ u)*(φ u-u*d)
  let F := actualJointTangentQuadratic (μ : Measure (Space n)) f g k w lam
  have hp := polynomialEval_memLp_two hμ.logConcave p
  have hq := polynomialEval_memLp_two hμ.logConcave q
  have hu : u ∈ Icc (0 : ℝ) 1 := by
    dsimp [u,f]
    rw [actualCovarianceAppellEnergy_isotropic hμ.isotropic]
    have hb := hprevious (μ : Measure (Space n)) hμ _ hp
    rw [hunit,mul_one] at hb
    exact ⟨div_nonneg (actualAppellEnergy_nonneg _ _ _) hh.le,(div_le_one hh).mpr hb⟩
  have hpφ : φ u ≠ 0 := (hφpos u hu).ne'
  have hX : 0 ≤ X := by
    dsimp [X]
    rw [actualCovarianceAppellEnergy_isotropic hμ.isotropic]
    exact actualAppellEnergy_nonneg _ _ _
  have hF0 : F 0=0 := by
    dsimp [F,actualJointTangentQuadratic]
    simp only [Prod.fst_zero,Prod.snd_zero,mul_zero,zero_mul,add_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    rw [actualDampedTiltLaw_zero_damping,exponentialTilt_zero]
    change X+w*actualCovarianceAppellEnergy (μ : Measure (Space n)) f k-
      lam*(∫ x, f x*f x ∂(μ : Measure (Space n)))=0
    have hn : (∫ x, f x*f x ∂(μ : Measure (Space n)))=1 := by
      simpa only [f,pow_two] using hunit
    rw [hn]
    dsimp [w,lam,u]
    have hpφ' : φ (actualCovarianceAppellEnergy (μ : Measure (Space n)) f k * h⁻¹) ≠ 0 := by
      simpa only [u,div_eq_mul_inv] using hpφ
    field_simp [hh.ne',hpφ']
    <;> ring_nf
    <;> simp_all only [mul_assoc,mul_inv_cancel₀ hpφ',mul_one,sub_self]
  let G : Space n × ℝ → ℝ := fun z =>
    (∫ x, (f x)^2 ∂actualDampedTiltLaw (μ : Measure (Space n)) z.1 0)+
      2*z.2*(∫ x, f x*g x ∂actualDampedTiltLaw (μ : Measure (Space n)) z.1 0)+
        z.2^2*(∫ x, (g x)^2 ∂actualDampedTiltLaw (μ : Measure (Space n)) z.1 0)
  have hG0 : G 0=1 := by
    simpa only [G,Prod.fst_zero,Prod.snd_zero,mul_zero,zero_mul,add_zero,
      zero_pow (by norm_num : (2:ℕ)≠0),actualDampedTiltLaw_zero_damping,exponentialTilt_zero,f] using hunit
  have hG : ContinuousAt G 0 := by
    have hff := contDiffAt_actualTestL2Field_theta hμ.logConcave
      (polynomialEval_square_memLp hμ.logConcave p)
    have hgg := contDiffAt_actualTestL2Field_theta hμ.logConcave
      (polynomialEval_square_memLp hμ.logConcave q)
    have hfg : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z => ∫ x, f x*g x ∂actualDampedTiltLaw (μ : Measure (Space n)) z 0) 0 := by
      simpa only [actualDampedTiltLaw_zero_damping,f,g] using
        contDiffAt_normalized_tilt_average hμ.logConcave
          (polynomialEval_mul_memLp_two hμ.logConcave p q)
    exact (((hff.comp (0 : Space n × ℝ) contDiffAt_fst).add
      (((contDiffAt_const (c := (2:ℝ))).mul contDiffAt_snd).mul
        (hfg.comp (0 : Space n × ℝ) contDiffAt_fst))).add
      ((contDiffAt_snd.pow 2).mul (hgg.comp (0 : Space n × ℝ) contDiffAt_fst))).continuousAt
  obtain ⟨r₁,hr₁,hfamily⟩ := actual_joint_all_L2_tilt_family_bound hμ p h φ hmax
  obtain ⟨r₂,hr₂,hwhite⟩ := exists_local_actual_damped_whitening hμ
  have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  have hpos : ∀ᶠ z in 𝓝 (0 : Space n × ℝ), 0 < G z :=
    hG.eventually (Ioi_mem_nhds (by rw [hG0];norm_num))
  have hrad : ∀ᶠ z in 𝓝 (0 : Space n × ℝ), ‖z.1‖ ≤ min r₁ r₂ := by
    have he : ∀ᶠ z in 𝓝 (0 : Space n × ℝ), ‖z.1‖ < min r₁ r₂ :=
      (continuousAt_fst.norm : ContinuousAt (fun z : Space n × ℝ => ‖z.1‖) 0).eventually
        (Iio_mem_nhds (by simpa using hr))
    filter_upwards [he] with z hz using hz.le
  change ∀ᶠ z in 𝓝 (0 : Space n × ℝ), F z ≤ F 0
  rw [hF0]
  filter_upwards [hpos,hrad] with z hzp hzr
  obtain ⟨hprob,hsupp,hcov,hadm⟩ := hwhite z.1 (hzr.trans (min_le_right _ _)) 0 le_rfl
  letI : IsProbabilityMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z.1 0) := hprob
  have hLC := actualDampedTiltLaw_logConcave hμ z.1 (show (0:ℝ)≤0 from le_rfl)
  have hpz := polynomialEval_memLp_two hLC p
  have hqz := polynomialEval_memLp_two hLC q
  have htest : MemLp (fun x => f x+z.2*g x) 2
      (actualDampedTiltLaw (μ : Measure (Space n)) z.1 0) := hpz.add (hqz.const_mul z.2)
  have hGval : G z=(∫ x, (f x+z.2*g x)^2
      ∂actualDampedTiltLaw (μ : Measure (Space n)) z.1 0) :=
    (actual_test_mass_add_scaled hpz hqz z.2).symm
  have htestpos : 0 < ∫ x, (f x+z.2*g x)^2
      ∂actualDampedTiltLaw (μ : Measure (Space n)) z.1 0 := hGval ▸ hzp
  have hratio := covariance_Appell_ratio_mem_Icc_of_whitening hLC hcov hadm htest hh hprevious
  have hm := hfamily z.1 (hzr.trans (min_le_left _ _)) 0 le_rfl _ htest
  unfold actualCovarianceAppellQuotient at hm
  rw [hunit,one_mul,mul_one] at hm
  have hb := concave_quotient_tangent_bound hφ hφpos hu hratio hd hh htestpos hX hm
  change F z ≤ 0
  dsimp only [F,actualJointTangentQuadratic]
  rw [actualJointTangentQuadratic_eq hLC hpz hqz]
  dsimp only [w,lam,X,u] at hb ⊢
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_joint_all_L2_tilt_family_bound
#print axioms KLS.DeterministicBridgeNext.actual_polynomial_joint_tangent_localMax
