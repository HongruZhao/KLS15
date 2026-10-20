import ActualWeightedAppellCentering

/-! A genuine centered tilted-law maximum and its heat correction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25 KLS.TensorEnergy
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem actual_weighted_tilt_family_variance_bound {n N : ℕ} {K : ℝ}
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ)
    (hglobal : ∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν : Measure (Space n)))
      (g : Lp ℝ 2 (ν : Measure (Space n))),
      actualWeightedAppellEnergy (ν : Measure (Space n)) g K N ≤ M*‖g‖^2) :
    ∃ r : ℝ, 0<r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      actualWeightedCovarianceAppellEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
        (polynomialEval p) K N ≤
      M*((∫ x, (polynomialEval p x)^2 ∂actualDampedTiltLaw (μ : Measure (Space n)) z s)-
        actualCovarianceAppellEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
          (polynomialEval p) 0) := by
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
  have hmean : (∫ x,g x ∂whitenedMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s))^2 =
      actualCovarianceAppellEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
        (polynomialEval p) 0 := by
    rw [←actualCovarianceAppellEnergy_zero_eq_mean_sq,
      actualCovarianceAppellEnergy_isotropic hadm.isotropic,
      actualAppellEnergy_congr_ae hg,actualAppellEnergy_whitening hLC hpos hf]
  have hm := actual_weighted_global_variance_bound hadm.logConcave (hglobal ν hadm) g
  change actualWeightedAppellEnergy
    (whitenedMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s)) g K N ≤ M*(‖g‖^2-
      (∫ x,g x ∂whitenedMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s))^2) at hm
  rw [actualWeightedAppellEnergy_congr_ae hg,
    actualWeightedCovarianceAppellEnergy_whitening hLC hpos hf,hn,hmean] at hm
  exact hm

theorem actualAppellEnergyHeatGenerator_zero_eq_one {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hmean : (∫ x,f x ∂μ)=0) :
    actualAppellEnergyHeatGenerator μ f 0=actualAppellEnergy μ f 1 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hT : actualAppellCoefficient μ f 0=0 := by
    funext a
    rw [actualAppellCoefficient_zero_eq_mean,hmean]
    rfl
  unfold actualAppellEnergyHeatGenerator
  rw [actualCovarianceAppellEnergy_generator_exact hμ hf 0,hT]
  simpa [energyNoiseCorrection] using actualAppell_next_slices_square μ f 0

theorem actual_weighted_polynomial_centered_heat_nonpos {n N : ℕ} {K : ℝ}
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ)
    (hmean : (∫ x,polynomialEval p x ∂(μ : Measure (Space n)))=0)
    (heq : actualWeightedAppellEnergy (μ : Measure (Space n)) (polynomialEval p) K N=
      M*(∫ x,(polynomialEval p x)^2 ∂(μ : Measure (Space n))))
    (hfamily : ∃ r : ℝ, 0<r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      actualWeightedCovarianceAppellEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
        (polynomialEval p) K N ≤
      M*((∫ x,(polynomialEval p x)^2 ∂actualDampedTiltLaw (μ : Measure (Space n)) z s)-
        actualCovarianceAppellEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
          (polynomialEval p) 0)) :
    actualWeightedAppellHeatGenerator (μ : Measure (Space n)) (polynomialEval p) K N+
      M*actualAppellEnergy (μ : Measure (Space n)) (polynomialEval p) 1 ≤ 0 := by
  let x : ℝ → Space n → ℝ := fun s z => actualWeightedCovarianceAppellEnergy
    (actualDampedTiltLaw (μ : Measure (Space n)) z s) (polynomialEval p) K N
  let g := actualTestL2Field (μ : Measure (Space n)) (polynomialEval p)
  let y : ℝ → Space n → ℝ := fun s z => actualCovarianceAppellEnergy
    (actualDampedTiltLaw (μ : Measure (Space n)) z s) (polynomialEval p) 0
  let H : ℝ → Space n → ℝ := fun s z => x s z-M*g s z-(-M)*y s z
  have hf := polynomialEval_memLp_two hμ.logConcave p
  have hf2 := polynomialEval_square_memLp hμ.logConcave p
  have hx : ContDiffAt ℝ (⊤ : ℕ∞) (x 0) 0 := by
    unfold x actualWeightedCovarianceAppellEnergy
    simpa only [Finset.sum_apply] using ContDiffAt.sum (s:=Finset.Icc 2 N) (fun d hd =>
      (contDiffAt_const.mul (contDiffAt_actualCovarianceAppellEnergy_theta hμ hf d) :
        ContDiffAt ℝ (⊤ : ℕ∞)
          (fun z => (K^d*(d.factorial:ℝ)^2)⁻¹*actualCovarianceAppellEnergy
            (actualDampedTiltLaw (μ:Measure (Space n)) z 0) (polynomialEval p) d) 0))
  have hxs : DifferentiableWithinAt ℝ (fun s => x s 0) (Ici 0) 0 := by
    have hds (d : ℕ) (_hd : d∈Finset.Icc 2 N) : DifferentiableWithinAt ℝ
        (fun s => (K^d*(d.factorial:ℝ)^2)⁻¹*actualCovarianceAppellEnergy
          (actualDampedTiltLaw (μ:Measure (Space n)) 0 s) (polynomialEval p) d) (Ici 0) 0 :=
      (differentiableWithinAt_actualCovarianceAppellEnergy_damping hμ hf d).const_mul _
    unfold x actualWeightedCovarianceAppellEnergy
    convert DifferentiableWithinAt.sum hds using 1
    ext s
    simp
  have hg := contDiffAt_actualTestL2Field_theta hμ.logConcave hf2
  have hgs := differentiableWithinAt_actualTestL2Field_damping hμ.logConcave hf2
  have hy := contDiffAt_actualCovarianceAppellEnergy_theta hμ hf 0
  have hys := differentiableWithinAt_actualCovarianceAppellEnergy_damping hμ hf 0
  have hzero : H 0 0=0 := by
    dsimp [H,x,g,y]
    rw [actualDampedTiltLaw_zero_damping,exponentialTilt_zero,
      actualWeightedCovarianceAppellEnergy_isotropic hμ.isotropic,actualTestL2Field_zero,heq,
      actualCovarianceAppellEnergy_zero_eq_mean_sq,hmean]
    ring
  obtain ⟨r,hr,hm⟩ := hfamily
  have hθ : IsLocalMax (H 0) 0 := by
    have hb : ∀ᶠ z : Space n in 𝓝 0,z∈ball 0 r :=
      isOpen_ball.mem_nhds (mem_ball_self hr)
    filter_upwards [hb] with z hz
    rw [hzero]
    have hz' : ‖z‖ ≤ r := (by simpa only [mem_ball,dist_zero_right] using hz : ‖z‖<r).le
    have hh := hm z hz' 0 le_rfl
    dsimp [H,x,g,y,actualTestL2Field]
    linarith
  have hs : IsLocalMaxOn (fun s => H s 0) (Ici 0) 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hzero]
    have hh := hm 0 (by simpa using hr.le) s hs
    dsimp [H,x,g,y,actualTestL2Field]
    linarith
  have hmax := localHeatGenerator_nonpos_of_localMax ((hx.sub (contDiffAt_const.mul hg)).sub (contDiffAt_const.mul hy)) hθ hs
    (fun i : Fin n => EuclideanSpace.single i 1)
  have he := localHeatGenerator_linear_combination (x:=x) (y:=y) (g:=g)
    hx hy hg hxs hys hgs (fun i : Fin n => EuclideanSpace.single i 1) M (-M)
  have hGg : localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) g=0 :=
    localHeatGenerator_actualTestL2Field hμ.logConcave hμ.isotropic hf2
  have hGx : localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) x=
      actualWeightedAppellHeatGenerator (μ : Measure (Space n)) (polynomialEval p) K N :=
    actualWeightedAppellHeatGenerator_eq hμ hf K
  have he' : localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) H=
      localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) x-
        M*localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) g-
        (-M)*localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) y := by
    simpa [H] using he
  have hGy : localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) y=
      actualAppellEnergy (μ : Measure (Space n)) (polynomialEval p) 1 :=
    actualAppellEnergyHeatGenerator_zero_eq_one hμ hf hmean
  rw [he',hGg,hGx,hGy] at hmax
  linarith

theorem exists_actual_centered_weighted_maximum_energy_inequality {n N : ℕ} {K : ℝ} (hK : 0<K)
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
      actualWeightedAppellHeatGenerator (μ : Measure (Space n)) f K N+
        M*actualAppellEnergy (μ : Measure (Space n)) f 1 ≤ 0 := by
  obtain ⟨μ,hμ,c,hunit,hglobal,hstat,hfamily⟩ := exists_actual_weighted_both_optimalities hK hμ₀
  let f := polynomialLp hμ.logConcave (boundedDegreePolynomial c)
  let M := actualWeightedAppellEnergy (μ : Measure (Space n)) f K N
  have hnorm : (∫ x,(polynomialEval (boundedDegreePolynomial c) x)^2 ∂(μ:Measure (Space n)))=1 := by
    rw [←polynomialLp_norm_sq hμ.logConcave,hunit]
    norm_num
  have heq : actualWeightedAppellEnergy (μ:Measure (Space n))
      (polynomialEval (boundedDegreePolynomial c)) K N=M*
        (∫ x,(polynomialEval (boundedDegreePolynomial c) x)^2 ∂(μ:Measure (Space n))) := by
    rw [hnorm,mul_one]
    exact (actualWeightedAppellEnergy_polynomialLp hμ.logConcave _ K N).symm
  refine ⟨μ,hμ,c,hunit,hglobal,hstat,?_⟩
  have hM : 0 ≤ M := actualWeightedAppellEnergy_nonneg _ f hK N
  rcases eq_or_lt_of_le hM with hzero | hpos
  · have hg := actual_weighted_polynomial_heat_nonpos hμ (boundedDegreePolynomial c) M heq hfamily
    rw [←actualWeightedAppellHeatGenerator_congr_ae
      (polynomialLp_coe hμ.logConcave (boundedDegreePolynomial c))] at hg
    change actualWeightedAppellHeatGenerator (μ:Measure (Space n)) f K N+
      M*actualAppellEnergy (μ:Measure (Space n)) f 1≤0
    rw [←hzero,zero_mul,add_zero]
    exact hg
  · have hmean := actual_weighted_maximum_mean_zero hμ.logConcave f hpos hstat
    have hrawmean : (∫ x,polynomialEval (boundedDegreePolynomial c) x ∂(μ:Measure (Space n)))=0 := by
      rw [←integral_congr_ae (polynomialLp_coe hμ.logConcave (boundedDegreePolynomial c))]
      exact hmean
    have hv := actual_weighted_tilt_family_variance_bound hμ (boundedDegreePolynomial c) M hglobal
    have hg := actual_weighted_polynomial_centered_heat_nonpos hμ (boundedDegreePolynomial c)
      M hrawmean heq hv
    rwa [←actualWeightedAppellHeatGenerator_congr_ae
      (polynomialLp_coe hμ.logConcave (boundedDegreePolynomial c)),
      ←actualAppellEnergy_congr_ae (polynomialLp_coe hμ.logConcave (boundedDegreePolynomial c))] at hg

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_weighted_tilt_family_variance_bound
#print axioms KLS.DeterministicBridgeNext.actualAppellEnergyHeatGenerator_zero_eq_one

#print axioms KLS.DeterministicBridgeNext.actual_weighted_polynomial_centered_heat_nonpos

#print axioms KLS.DeterministicBridgeNext.exists_actual_centered_weighted_maximum_energy_inequality
