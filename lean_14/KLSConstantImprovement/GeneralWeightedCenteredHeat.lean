import KLSConstantImprovement.GeneralWeightedAppellMaximum
import ActualCenteredWeightedAppellHeat

/-! General raw degree weights: actual centered tilted-law maximum and heat.
All analytic law, whitening, compact maximum, and original L2 obligations
are derived. Only nonnegativity of the fixed real weights is required. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLSConstantImprovement.GeneralWeighted
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration KLSBelow25 KLS.TensorEnergy
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def heatGenerator {n : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d∈Finset.Icc 2 N,(w d)*actualAppellEnergyHeatGenerator μ f d

theorem heatGenerator_eq {n N : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) (w : ℕ → ℝ) :
    localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1)
      (fun s z => covarianceEnergy (actualDampedTiltLaw μ z s) f w N)=
    heatGenerator μ f w N := by
  unfold covarianceEnergy heatGenerator
  rw [localHeatGenerator_finset_sum]
  · apply Finset.sum_congr rfl
    intro d hd
    exact localHeatGenerator_const_mul_local (contDiffAt_actualCovarianceAppellEnergy_theta hμ hf d)
      (differentiableWithinAt_actualCovarianceAppellEnergy_damping hμ hf d) _ _
  · intro d hd
    exact contDiffAt_const.mul (contDiffAt_actualCovarianceAppellEnergy_theta hμ hf d)
  · intro d hd
    exact (differentiableWithinAt_actualCovarianceAppellEnergy_damping hμ hf d).const_mul _

theorem polynomial_heat_nonpos {n N : ℕ} {w : ℕ → ℝ}
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ)
    (heq : energy (μ : Measure (Space n)) (polynomialEval p) w N=
      M*(∫ x,(polynomialEval p x)^2 ∂(μ : Measure (Space n))))
    (hfamily : ∃ r : ℝ, 0<r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      covarianceEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
        (polynomialEval p) w N ≤
      M*(∫ x,(polynomialEval p x)^2 ∂actualDampedTiltLaw (μ : Measure (Space n)) z s)) :
    heatGenerator (μ : Measure (Space n)) (polynomialEval p) w N ≤ 0 := by
  let x : ℝ → Space n → ℝ := fun s z => covarianceEnergy
    (actualDampedTiltLaw (μ : Measure (Space n)) z s) (polynomialEval p) w N
  let g := actualTestL2Field (μ : Measure (Space n)) (polynomialEval p)
  let H : ℝ → Space n → ℝ := fun s z => x s z-M*g s z
  have hf := polynomialEval_memLp_two hμ.logConcave p
  have hf2 := polynomialEval_square_memLp hμ.logConcave p
  have hx : ContDiffAt ℝ (⊤ : ℕ∞) (x 0) 0 := by
    unfold x covarianceEnergy
    simpa only [Finset.sum_apply] using ContDiffAt.sum (s:=Finset.Icc 2 N) (fun d hd =>
      (contDiffAt_const.mul (contDiffAt_actualCovarianceAppellEnergy_theta hμ hf d) :
        ContDiffAt ℝ (⊤ : ℕ∞)
          (fun z => (w d)*actualCovarianceAppellEnergy
            (actualDampedTiltLaw (μ:Measure (Space n)) z 0) (polynomialEval p) d) 0))
  have hxs : DifferentiableWithinAt ℝ (fun s => x s 0) (Ici 0) 0 := by
    have hds (d : ℕ) (_hd : d∈Finset.Icc 2 N) : DifferentiableWithinAt ℝ
        (fun s => (w d)*actualCovarianceAppellEnergy
          (actualDampedTiltLaw (μ:Measure (Space n)) 0 s) (polynomialEval p) d) (Ici 0) 0 :=
      (differentiableWithinAt_actualCovarianceAppellEnergy_damping hμ hf d).const_mul _
    unfold x covarianceEnergy
    convert DifferentiableWithinAt.sum hds using 1
    ext s
    simp
  have hg := contDiffAt_actualTestL2Field_theta hμ.logConcave hf2
  have hgs := differentiableWithinAt_actualTestL2Field_damping hμ.logConcave hf2
  have hzero : H 0 0=0 := by
    dsimp [H,x,g]
    rw [actualDampedTiltLaw_zero_damping,exponentialTilt_zero,
      covarianceEnergy_isotropic hμ.isotropic,actualTestL2Field_zero,heq]
    ring
  obtain ⟨r,hr,hm⟩ := hfamily
  have hθ : IsLocalMax (H 0) 0 := by
    have hb : ∀ᶠ z : Space n in 𝓝 0,z∈ball 0 r :=
      isOpen_ball.mem_nhds (mem_ball_self hr)
    filter_upwards [hb] with z hz
    rw [hzero]
    have hz' : ‖z‖ ≤ r := (by simpa only [mem_ball,dist_zero_right] using hz : ‖z‖<r).le
    exact sub_nonpos.mpr (hm z hz' 0 le_rfl)
  have hs : IsLocalMaxOn (fun s => H s 0) (Ici 0) 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hzero]
    exact sub_nonpos.mpr (hm 0 (by simpa using hr.le) s hs)
  have hmax := localHeatGenerator_nonpos_of_localMax (hx.sub (contDiffAt_const.mul hg)) hθ hs
    (fun i : Fin n => EuclideanSpace.single i 1)
  have he := localHeatGenerator_linear_combination (x:=x) (y:=fun _ _ => (0:ℝ)) (g:=g)
    hx contDiffAt_const hg hxs (differentiableWithinAt_const 0) hgs (fun i : Fin n => EuclideanSpace.single i 1) M 0
  have hGg : localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) g=0 :=
    localHeatGenerator_actualTestL2Field hμ.logConcave hμ.isotropic hf2
  have hGx : localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) x=
      heatGenerator (μ : Measure (Space n)) (polynomialEval p) w N :=
    heatGenerator_eq hμ hf w
  have he' : localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) H=
      localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) x-
        M*localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) g := by
    simpa [H] using he
  rw [he',hGg,hGx] at hmax
  simpa using hmax

theorem heatGenerator_congr_ae {n : ℕ} {μ : Measure (Space n)}
    {f g : Space n → ℝ} (hfg : f =ᵐ[μ] g) (w : ℕ → ℝ) (N : ℕ) :
    heatGenerator μ f w N=heatGenerator μ g w N := by
  unfold heatGenerator
  exact Finset.sum_congr rfl fun d hd => congrArg (_ * ·)
    (actualAppellEnergyHeatGenerator_congr_ae hfg d)

section Centering
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem energy_sub_const (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (c : ℝ) (w : ℕ → ℝ) (N : ℕ) :
    energy μ (fun x => f x-c) w N=
      energy μ f w N := by
  unfold energy
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  unfold actualAppellEnergy
  apply Finset.sum_congr rfl
  intro a ha
  rw [actualAppellCoefficient_sub_const hLC hf c (by have := (Finset.mem_Icc.mp hd).1; omega)]

theorem pairing_oneLp (hLC : measureLogConcave μ)
    (f : Lp ℝ 2 μ) (w : ℕ → ℝ) (N : ℕ) :
    pairing f (CenteredL2.oneLp μ) w N=0 := by
  classical
  unfold pairing
  apply Finset.sum_eq_zero
  intro d hd
  have he : fullClassAppellTensor d (CenteredL2.oneLp μ)=0 := by
    apply PiLp.ext
    intro a
    change actualAppellCoefficient μ (CenteredL2.oneLp μ) d a=0
    rw [actualAppellCoefficient_congr_ae (CenteredL2.oneLp_ae μ)]
    exact actualAppellCoefficient_const_fullClass hLC 1
      (by have := (Finset.mem_Icc.mp hd).1; omega) a
  rw [he,inner_zero_right,mul_zero]

theorem maximum_mean_zero (hLC : measureLogConcave μ)
    (f : Lp ℝ 2 μ) {w : ℕ → ℝ} {M : ℝ} {N : ℕ} (hM : 0<M)
    (hstat : ∀ ell : Lp ℝ 2 μ,pairing f ell w N=M*inner ℝ f ell) :
    (∫ x,f x ∂μ)=0 := by
  have hs := hstat (CenteredL2.oneLp μ)
  rw [pairing_oneLp hLC,real_inner_comm,
    CenteredL2.inner_oneLp] at hs
  exact (mul_eq_zero.mp hs.symm).resolve_left (ne_of_gt hM)

theorem global_variance_bound (hLC : measureLogConcave μ)
    {w : ℕ → ℝ} {M : ℝ} {N : ℕ}
    (hglobal : ∀ g : Lp ℝ 2 μ,energy μ g w N ≤ M*‖g‖^2)
    (f : Lp ℝ 2 μ) :
    energy μ f w N ≤ M*(‖f‖^2-(∫ x,f x ∂μ)^2) := by
  have he : energy μ (CenteredL2.center μ f) w N=
      energy μ f w N := by
    rw [energy_congr_ae (CenteredL2.center_ae μ f)]
    exact energy_sub_const hLC (Lp.memLp f) _ w N
  have hb := hglobal (CenteredL2.center μ f)
  rw [he,CenteredL2.norm_center_sq] at hb
  exact hb

end Centering

theorem tilt_family_variance_bound {n N : ℕ} {w : ℕ → ℝ}
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ)
    (hglobal : ∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν : Measure (Space n)))
      (g : Lp ℝ 2 (ν : Measure (Space n))),
      energy (ν : Measure (Space n)) g w N ≤ M*‖g‖^2) :
    ∃ r : ℝ, 0<r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      covarianceEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
        (polynomialEval p) w N ≤
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
  have hm := global_variance_bound hadm.logConcave (hglobal ν hadm) g
  change energy
    (whitenedMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s)) g w N ≤ M*(‖g‖^2-
      (∫ x,g x ∂whitenedMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s))^2) at hm
  rw [energy_congr_ae hg,
    covarianceEnergy_whitening hLC hpos hf,hn,hmean] at hm
  exact hm

theorem polynomial_centered_heat_nonpos {n N : ℕ} {w : ℕ → ℝ}
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ)
    (hmean : (∫ x,polynomialEval p x ∂(μ : Measure (Space n)))=0)
    (heq : energy (μ : Measure (Space n)) (polynomialEval p) w N=
      M*(∫ x,(polynomialEval p x)^2 ∂(μ : Measure (Space n))))
    (hfamily : ∃ r : ℝ, 0<r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      covarianceEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
        (polynomialEval p) w N ≤
      M*((∫ x,(polynomialEval p x)^2 ∂actualDampedTiltLaw (μ : Measure (Space n)) z s)-
        actualCovarianceAppellEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
          (polynomialEval p) 0)) :
    heatGenerator (μ : Measure (Space n)) (polynomialEval p) w N+
      M*actualAppellEnergy (μ : Measure (Space n)) (polynomialEval p) 1 ≤ 0 := by
  let x : ℝ → Space n → ℝ := fun s z => covarianceEnergy
    (actualDampedTiltLaw (μ : Measure (Space n)) z s) (polynomialEval p) w N
  let g := actualTestL2Field (μ : Measure (Space n)) (polynomialEval p)
  let y : ℝ → Space n → ℝ := fun s z => actualCovarianceAppellEnergy
    (actualDampedTiltLaw (μ : Measure (Space n)) z s) (polynomialEval p) 0
  let H : ℝ → Space n → ℝ := fun s z => x s z-M*g s z-(-M)*y s z
  have hf := polynomialEval_memLp_two hμ.logConcave p
  have hf2 := polynomialEval_square_memLp hμ.logConcave p
  have hx : ContDiffAt ℝ (⊤ : ℕ∞) (x 0) 0 := by
    unfold x covarianceEnergy
    simpa only [Finset.sum_apply] using ContDiffAt.sum (s:=Finset.Icc 2 N) (fun d hd =>
      (contDiffAt_const.mul (contDiffAt_actualCovarianceAppellEnergy_theta hμ hf d) :
        ContDiffAt ℝ (⊤ : ℕ∞)
          (fun z => (w d)*actualCovarianceAppellEnergy
            (actualDampedTiltLaw (μ:Measure (Space n)) z 0) (polynomialEval p) d) 0))
  have hxs : DifferentiableWithinAt ℝ (fun s => x s 0) (Ici 0) 0 := by
    have hds (d : ℕ) (_hd : d∈Finset.Icc 2 N) : DifferentiableWithinAt ℝ
        (fun s => (w d)*actualCovarianceAppellEnergy
          (actualDampedTiltLaw (μ:Measure (Space n)) 0 s) (polynomialEval p) d) (Ici 0) 0 :=
      (differentiableWithinAt_actualCovarianceAppellEnergy_damping hμ hf d).const_mul _
    unfold x covarianceEnergy
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
      covarianceEnergy_isotropic hμ.isotropic,actualTestL2Field_zero,heq,
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
      heatGenerator (μ : Measure (Space n)) (polynomialEval p) w N :=
    heatGenerator_eq hμ hf w
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

theorem exists_centered_maximum_energy_inequality {n N : ℕ} (w : ℕ → ℝ) (hw : ∀ d, 2 ≤ d → 0 ≤ w d)
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
      heatGenerator (μ : Measure (Space n)) f w N+
        M*actualAppellEnergy (μ : Measure (Space n)) f 1 ≤ 0 := by
  obtain ⟨μ,hμ,c,hunit,hglobal,hstat,hfamily⟩ := exists_both_optimalities hw hμ₀
  let f := polynomialLp hμ.logConcave (boundedDegreePolynomial c)
  let M := energy (μ : Measure (Space n)) f w N
  have hnorm : (∫ x,(polynomialEval (boundedDegreePolynomial c) x)^2 ∂(μ:Measure (Space n)))=1 := by
    rw [←polynomialLp_norm_sq hμ.logConcave,hunit]
    norm_num
  have heq : energy (μ:Measure (Space n))
      (polynomialEval (boundedDegreePolynomial c)) w N=M*
        (∫ x,(polynomialEval (boundedDegreePolynomial c) x)^2 ∂(μ:Measure (Space n))) := by
    rw [hnorm,mul_one]
    exact (energy_polynomialLp hμ.logConcave _ w N).symm
  refine ⟨μ,hμ,c,hunit,hglobal,hstat,?_⟩
  have hM : 0 ≤ M := energy_nonneg _ f w hw N
  rcases eq_or_lt_of_le hM with hzero | hpos
  · have hg := polynomial_heat_nonpos hμ (boundedDegreePolynomial c) M heq hfamily
    rw [←heatGenerator_congr_ae
      (polynomialLp_coe hμ.logConcave (boundedDegreePolynomial c))] at hg
    change heatGenerator (μ:Measure (Space n)) f w N+
      M*actualAppellEnergy (μ:Measure (Space n)) f 1≤0
    rw [←hzero,zero_mul,add_zero]
    exact hg
  · have hmean := maximum_mean_zero hμ.logConcave f hpos hstat
    have hrawmean : (∫ x,polynomialEval (boundedDegreePolynomial c) x ∂(μ:Measure (Space n)))=0 := by
      rw [←integral_congr_ae (polynomialLp_coe hμ.logConcave (boundedDegreePolynomial c))]
      exact hmean
    have hv := tilt_family_variance_bound hμ (boundedDegreePolynomial c) M hglobal
    have hg := polynomial_centered_heat_nonpos hμ (boundedDegreePolynomial c)
      M hrawmean heq hv
    rwa [←heatGenerator_congr_ae
      (polynomialLp_coe hμ.logConcave (boundedDegreePolynomial c)),
      ←actualAppellEnergy_congr_ae (polynomialLp_coe hμ.logConcave (boundedDegreePolynomial c))] at hg

end KLSConstantImprovement.GeneralWeighted
#print axioms KLSConstantImprovement.GeneralWeighted.heatGenerator_eq
#print axioms KLSConstantImprovement.GeneralWeighted.polynomial_heat_nonpos
#print axioms KLSConstantImprovement.GeneralWeighted.maximum_mean_zero
#print axioms KLSConstantImprovement.GeneralWeighted.tilt_family_variance_bound
#print axioms KLSConstantImprovement.GeneralWeighted.polynomial_centered_heat_nonpos
#print axioms KLSConstantImprovement.GeneralWeighted.exists_centered_maximum_energy_inequality
