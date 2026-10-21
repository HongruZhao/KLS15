import ActualCenteredAdjacentTangent
import ActualCenteredWeightedAppellHeat

/-! The centered law-variation maximum for the genuine adjacent quotient. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25 KLS.TensorEnergy
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem actual_two_rank_polynomial_centered_heat_nonpos {n k j : ℕ}
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (p : MvPolynomial (Fin n) ℝ) (w lam : ℝ)
    (hmean : (∫ x,polynomialEval p x ∂(μ : Measure (Space n)))=0)
    (heq : actualAppellEnergy (μ : Measure (Space n)) (polynomialEval p) j+
      w*actualAppellEnergy (μ : Measure (Space n)) (polynomialEval p) k=
      lam*(∫ x,(polynomialEval p x)^2 ∂(μ : Measure (Space n))))
    (hfamily : ∃ r : ℝ, 0<r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      actualCovarianceAppellEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
        (polynomialEval p) j+w*actualCovarianceAppellEnergy
          (actualDampedTiltLaw (μ : Measure (Space n)) z s) (polynomialEval p) k ≤
      lam*((∫ x,(polynomialEval p x)^2 ∂actualDampedTiltLaw (μ : Measure (Space n)) z s)-
        actualCovarianceAppellEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
          (polynomialEval p) 0)) :
    actualAppellEnergyHeatGenerator (μ : Measure (Space n)) (polynomialEval p) j+
      w*actualAppellEnergyHeatGenerator (μ : Measure (Space n)) (polynomialEval p) k+
      lam*actualAppellEnergy (μ : Measure (Space n)) (polynomialEval p) 1 ≤ 0 := by
  let xj : ℝ → Space n → ℝ := fun s z => actualCovarianceAppellEnergy
    (actualDampedTiltLaw (μ : Measure (Space n)) z s) (polynomialEval p) j
  let xk : ℝ → Space n → ℝ := fun s z => actualCovarianceAppellEnergy
    (actualDampedTiltLaw (μ : Measure (Space n)) z s) (polynomialEval p) k
  let x : ℝ → Space n → ℝ := fun s z => xj s z+w*xk s z
  let g := actualTestL2Field (μ : Measure (Space n)) (polynomialEval p)
  let y : ℝ → Space n → ℝ := fun s z => actualCovarianceAppellEnergy
    (actualDampedTiltLaw (μ : Measure (Space n)) z s) (polynomialEval p) 0
  let H : ℝ → Space n → ℝ := fun s z => x s z-lam*g s z-(-lam)*y s z
  have hf := polynomialEval_memLp_two hμ.logConcave p
  have hf2 := polynomialEval_square_memLp hμ.logConcave p
  have hxj := contDiffAt_actualCovarianceAppellEnergy_theta hμ hf j
  have hxk := contDiffAt_actualCovarianceAppellEnergy_theta hμ hf k
  have hxjs := differentiableWithinAt_actualCovarianceAppellEnergy_damping hμ hf j
  have hxks := differentiableWithinAt_actualCovarianceAppellEnergy_damping hμ hf k
  have hx : ContDiffAt ℝ (⊤ : ℕ∞) (x 0) 0 := hxj.add (contDiffAt_const.mul hxk)
  have hxs : DifferentiableWithinAt ℝ (fun s => x s 0) (Ici 0) 0 :=
    hxjs.add (hxks.const_mul w)
  have hg := contDiffAt_actualTestL2Field_theta hμ.logConcave hf2
  have hgs := differentiableWithinAt_actualTestL2Field_damping hμ.logConcave hf2
  have hy := contDiffAt_actualCovarianceAppellEnergy_theta hμ hf 0
  have hys := differentiableWithinAt_actualCovarianceAppellEnergy_damping hμ hf 0
  have hzero : H 0 0=0 := by
    dsimp [H,x,xj,xk,g,y]
    rw [actualDampedTiltLaw_zero_damping,exponentialTilt_zero,
      actualCovarianceAppellEnergy_isotropic hμ.isotropic,actualCovarianceAppellEnergy_isotropic hμ.isotropic,actualTestL2Field_zero,heq,
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
    dsimp [H,x,xj,xk,g,y,actualTestL2Field]
    linarith
  have hs : IsLocalMaxOn (fun s => H s 0) (Ici 0) 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hzero]
    have hh := hm 0 (by simpa using hr.le) s hs
    dsimp [H,x,xj,xk,g,y,actualTestL2Field]
    linarith
  have hmax := localHeatGenerator_nonpos_of_localMax ((hx.sub (contDiffAt_const.mul hg)).sub (contDiffAt_const.mul hy)) hθ hs
    (fun i : Fin n => EuclideanSpace.single i 1)
  have he := localHeatGenerator_linear_combination (x:=x) (y:=y) (g:=g)
    hx hy hg hxs hys hgs (fun i : Fin n => EuclideanSpace.single i 1) lam (-lam)
  have hGg : localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) g=0 :=
    localHeatGenerator_actualTestL2Field hμ.logConcave hμ.isotropic hf2
  have hGx : localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) x=
      actualAppellEnergyHeatGenerator (μ : Measure (Space n)) (polynomialEval p) j+
        w*actualAppellEnergyHeatGenerator (μ : Measure (Space n)) (polynomialEval p) k := by
    rw [show x=(fun s z => xj s z+w*xk s z) from rfl,
      localHeatGenerator_add_local hxj (contDiffAt_const.mul hxk) hxjs
        (hxks.const_mul w),localHeatGenerator_const_mul_local hxk hxks]
    rfl
  have he' : localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) H=
      localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) x-
        lam*localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) g-
        (-lam)*localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) y := by
    simpa [H] using he
  have hGy : localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) y=
      actualAppellEnergy (μ : Measure (Space n)) (polynomialEval p) 1 :=
    actualAppellEnergyHeatGenerator_zero_eq_one hμ hf hmean
  rw [he',hGg,hGx,hGy] at hmax
  linarith



theorem actual_two_rank_polynomial_centered_heat_of_global_bound {n k j : ℕ}
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (hk : k≠0) (hj : j≠0) (p : MvPolynomial (Fin n) ℝ) (w lam : ℝ) (hlam : 0<lam)
    (hunit : ‖polynomialLp hμ.logConcave p‖=1)
    (heq : actualAppellEnergy (μ : Measure (Space n)) (polynomialLp hμ.logConcave p) j+
      w*actualAppellEnergy (μ : Measure (Space n)) (polynomialLp hμ.logConcave p) k=lam)
    (hglobal : ∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν : Measure (Space n)))
      (g : Lp ℝ 2 (ν : Measure (Space n))),
      actualAppellEnergy (ν : Measure (Space n)) g j+w*actualAppellEnergy (ν : Measure (Space n)) g k
        ≤lam*‖g‖^2) :
    actualAppellEnergyHeatGenerator (μ : Measure (Space n)) (polynomialLp hμ.logConcave p) j+
      w*actualAppellEnergyHeatGenerator (μ : Measure (Space n)) (polynomialLp hμ.logConcave p) k+
      lam*actualAppellEnergy (μ : Measure (Space n)) (polynomialLp hμ.logConcave p) 1 ≤ 0 := by
  let f := polynomialLp hμ.logConcave p
  have hv := actual_two_rank_global_variance_bound hμ.logConcave hk hj w lam (hglobal μ hμ) f
  rw [heq,hunit,one_pow] at hv
  have hmean : (∫ x,f x ∂(μ:Measure (Space n)))=0 := by
    have hs : (∫ x,f x ∂(μ:Measure (Space n)))^2≤0 := by nlinarith
    exact sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))
  have hae := polynomialLp_coe hμ.logConcave p
  have hrawmean : (∫ x,polynomialEval p x ∂(μ:Measure (Space n)))=0 := by
    rw [←integral_congr_ae hae]
    exact hmean
  have hnorm : (∫ x,(polynomialEval p x)^2 ∂(μ:Measure (Space n)))=1 := by
    rw [←polynomialLp_norm_sq hμ.logConcave p,hunit]
    norm_num
  have hraw : actualAppellEnergy (μ:Measure (Space n)) (polynomialEval p) j+
      w*actualAppellEnergy (μ:Measure (Space n)) (polynomialEval p) k=
      lam*(∫ x,(polynomialEval p x)^2 ∂(μ:Measure (Space n))) := by
    rw [←actualAppellEnergy_congr_ae hae,←actualAppellEnergy_congr_ae hae,hnorm,mul_one]
    exact heq
  have hfam := actual_two_rank_tilt_family_variance_bound hμ hk hj p w lam hglobal
  have hh := actual_two_rank_polynomial_centered_heat_nonpos hμ p w lam hrawmean hraw hfam
  rwa [←actualAppellEnergyHeatGenerator_congr_ae hae,
    ←actualAppellEnergyHeatGenerator_congr_ae hae,←actualAppellEnergy_congr_ae hae] at hh

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_two_rank_polynomial_centered_heat_nonpos

#print axioms KLS.DeterministicBridgeNext.actual_two_rank_polynomial_centered_heat_of_global_bound
