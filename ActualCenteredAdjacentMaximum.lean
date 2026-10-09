import ActualCenteredAdjacentTerminal

/-! The genuine global quotient maximum yields a variance-centered heat
inequality. Positive top energy is only used to infer that its mass multiplier
is positive; a zero top energy needs no excess contradiction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped ContDiff Topology
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_adjacent_quotient_centered_heat_nonpos {n k : ℕ}
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (hk : 1≤k) (p : MvPolynomial (Fin n) ℝ) {h : ℝ} (hh : 0<h)
    (hunit : ‖polynomialLp hμ.logConcave p‖=1)
    {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ (Icc 0 1) φ)
    (hφpos : ∀ u∈Icc (0:ℝ) 1,0<φ u)
    (hprevious : ∀ (ν : Measure (Space n)),admissibleMeasure ν → ∀ g : Space n → ℝ,
      MemLp g 2 ν → actualAppellEnergy ν g k≤h*(∫ x,(g x)^2 ∂ν))
    {d : ℝ} (hd : HasDerivAt φ d
      (actualAppellEnergy (μ:Measure (Space n)) (polynomialLp hμ.logConcave p) k/h))
    (hX : 0<actualAppellEnergy (μ:Measure (Space n)) (polynomialLp hμ.logConcave p) (k+1))
    (hq : 0≤-d/φ (actualAppellEnergy (μ:Measure (Space n)) (polynomialLp hμ.logConcave p) k/h))
    (hmax : ∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν:Measure (Space n)))
      (g : Lp ℝ 2 (ν:Measure (Space n))),
      coefficientQuotient (fullClassAppellLinearMap hν.logConcave k)
        (fullClassAppellLinearMap hν.logConcave (k+1)) h φ g≤
      coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
        (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ (polynomialLp hμ.logConcave p)) :
    let f := polynomialLp hμ.logConcave p
    let X := actualAppellEnergy (μ:Measure (Space n)) f (k+1)
    let u := actualAppellEnergy (μ:Measure (Space n)) f k/h
    let q := -d/φ u
    actualAppellEnergyHeatGenerator (μ:Measure (Space n)) f (k+1)+
      X*q/h*actualAppellEnergyHeatGenerator (μ:Measure (Space n)) f k+
      X*(1+u*q)*actualAppellEnergy (μ:Measure (Space n)) f 1≤0 := by
  let f := polynomialLp hμ.logConcave p
  let X := actualAppellEnergy (μ:Measure (Space n)) f (k+1)
  let Y := actualAppellEnergy (μ:Measure (Space n)) f k
  let u := Y/h
  let q := -d/φ u
  have hfunit : ‖f‖=1 := hunit
  have hfne : f≠0 := by
    intro hz
    rw [hz,norm_zero] at hfunit
    norm_num at hfunit
  have hu : u∈Icc (0:ℝ) 1 := by
    have hu' := actualAppell_ratio_mem_Icc hμ hh hprevious f hfne
    simpa only [hfunit,one_pow,mul_one,←actualAppellEnergy_eq_norm_sq] using hu'
  have hpos := hφpos u hu
  have hd' : HasDerivAt φ d (‖fullClassAppellTensor k f‖^2/h) := by
    simpa only [←actualAppellEnergy_eq_norm_sq] using hd
  have hb := actual_joint_all_law_tangent_bound hμ f hh hunit hφ hφpos hprevious hd' hmax
  simp only [←actualAppellEnergy_eq_norm_sq] at hb
  change ∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν:Measure (Space n)))
    (g : Lp ℝ 2 (ν:Measure (Space n))),
    actualAppellEnergy (ν:Measure (Space n)) g (k+1)+
      (-(X/φ u)*(d/h))*actualAppellEnergy (ν:Measure (Space n)) g k≤
      ((X/φ u)*(φ u-u*d))*‖g‖^2 at hb
  have hw : -(X/φ u)*(d/h)=X*q/h := by dsimp only [q]; ring
  have hlam : (X/φ u)*(φ u-u*d)=X*(1+u*q) := by
    dsimp only [q]
    field_simp [hpos.ne']
    ring
  rw [hw,hlam] at hb
  have hp : 0<X*(1+u*q) := mul_pos hX (by
    have hq' : 0≤q := hq
    have huu : 0≤u := hu.1
    linarith [mul_nonneg huu hq'])
  have heq : actualAppellEnergy (μ:Measure (Space n)) f (k+1)+
      (X*q/h)*actualAppellEnergy (μ:Measure (Space n)) f k=X*(1+u*q) := by
    dsimp only [X,u,Y]
    ring
  exact actual_two_rank_polynomial_centered_heat_of_global_bound hμ (by omega) (by omega)
    p (X*q/h) (X*(1+u*q)) hp hunit heq hb

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_adjacent_quotient_centered_heat_nonpos
