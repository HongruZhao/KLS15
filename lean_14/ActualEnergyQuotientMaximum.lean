import ActualTiltInductionRatio
import ActualTestMassHeatCancellation
import LocalQuotientMaximumPrinciple

/-! Literal maximum-principle inequality for the genuine covariance Appell
energies. The test is a genuine polynomial, every law variation is the actual
damped tilt, and its whitening/induction interval are proved internally. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

 def actualAppellEnergyHeatGenerator {n : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) (d : ℕ) : ℝ :=
    localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1)
      (fun s z => actualCovarianceAppellEnergy (actualDampedTiltLaw μ z s) f d)

 theorem actual_polynomial_family_maximum_energy_inequality {n k : ℕ}
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (p : MvPolynomial (Fin n) ℝ) {h : ℝ} (hh : 0 < h) {φ : ℝ → ℝ}
    (hφ : ConcaveOn ℝ (Icc 0 1) φ)
    (hφpos : ∀ v ∈ Icc (0 : ℝ) 1, 0 < φ v)
    (hprevious : ∀ (ν : Measure (Space n)), admissibleMeasure ν → ∀ f : Space n → ℝ,
      MemLp f 2 ν → actualAppellEnergy ν f k ≤ h*(∫ x, (f x)^2 ∂ν))
    (hunit : (∫ x, (polynomialEval p x)^2 ∂μ) = 1) {d : ℝ}
    (hd : HasDerivAt φ d (actualCovarianceAppellEnergy μ (polynomialEval p) k/h))
    (hfamily : ∃ r : ℝ, 0 < r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      actualCovarianceAppellQuotient (actualDampedTiltLaw μ z s) (polynomialEval p) k h φ ≤
      actualCovarianceAppellQuotient μ (polynomialEval p) k h φ) :
    actualAppellEnergyHeatGenerator μ (polynomialEval p) (k+1)+
      actualCovarianceAppellEnergy μ (polynomialEval p) (k+1)*
        ((-d)/φ (actualCovarianceAppellEnergy μ (polynomialEval p) k/h))/h*
          actualAppellEnergyHeatGenerator μ (polynomialEval p) k ≤ 0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let f := polynomialEval p
  let x : ℝ → Space n → ℝ := fun s z => actualCovarianceAppellEnergy (actualDampedTiltLaw μ z s) f (k+1)
  let y : ℝ → Space n → ℝ := fun s z => actualCovarianceAppellEnergy (actualDampedTiltLaw μ z s) f k
  let g := actualTestL2Field μ f
  have hf : MemLp f 2 μ := polynomialEval_memLp_two hμ.logConcave p
  have hf2 : MemLp (fun a => (f a)^2) 2 μ := polynomialEval_square_memLp hμ.logConcave p
  have hzero : actualDampedTiltLaw μ 0 0 = μ := by
    rw [actualDampedTiltLaw_zero_damping,exponentialTilt_zero]
  have hx : ContDiffAt ℝ (⊤ : ℕ∞) (x 0) 0 :=
    contDiffAt_actualCovarianceAppellEnergy_theta hμ hf (k+1)
  have hy : ContDiffAt ℝ (⊤ : ℕ∞) (y 0) 0 :=
    contDiffAt_actualCovarianceAppellEnergy_theta hμ hf k
  have hg : ContDiffAt ℝ (⊤ : ℕ∞) (g 0) 0 := contDiffAt_actualTestL2Field_theta hμ.logConcave hf2
  have hxs : DifferentiableWithinAt ℝ (fun s => x s 0) (Ici 0) 0 :=
    differentiableWithinAt_actualCovarianceAppellEnergy_damping hμ hf (k+1)
  have hys : DifferentiableWithinAt ℝ (fun s => y s 0) (Ici 0) 0 :=
    differentiableWithinAt_actualCovarianceAppellEnergy_damping hμ hf k
  have hgs : DifferentiableWithinAt ℝ (fun s => g s 0) (Ici 0) 0 :=
    differentiableWithinAt_actualTestL2Field_damping hμ.logConcave hf2
  have hg0 : g 0 0 = 1 := by simpa only [g,actualTestL2Field_zero] using hunit
  have hx0 : 0 ≤ x 0 0 := by
    dsimp [x]
    rw [hzero,actualCovarianceAppellEnergy_isotropic hμ.isotropic]
    exact actualAppellEnergy_nonneg _ _ _
  have hu : y 0 0/h ∈ Icc (0 : ℝ) 1 := by
    dsimp [y]
    rw [hzero,actualCovarianceAppellEnergy_isotropic hμ.isotropic]
    have hb := hprevious μ hμ f hf
    rw [hunit,mul_one] at hb
    exact ⟨div_nonneg (actualAppellEnergy_nonneg _ _ _) hh.le,(div_le_one hh).mpr hb⟩
  have hd' : HasDerivAt φ d (y 0 0/h) := by simpa only [y,hzero] using hd
  obtain ⟨r₁,hr₁,hmax⟩ := hfamily
  obtain ⟨r₂,hr₂,hratio⟩ := exists_local_actual_damped_induction_ratio hμ p hh hprevious
  have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  have hrat : ∀ z : Space n, ‖z‖ ≤ min r₁ r₂ → ∀ s : ℝ, 0 ≤ s →
      y s z/(h*g s z) ∈ Icc (0 : ℝ) 1 := by
    intro z hz s hs
    exact hratio z (hz.trans (min_le_right _ _)) s hs
  have hmx : ∀ z : Space n, ‖z‖ ≤ min r₁ r₂ → ∀ s : ℝ, 0 ≤ s →
      x s z/(g s z*φ (y s z/(h*g s z))) ≤ x 0 0/φ (y 0 0/h) := by
    intro z hz s hs
    have hm := hmax z (hz.trans (min_le_left _ _)) s hs
    unfold actualCovarianceAppellQuotient at hm
    rw [hunit,one_mul,mul_one] at hm
    simpa only [x,y,g,actualTestL2Field,hzero] using hm
  have hGg : localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) g = 0 :=
    localHeatGenerator_actualTestL2Field hμ.logConcave hμ.isotropic hf2
  have hhgen := localHeatGenerator_quotient_maximum hx hy hg hxs hys hgs
    (fun i : Fin n => EuclideanSpace.single i 1) hh hφ hφpos hg0 hx0 hu hd' hr hrat hmx hGg
  simpa only [x,y,hzero,actualAppellEnergyHeatGenerator] using hhgen

 theorem exists_actual_joint_maximizer_energy_inequality {n k : ℕ}
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n)))
    {h : ℝ} (hh : 0 < h) {φ φ' : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc 0 1))
    (hφpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < φ u)
    (hφanti : AntitoneOn φ (Icc (0 : ℝ) 1))
    (hφconc : ConcaveOn ℝ (Icc 0 1) φ)
    (hφderiv : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' u) u)
    (hprevious : ∀ (μ : Measure (Space n)), admissibleMeasure μ → ∀ f : Space n → ℝ,
      MemLp f 2 μ → actualAppellEnergy μ f k ≤ h*(∫ x, (f x)^2 ∂μ)) :
    ∃ (μ : ProbabilityMeasure (Space n)) (hμ : admissibleMeasure (μ : Measure (Space n)))
      (c : DegreeIndex n (k+1) → ℝ),
      let f := polynomialLp hμ.logConcave (boundedDegreePolynomial c)
      ‖f‖ = 1 ∧
      (∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν : Measure (Space n)))
        (g : Lp ℝ 2 (ν : Measure (Space n))),
        coefficientQuotient (fullClassAppellLinearMap hν.logConcave k)
          (fullClassAppellLinearMap hν.logConcave (k+1)) h φ g ≤
        coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
          (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ f) ∧
      (∀ ell : Lp ℝ 2 (μ : Measure (Space n)),
        inner ℝ (fullClassAppellTensor (k+1) f) (fullClassAppellTensor (k+1) ell)+
          ‖fullClassAppellTensor (k+1) f‖^2*
            ((-φ' (‖fullClassAppellTensor k f‖^2/h))/φ (‖fullClassAppellTensor k f‖^2/h))/h*
            inner ℝ (fullClassAppellTensor k f) (fullClassAppellTensor k ell) =
        ‖fullClassAppellTensor (k+1) f‖^2*
          (1+(‖fullClassAppellTensor k f‖^2/h)*
            ((-φ' (‖fullClassAppellTensor k f‖^2/h))/φ (‖fullClassAppellTensor k f‖^2/h)))*
          inner ℝ f ell) ∧
      actualAppellEnergyHeatGenerator (μ : Measure (Space n))
          (polynomialEval (boundedDegreePolynomial c)) (k+1)+
        actualCovarianceAppellEnergy (μ : Measure (Space n))
          (polynomialEval (boundedDegreePolynomial c)) (k+1)*
          ((-φ' (actualCovarianceAppellEnergy (μ : Measure (Space n))
            (polynomialEval (boundedDegreePolynomial c)) k/h))/
            φ (actualCovarianceAppellEnergy (μ : Measure (Space n))
              (polynomialEval (boundedDegreePolynomial c)) k/h))/h*
          actualAppellEnergyHeatGenerator (μ : Measure (Space n))
            (polynomialEval (boundedDegreePolynomial c)) k ≤ 0 := by
  obtain ⟨μ,hμ,c,hunit,hmax,hstat,hfamily⟩ := exists_actual_joint_maximizer_both_optimalities
    hμ₀ hh hφ hφpos hφanti hφderiv hprevious
  have htestunit : (∫ x, (polynomialEval (boundedDegreePolynomial c) x)^2
      ∂(μ : Measure (Space n))) = 1 := by
    rw [← polynomialLp_norm_sq hμ.logConcave (boundedDegreePolynomial c),hunit]
    norm_num
  have hf := polynomialEval_memLp_two hμ.logConcave (boundedDegreePolynomial c)
  have hu : actualCovarianceAppellEnergy (μ : Measure (Space n))
      (polynomialEval (boundedDegreePolynomial c)) k/h ∈ Icc (0 : ℝ) 1 := by
    rw [actualCovarianceAppellEnergy_isotropic hμ.isotropic]
    have hb := hprevious (μ : Measure (Space n)) hμ _ hf
    rw [htestunit,mul_one] at hb
    exact ⟨div_nonneg (actualAppellEnergy_nonneg _ _ _) hh.le,(div_le_one hh).mpr hb⟩
  exact ⟨μ,hμ,c,hunit,hmax,hstat,actual_polynomial_family_maximum_energy_inequality
    hμ (boundedDegreePolynomial c) hh hφconc hφpos hprevious htestunit (hφderiv _ hu) hfamily⟩

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_polynomial_family_maximum_energy_inequality

#print axioms KLS.DeterministicBridgeNext.exists_actual_joint_maximizer_energy_inequality
