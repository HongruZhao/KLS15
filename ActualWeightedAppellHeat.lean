import ActualWeightedAppellOptimality
import ActualEnergyQuotientMaximum
import ActualAppellWeightedEnergy

/-! A true one-sided heat maximum at the actual finite weighted maximizer. -/
noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

section HeatLinearity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : ℕ}

theorem localHeatGenerator_add_local {f g : ℝ → E → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) (f 0) 0) (hg : ContDiffAt ℝ (⊤ : ℕ∞) (g 0) 0)
    (hfs : DifferentiableWithinAt ℝ (fun s => f s 0) (Ici 0) 0)
    (hgs : DifferentiableWithinAt ℝ (fun s => g s 0) (Ici 0) 0) (σ : Fin q → E) :
    localHeatGenerator σ (fun s z => f s z+g s z)=
      localHeatGenerator σ f+localHeatGenerator σ g := by
  have hm := localHeatGenerator_linear_combination (x:=f) (y:=fun _ _ => (0:ℝ)) (g:=g)
    hf contDiffAt_const hg hfs (differentiableWithinAt_const 0) hgs σ (-1) 0
  simpa using hm

theorem localHeatGenerator_const_mul_local {f : ℝ → E → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) (f 0) 0)
    (hfs : DifferentiableWithinAt ℝ (fun s => f s 0) (Ici 0) 0)
    (σ : Fin q → E) (a : ℝ) :
    localHeatGenerator σ (fun s z => a*f s z)=a*localHeatGenerator σ f := by
  have hm := localHeatGenerator_compCLM (a • ContinuousLinearMap.id ℝ ℝ) hf hfs σ
  simpa using hm

theorem localHeatGenerator_finset_sum {I : Type*} (s : Finset I) (f : I → ℝ → E → ℝ)
    (hf : ∀ i∈s, ContDiffAt ℝ (⊤ : ℕ∞) (f i 0) 0)
    (hfs : ∀ i∈s, DifferentiableWithinAt ℝ (fun t => f i t 0) (Ici 0) 0)
    (σ : Fin q → E) :
    localHeatGenerator σ (fun t z => ∑ i∈s, f i t z)=∑ i∈s,localHeatGenerator σ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [localHeatGenerator]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [localHeatGenerator_add_local (hf i (Finset.mem_insert_self _ _))
        (ContDiffAt.sum (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
        (hfs i (Finset.mem_insert_self _ _))
        (by
          convert DifferentiableWithinAt.sum (fun j hj => hfs j (Finset.mem_insert_of_mem hj)) using 1
          ext t
          simp),
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hfs j (Finset.mem_insert_of_mem hj))]
end HeatLinearity

def actualWeightedAppellHeatGenerator {n : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) (K : ℝ) (N : ℕ) : ℝ :=
  ∑ d∈Finset.Icc 2 N,(K^d*(d.factorial:ℝ)^2)⁻¹*actualAppellEnergyHeatGenerator μ f d

theorem actualWeightedAppellHeatGenerator_eq {n N : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) (K : ℝ) :
    localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1)
      (fun s z => actualWeightedCovarianceAppellEnergy (actualDampedTiltLaw μ z s) f K N)=
    actualWeightedAppellHeatGenerator μ f K N := by
  unfold actualWeightedCovarianceAppellEnergy actualWeightedAppellHeatGenerator
  rw [localHeatGenerator_finset_sum]
  · apply Finset.sum_congr rfl
    intro d hd
    exact localHeatGenerator_const_mul_local (contDiffAt_actualCovarianceAppellEnergy_theta hμ hf d)
      (differentiableWithinAt_actualCovarianceAppellEnergy_damping hμ hf d) _ _
  · intro d hd
    exact contDiffAt_const.mul (contDiffAt_actualCovarianceAppellEnergy_theta hμ hf d)
  · intro d hd
    exact (differentiableWithinAt_actualCovarianceAppellEnergy_damping hμ hf d).const_mul _

theorem actual_weighted_polynomial_heat_nonpos {n N : ℕ} {K : ℝ}
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ)
    (heq : actualWeightedAppellEnergy (μ : Measure (Space n)) (polynomialEval p) K N=
      M*(∫ x,(polynomialEval p x)^2 ∂(μ : Measure (Space n))))
    (hfamily : ∃ r : ℝ, 0<r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      actualWeightedCovarianceAppellEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
        (polynomialEval p) K N ≤
      M*(∫ x,(polynomialEval p x)^2 ∂actualDampedTiltLaw (μ : Measure (Space n)) z s)) :
    actualWeightedAppellHeatGenerator (μ : Measure (Space n)) (polynomialEval p) K N ≤ 0 := by
  let x : ℝ → Space n → ℝ := fun s z => actualWeightedCovarianceAppellEnergy
    (actualDampedTiltLaw (μ : Measure (Space n)) z s) (polynomialEval p) K N
  let g := actualTestL2Field (μ : Measure (Space n)) (polynomialEval p)
  let H : ℝ → Space n → ℝ := fun s z => x s z-M*g s z
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
  have hzero : H 0 0=0 := by
    dsimp [H,x,g]
    rw [actualDampedTiltLaw_zero_damping,exponentialTilt_zero,
      actualWeightedCovarianceAppellEnergy_isotropic hμ.isotropic,actualTestL2Field_zero,heq]
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
      actualWeightedAppellHeatGenerator (μ : Measure (Space n)) (polynomialEval p) K N :=
    actualWeightedAppellHeatGenerator_eq hμ hf K
  have he' : localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) H=
      localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) x-
        M*localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1) g := by
    simpa [H] using he
  rw [he',hGg,hGx] at hmax
  simpa using hmax

theorem actualWeightedAppellHeatGenerator_congr_ae {n : ℕ} {μ : Measure (Space n)}
    {f g : Space n → ℝ} (hfg : f =ᵐ[μ] g) (K : ℝ) (N : ℕ) :
    actualWeightedAppellHeatGenerator μ f K N=actualWeightedAppellHeatGenerator μ g K N := by
  unfold actualWeightedAppellHeatGenerator
  exact Finset.sum_congr rfl fun d hd => congrArg (_ * ·)
    (actualAppellEnergyHeatGenerator_congr_ae hfg d)

theorem exists_actual_weighted_maximum_energy_inequality {n N : ℕ} {K : ℝ} (hK : 0<K)
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
      actualWeightedAppellHeatGenerator (μ : Measure (Space n)) f K N ≤ 0 := by
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
  have hg := actual_weighted_polynomial_heat_nonpos hμ (boundedDegreePolynomial c) M heq hfamily
  refine ⟨μ,hμ,c,hunit,hglobal,hstat,?_⟩
  rwa [←actualWeightedAppellHeatGenerator_congr_ae
    (polynomialLp_coe hμ.logConcave (boundedDegreePolynomial c))] at hg

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_weighted_polynomial_heat_nonpos

#print axioms KLS.DeterministicBridgeNext.exists_actual_weighted_maximum_energy_inequality
