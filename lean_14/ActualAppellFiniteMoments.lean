import BoundedDegreePolynomialPairs
import ActualLawTiltSmooth
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Exact finite raw-moment formula for genuine Appell derivatives. The formula
is obtained from the actual normalized Laplace expectation by Faà di Bruno,
not posited as an independent coefficient sequence. -/
noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 def scalarRatio (p : ℝ × ℝ) : ℝ := p.1/p.2

 theorem scalarRatio_contDiffAt (a b : ℝ) (hb : b ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) scalarRatio (a,b) := by
  exact contDiffAt_fst.div contDiffAt_snd hb

 def rawLaplacePair {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ)
    (z : Space n) : ℝ × ℝ :=
  (tiltNumerator μ (fun _ => 0) f z,
    tiltNumerator μ (fun _ => 0) (fun _ => 1) z)

 theorem rawLaplacePair_zero {n : ℕ} (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (f : Space n → ℝ) : rawLaplacePair μ f 0 = (∫ x, f x ∂μ,1) := by
  simp only [rawLaplacePair,tiltNumerator,inner_zero_left,zero_add,Real.exp_zero,mul_one]
  simp

 theorem normalized_tilt_average_eq_ratio_comp {n : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) :
    (fun z => ∫ x, f x ∂exponentialTilt μ z) = scalarRatio ∘ rawLaplacePair μ f := by
  funext z
  change tiltAverage μ (fun x => inner ℝ z x) f = _
  rw [tiltAverage_eq_ratio]
  simp only [scalarRatio,rawLaplacePair,Function.comp_apply,tiltNumerator,
    tiltPartition,zero_add,one_mul]

 theorem rawLaplacePair_contDiffAt {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (rawLaplacePair μ f) 0 := by
  obtain ⟨r,hr,hfD,h1D⟩ := exists_common_local_exponential_domains hLC hf
  have h0 : (0 : Space n) ∈ ball 0 r := by simpa using hr
  exact ((contDiffOn_tiltNumerator_of_localNormExponentialDomain hfD).contDiffAt
    (isOpen_ball.mem_nhds h0)).prodMk
    ((contDiffOn_tiltNumerator_of_localNormExponentialDomain h1D).contDiffAt
    (isOpen_ball.mem_nhds h0))

 theorem iteratedFDeriv_rawLaplacePair_moments {n d : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (v : Fin d → Space n) :
    iteratedFDeriv ℝ d (rawLaplacePair μ f) 0 v =
    (∫ x, f x*(∏ j, inner ℝ x (v j)) ∂μ,
      ∫ x, (∏ j, inner ℝ x (v j)) ∂μ) := by
  obtain ⟨r,hr,hfD,h1D⟩ := exists_common_local_exponential_domains hLC hf
  have h0 : (0 : Space n) ∈ ball 0 r := by simpa using hr
  have hN := (contDiffOn_tiltNumerator_of_localNormExponentialDomain hfD).contDiffAt
    (isOpen_ball.mem_nhds h0)
  have hZ := (contDiffOn_tiltNumerator_of_localNormExponentialDomain h1D).contDiffAt
    (isOpen_ball.mem_nhds h0)
  unfold rawLaplacePair
  rw [iteratedFDeriv_prodMk hN hZ (by simp)]
  change (iteratedFDeriv ℝ d (tiltNumerator μ (fun _ => 0) f) 0 v,
    iteratedFDeriv ℝ d (tiltNumerator μ (fun _ => 0) (fun _ => 1)) 0 v) = _
  rw [iteratedFDeriv_tiltNumerator_moment_of_local hfD (by simpa using hr),
    iteratedFDeriv_tiltNumerator_moment_of_local h1D (by simpa using hr)]
  simp only [inner_zero_left,Real.exp_zero,mul_one,one_mul]

/-- Every mixed actual Appell derivative is an explicit finite expression in
raw moments up to its order (and f-weighted moments up to its order). -/
 theorem actualAppell_mixed_finite_moment_formula {n d : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (v : Fin d → Space n) :
    iteratedFDeriv ℝ d (fun z => ∫ x, f x ∂exponentialTilt μ z) 0 v =
    ∑ c : OrderedFinpartition d,
      iteratedFDeriv ℝ c.length scalarRatio (∫ x, f x ∂μ,1)
        (fun j => (∫ x, f x*(∏ i, inner ℝ x (v (c.emb j i))) ∂μ,
          ∫ x, (∏ i, inner ℝ x (v (c.emb j i))) ∂μ)) := by
  have hPair := rawLaplacePair_contDiffAt hLC hf
  have hRatio : ContDiffAt ℝ (⊤ : ℕ∞) scalarRatio (rawLaplacePair μ f 0) := by
    rw [rawLaplacePair_zero]
    exact scalarRatio_contDiffAt _ _ one_ne_zero
  rw [normalized_tilt_average_eq_ratio_comp,iteratedFDeriv_comp hRatio hPair (by simp)]
  simp only [FormalMultilinearSeries.taylorComp,ContinuousMultilinearMap.sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,ftaylorSeries,
    OrderedFinpartition.applyOrderedFinpartition_apply,rawLaplacePair_zero]
  apply Finset.sum_congr rfl
  intro c hc
  congr 1
  funext j
  exact iteratedFDeriv_rawLaplacePair_moments hLC hf _

 theorem actualAppellCoefficient_finite_moment_formula {n d : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (a : Fin d → Fin n) :
    actualAppellCoefficient μ f d a =
    ∑ c : OrderedFinpartition d,
      iteratedFDeriv ℝ c.length scalarRatio (∫ x, f x ∂μ,1)
        (fun j => (∫ x, f x*(∏ i, x (a (c.emb j i))) ∂μ,
          ∫ x, (∏ i, x (a (c.emb j i))) ∂μ)) := by
  unfold actualAppellCoefficient
  rw [actualAppell_mixed_finite_moment_formula hLC hf]
  simp only [EuclideanSpace.inner_single_right]
  simp

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualAppell_mixed_finite_moment_formula
#print axioms KLS.DeterministicBridgeNext.actualAppellCoefficient_finite_moment_formula
