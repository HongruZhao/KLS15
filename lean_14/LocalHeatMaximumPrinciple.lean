import LocalTensorMetricGenerator
import LocalMaximumSecondDerivative

/-! A local heat maximum principle proved from the actual first and second
derivative tests. The damping direction is one-sided. -/
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {q : ℕ}

 theorem fderiv_fderiv_nonpos_of_localMax {f : E → ℝ}
    (hmax : IsLocalMax f 0) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f 0) (v : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) 0 v ≤ 0 := by
  let l : ℝ → E := fun t => t • v
  have hl (t : ℝ) : HasDerivAt l v t := by
    simpa [l] using (hasDerivAt_id t).smul_const v
  have hlim : Tendsto l (𝓝 (0 : ℝ)) (𝓝 (0 : E)) := by
    simpa [l] using (hl 0).continuousAt.tendsto
  have hmax' : IsLocalMax f (l 0) := by simpa only [l,zero_smul] using hmax
  have hlocal : IsLocalMax (fun t => f (l t)) 0 := by
    simpa only [Function.comp_def] using
      hmax'.comp_continuous (g := l) (b := (0 : ℝ)) (hl 0).continuousAt
  have hdiff := eventually_differentiableAt_of_contDiffAt hf
  have he : deriv (fun t => f (l t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => fderiv ℝ f (l t) v) := by
    filter_upwards [hlim.eventually hdiff] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hl t)).deriv
  have hdpath : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun t => f (l t)) t := by
    filter_upwards [hlim.eventually hdiff] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hl t)).differentiableAt
  have hs0 : HasFDerivAt (fun y => fderiv ℝ f y v)
      (fderiv ℝ (fun y => fderiv ℝ f y v) 0) (l 0) := by
    simpa only [l,zero_smul] using
      (differentiableAt_directional_of_contDiffAt hf v).hasFDerivAt
  have hs := hs0.comp_hasDerivAt (0 : ℝ) (hl 0)
  have hs' : HasDerivAt (deriv (fun t => f (l t)))
      (fderiv ℝ (fun y => fderiv ℝ f y v) 0 v) 0 := by
    simpa only [l,zero_smul] using hs.congr_of_eventuallyEq he
  exact second_derivative_nonpos_of_localMax hlocal hdpath hs'

 theorem derivWithin_nonpos_of_localMaxOn_Ici {f : ℝ → ℝ}
    (hmax : IsLocalMaxOn f (Ici 0) 0) : derivWithin f (Ici 0) 0 ≤ 0 := by
  have hc : (1 : ℝ) ∈ posTangentConeAt (Ici 0) 0 := by
    rw [one_mem_posTangentConeAt_iff_mem_closure]
    have he : Ioi (0 : ℝ) ∩ Ici 0 = Ioi 0 :=
      inter_eq_left.mpr (fun t ht => (show (0 : ℝ) < t from ht).le)
    rw [he,closure_Ioi]
    exact (le_refl (0 : ℝ))
  exact hmax.fderivWithin_nonpos hc

 theorem localHeatGenerator_nonpos_of_localMax
    {f : ℝ → E → ℝ} (hf : ContDiffAt ℝ (⊤ : ℕ∞) (f 0) 0)
    (hθ : IsLocalMax (f 0) 0)
    (hs : IsLocalMaxOn (fun s => f s 0) (Ici 0) 0) (σ : Fin q → E) :
    localHeatGenerator σ f ≤ 0 := by
  have hd := derivWithin_nonpos_of_localMaxOn_Ici hs
  have hsum : (∑ i, fderiv ℝ (fun y => fderiv ℝ (f 0) y (σ i)) 0 (σ i)) ≤ 0 :=
    Finset.sum_nonpos fun i _ => fderiv_fderiv_nonpos_of_localMax hθ hf (σ i)
  unfold localHeatGenerator
  simp only [smul_eq_mul]
  linarith

 theorem localHeatGenerator_linear_combination
    {x y g : ℝ → E → ℝ}
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) (x 0) 0)
    (hy : ContDiffAt ℝ (⊤ : ℕ∞) (y 0) 0)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) (g 0) 0)
    (hxs : DifferentiableWithinAt ℝ (fun s => x s 0) (Ici 0) 0)
    (hys : DifferentiableWithinAt ℝ (fun s => y s 0) (Ici 0) 0)
    (hgs : DifferentiableWithinAt ℝ (fun s => g s 0) (Ici 0) 0)
    (σ : Fin q → E) (a b : ℝ) :
    localHeatGenerator σ (fun s z => x s z-a*g s z-b*y s z) =
      localHeatGenerator σ x-a*localHeatGenerator σ g-b*localHeatGenerator σ y := by
  let V := ℝ × (ℝ × ℝ)
  let f : ℝ → E → V := fun s z => (x s z,(g s z,y s z))
  have hf : ContDiffAt ℝ (⊤ : ℕ∞) (f 0) 0 := hx.prodMk (hg.prodMk hy)
  have hfs : DifferentiableWithinAt ℝ (fun s => f s 0) (Ici 0) 0 :=
    hxs.prodMk (hgs.prodMk hys)
  let L : V →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)-
    a • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))-
    b • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  have hm := localHeatGenerator_compCLM L hf hfs σ
  have h1 := localHeatGenerator_compCLM (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) hf hfs σ
  have h2 := localHeatGenerator_compCLM
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) hf hfs σ
  have h3 := localHeatGenerator_compCLM
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) hf hfs σ
  change localHeatGenerator σ x = (localHeatGenerator σ f).1 at h1
  change localHeatGenerator σ g = (localHeatGenerator σ f).2.1 at h2
  change localHeatGenerator σ y = (localHeatGenerator σ f).2.2 at h3
  change localHeatGenerator σ (fun s z => x s z-a*g s z-b*y s z) =
    (localHeatGenerator σ f).1-a*(localHeatGenerator σ f).2.1-
      b*(localHeatGenerator σ f).2.2 at hm
  simpa only [← h1,← h2,← h3] using hm

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.localHeatGenerator_nonpos_of_localMax
#print axioms KLS.DeterministicBridgeNext.localHeatGenerator_linear_combination
