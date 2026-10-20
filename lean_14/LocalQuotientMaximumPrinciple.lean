import LocalHeatMaximumPrinciple
import ConcaveBarrierTangent

/-! The quotient maximum is converted to a tangent-supported linear maximum.
This derives the energy inequality without assuming a maximum principle or
any quotient second-derivative formula. -/
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {q : ℕ}

 theorem localHeatGenerator_quotient_maximum
    {x y g : ℝ → E → ℝ}
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) (x 0) 0)
    (hy : ContDiffAt ℝ (⊤ : ℕ∞) (y 0) 0)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) (g 0) 0)
    (hxs : DifferentiableWithinAt ℝ (fun s => x s 0) (Ici 0) 0)
    (hys : DifferentiableWithinAt ℝ (fun s => y s 0) (Ici 0) 0)
    (hgs : DifferentiableWithinAt ℝ (fun s => g s 0) (Ici 0) 0)
    (σ : Fin q → E) {h : ℝ} (hh : 0 < h) {φ : ℝ → ℝ}
    (hφ : ConcaveOn ℝ (Icc 0 1) φ)
    (hφpos : ∀ v ∈ Icc (0 : ℝ) 1, 0 < φ v)
    (hg0 : g 0 0 = 1) (hx0 : 0 ≤ x 0 0)
    (hu : y 0 0/h ∈ Icc (0 : ℝ) 1) {d : ℝ}
    (hd : HasDerivAt φ d (y 0 0/h))
    {r : ℝ} (hr : 0 < r)
    (hratio : ∀ z : E, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      y s z/(h*g s z) ∈ Icc (0 : ℝ) 1)
    (hmax : ∀ z : E, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      x s z/(g s z*φ (y s z/(h*g s z))) ≤ x 0 0/φ (y 0 0/h))
    (hGg : localHeatGenerator σ g = 0) :
    localHeatGenerator σ x+x 0 0*((-d)/φ (y 0 0/h))/h*localHeatGenerator σ y ≤ 0 := by
  let u := y 0 0/h
  let X := x 0 0
  let a := (X/φ u)*(φ u-u*d)
  let b := (X/φ u)*(d/h)
  let H : ℝ → E → ℝ := fun s z => x s z-a*g s z-b*y s z
  have hp : φ u ≠ 0 := (hφpos u hu).ne'
  have hpu : φ (y 0 0/h) ≠ 0 := by simpa only [u] using hp
  have hH0 : H 0 0 = 0 := by
    dsimp [H,a,b,X,u]
    rw [hg0]
    field_simp [hh.ne',hpu]
    <;> ring
  have hbound (s : ℝ) (hs : 0 ≤ s) (z : E) (hz : ‖z‖ ≤ r) (hgp : 0 < g s z) :
      H s z ≤ 0 := by
    exact concave_quotient_tangent_bound hφ hφpos hu (hratio z hz s hs) hd hh hgp hx0
      (hmax z hz s hs)
  have hθpos : ∀ᶠ z in 𝓝 (0 : E), 0 < g 0 z :=
    hg.continuousAt.eventually (Ioi_mem_nhds (by simpa [hg0]))
  have hspos : ∀ᶠ s in 𝓝[Ici 0] (0 : ℝ), 0 < g s 0 :=
    hgs.continuousWithinAt.eventually (Ioi_mem_nhds (by simpa [hg0]))
  have hθmax : IsLocalMax (H 0) 0 := by
    change ∀ᶠ z in 𝓝 (0 : E), H 0 z ≤ H 0 0
    rw [hH0]
    filter_upwards [hθpos,closedBall_mem_nhds (0 : E) hr] with z hzp hzr
    exact hbound 0 le_rfl z (by simpa only [mem_closedBall,dist_zero_right] using hzr) hzp
  have hsmax : IsLocalMaxOn (fun s => H s 0) (Ici 0) 0 := by
    change ∀ᶠ s in 𝓝[Ici 0] (0 : ℝ), H s 0 ≤ H 0 0
    rw [hH0]
    filter_upwards [hspos,self_mem_nhdsWithin] with s hsp hs
    exact hbound s hs 0 (by simpa using hr.le) hsp
  have hH : ContDiffAt ℝ (⊤ : ℕ∞) (H 0) 0 :=
    (hx.sub (contDiffAt_const.mul hg)).sub (contDiffAt_const.mul hy)
  have hG := localHeatGenerator_nonpos_of_localMax hH hθmax hsmax σ
  change localHeatGenerator σ (fun s z => x s z-a*g s z-b*y s z) ≤ 0 at hG
  rw [localHeatGenerator_linear_combination hx hy hg hxs hys hgs σ a b,hGg,mul_zero,
    sub_zero] at hG
  convert hG using 1 <;> dsimp [b,X,u] <;> ring

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.localHeatGenerator_quotient_maximum
