import Mathlib

/-! A concave barrier lies below its actual tangent, including at either
endpoint of the closed induction interval. -/
noncomputable section
open Set
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem concave_barrier_tangent {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ (Icc 0 1) φ)
    {u v d : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (hd : HasDerivAt φ d u) : φ v ≤ φ u+d*(v-u) := by
  rcases lt_trichotomy u v with huv | huv | hvu
  · have hs := hφ.slope_le_of_hasDerivAt hu hv huv hd
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr huv)).mp hs
    linarith
  · subst v
    simp
  · have hs := hφ.le_slope_of_hasDerivAt hv hu hvu hd
    rw [slope_def_field] at hs
    have hm := (le_div_iff₀ (sub_pos.mpr hvu)).mp hs
    linarith

 theorem concave_barrier_perspective_tangent {φ : ℝ → ℝ}
    (hφ : ConcaveOn ℝ (Icc 0 1) φ) {u v d h g : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v/(h*g) ∈ Icc (0 : ℝ) 1)
    (hd : HasDerivAt φ d u) (hh : 0 < h) (hg : 0 < g) :
    g*φ (v/(h*g)) ≤ (φ u-u*d)*g+(d/h)*v := by
  have ht := mul_le_mul_of_nonneg_left (concave_barrier_tangent hφ hu hv hd) hg.le
  convert ht using 1 <;> field_simp <;> ring

 theorem concave_quotient_tangent_bound {φ : ℝ → ℝ}
    (hφ : ConcaveOn ℝ (Icc 0 1) φ)
    (hφpos : ∀ v ∈ Icc (0 : ℝ) 1, 0 < φ v)
    {u d h x y g X : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : y/(h*g) ∈ Icc (0 : ℝ) 1) (hd : HasDerivAt φ d u)
    (hh : 0 < h) (hg : 0 < g) (hX : 0 ≤ X)
    (hmax : x/(g*φ (y/(h*g))) ≤ X/φ u) :
    x-(X/φ u)*(φ u-u*d)*g-(X/φ u)*(d/h)*y ≤ 0 := by
  have hp := hφpos u hu
  have hden := mul_pos hg (hφpos _ hv)
  have hb := (div_le_iff₀ hden).mp hmax
  have ht := mul_le_mul_of_nonneg_left
    (concave_barrier_perspective_tangent hφ hu hv hd hh hg)
    (div_nonneg hX hp.le)
  nlinarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.concave_quotient_tangent_bound
