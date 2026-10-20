import Mathlib

/-! Positive finite-head Bellman payments. These scalar lemmas keep each
finite weight separate from the later tail floor. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.PositiveFiniteHeadBellman
set_option maxHeartbeats 2000000

structure Affine where
  slope : ℝ
  intercept : ℝ

def Affine.eval (L : Affine) (r : ℝ) : ℝ := L.slope*r+L.intercept
def Affine.positive (L : Affine) (r : ℝ) : ℝ := max 0 (L.eval r)

theorem Affine.positive_nonneg (L : Affine) (r : ℝ) : 0 ≤ L.positive r :=
  le_max_left _ _

theorem Affine.positive_mono (L : Affine) (ha : 0 ≤ L.slope)
    {r s : ℝ} (hrs : r ≤ s) : L.positive r ≤ L.positive s := by
  apply max_le_max_left
  dsimp only [Affine.eval]
  exact add_le_add (mul_le_mul_of_nonneg_left hrs ha) (le_refl _)

theorem Affine.positive_zero (L : Affine) (ha : 0 ≤ L.slope)
    (h1 : L.eval 1 ≤ 0) {r : ℝ} (hr : r ≤ 1) : L.positive r=0 := by
  have h : L.eval r ≤ L.eval 1 := by
    dsimp only [Affine.eval]
    exact add_le_add (mul_le_mul_of_nonneg_left hr ha) (le_refl _)
  exact max_eq_left (h.trans h1)

theorem Affine.product_mono (L : Affine) (ha : 0 ≤ L.slope)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    r*L.positive r ≤ s*L.positive s := by
  exact mul_le_mul hrs (L.positive_mono ha hrs) (L.positive_nonneg r) (hr.trans hrs)

/-- The supporting polynomial identities provide the stage inequality.
No ordering between a finite weight and a tail floor is required. -/
structure StageCertificate (w upper : ℝ) (lower : ℝ → ℝ)
    (current next : Affine) : Prop where
  weight_nonneg : 0 ≤ w
  current_slope_nonneg : 0 ≤ current.slope
  next_slope_nonneg : 0 ≤ next.slope
  current_at_one : current.eval 1 ≤ 0
  next_at_one : next.eval 1 ≤ 0
  stage : ∀ r, 1 ≤ r → r ≤ upper → ∀ s,
    1 ≤ s → lower r ≤ s → s ≤ r →
    current.eval r ≤ w*(r-s)+s*next.positive s

theorem transition_payment {w upper : ℝ} {lower : ℝ → ℝ}
    {current next : Affine} (h : StageCertificate w upper lower current next)
    {z r s d : ℝ} (hz : 0 ≤ z) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hd : 0 ≤ d) (hu : r ≤ upper) (hdrop : r-s ≤ d)
    (hlr : lower r ≤ r) (hls : lower r ≤ s) :
    z*current.positive r ≤ w*(z*d)+(z*s)*next.positive s := by
  have hwd : 0 ≤ w*d := mul_nonneg h.weight_nonneg hd
  have hsnext : 0 ≤ s*next.positive s := mul_nonneg hs (next.positive_nonneg s)
  have hbound : current.positive r ≤ w*d+s*next.positive s := by
    by_cases hr1 : r ≤ 1
    · rw [current.positive_zero h.current_slope_nonneg h.current_at_one hr1]
      exact add_nonneg hwd hsnext
    have hr1' : 1 ≤ r := (lt_of_not_ge hr1).le
    by_cases hs1 : s ≤ 1
    · have he := h.stage r hr1' hu 1 (le_refl _) (hls.trans hs1) hr1'
      rw [next.positive_zero h.next_slope_nonneg h.next_at_one (le_refl _),mul_zero,add_zero] at he
      have hrd : r-1 ≤ d := by linarith
      have he' : current.eval r ≤ w*d := he.trans
        (mul_le_mul_of_nonneg_left hrd h.weight_nonneg)
      have hp : current.positive r ≤ w*d := max_le hwd he'
      exact hp.trans (le_add_of_nonneg_right hsnext)
    have hs1' : 1 ≤ s := (lt_of_not_ge hs1).le
    by_cases hsr : s ≤ r
    · have he := h.stage r hr1' hu s hs1' hls hsr
      have he' : current.eval r ≤ w*d+s*next.positive s := he.trans
        (add_le_add (mul_le_mul_of_nonneg_left hdrop h.weight_nonneg) (le_refl _))
      exact max_le (add_nonneg hwd hsnext) he'
    · have hrs : r ≤ s := (lt_of_not_ge hsr).le
      have he := h.stage r hr1' hu r hr1' hlr (le_refl _)
      simp only [sub_self,mul_zero,zero_add] at he
      have he' := he.trans (next.product_mono h.next_slope_nonneg hr hrs)
      have he'' : current.eval r ≤ w*d+s*next.positive s :=
        he'.trans (le_add_of_nonneg_left hwd)
      exact max_le (add_nonneg hwd hsnext) he''
  calc
    _ ≤ z*(w*d+s*next.positive s) := mul_le_mul_of_nonneg_left hbound hz
    _ = _ := by ring

theorem finite_head_payment (N : ℕ) (w c z r : ℕ → ℝ)
    (L : ℕ → Affine)
    (hstep : ∀ i, i<N →
      z i*(L i).positive (r i) ≤
        w i*c i+z (i+1)*(L (i+1)).positive (r (i+1))) :
    z 0*(L 0).positive (r 0) ≤
      (∑ i∈Finset.range N,w i*c i)+z N*(L N).positive (r N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hh := ih (fun i hi => hstep i (by omega))
    have hl := hstep N (by omega)
    rw [Finset.sum_range_succ]
    linarith

end KLSConstantImprovement.PositiveFiniteHeadBellman
#print axioms KLSConstantImprovement.PositiveFiniteHeadBellman.transition_payment
#print axioms KLSConstantImprovement.PositiveFiniteHeadBellman.finite_head_payment
