import KLS.ConvexMollifierProperties
import KLS.StrongConvexAffine
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! A concrete smooth convex barrier for a closed convex target.  The input is
the actual distance to the target.  The diagonal mollifier radius is quadratic
in the penalty index, so the penalty vanishes on the target and diverges at
every point outside it.  No smooth defining function for the target is assumed. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ContDiff
namespace KLSConstantImprovement.ActualConvexSoftBarrier405
open KLS
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem convexOn_infDist_of_closed_convex {K : Set (Space n)}
    (hK : IsClosed K) (hne : K.Nonempty) (hc : Convex ℝ K) :
    ConvexOn ℝ univ (fun x => infDist x K) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  obtain ⟨u, hu, hxu⟩ := hK.exists_infDist_eq_dist hne x
  obtain ⟨v, hv, hyv⟩ := hK.exists_infDist_eq_dist hne y
  have hm : a • u + b • v ∈ K := hc hu hv ha hb hab
  calc
    infDist (a • x + b • y) K ≤ dist (a • x + b • y) (a • u + b • v) :=
      infDist_le_dist_of_mem hm
    _ = ‖a • (x-u) + b • (y-v)‖ := by
      rw [dist_eq_norm]
      congr 1
      module
    _ ≤ ‖a • (x-u)‖ + ‖b • (y-v)‖ := norm_add_le _ _
    _ = a * infDist x K + b * infDist y K := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb,
        hxu, hyv, dist_eq_norm, dist_eq_norm]
    _ = a • infDist x K + b • infDist y K := rfl

def softBarrierIndex (j : ℕ) : ℕ := j*j + 2*j

def convexSoftBarrier (K : Set (Space n)) (j : ℕ) (x : Space n) : ℝ :=
  ((j : ℝ)+1) * mollify (softBarrierIndex j) (fun y => infDist y K) x

theorem convexSoftBarrier_smooth (K : Set (Space n)) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (convexSoftBarrier K j) :=
  contDiff_const.mul (mollify_contDiff (continuous_infDist_pt K).locallyIntegrable _)

theorem convexSoftBarrier_convex {K : Set (Space n)}
    (hK : IsClosed K) (hne : K.Nonempty) (hc : Convex ℝ K) (j : ℕ) :
    ConvexOn ℝ univ (convexSoftBarrier K j) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hh := (convexOn_mollify (continuous_infDist_pt K)
    (convexOn_infDist_of_closed_convex hK hne hc) (softBarrierIndex j)).2
      (mem_univ x) (mem_univ y) ha hb hab
  change ((j : ℝ)+1) * mollify (softBarrierIndex j) (fun z => infDist z K) (a • x+b • y) ≤
    a * (((j : ℝ)+1) * mollify (softBarrierIndex j) (fun z => infDist z K) x) +
    b * (((j : ℝ)+1) * mollify (softBarrierIndex j) (fun z => infDist z K) y)
  simp only [smul_eq_mul] at hh
  calc
    _ ≤ ((j : ℝ)+1) * (a * mollify (softBarrierIndex j) (fun z => infDist z K) x +
      b * mollify (softBarrierIndex j) (fun z => infDist z K) y) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

theorem convexSoftBarrier_nonneg (K : Set (Space n)) (j : ℕ) (x : Space n) :
    0 ≤ convexSoftBarrier K j x := by
  unfold convexSoftBarrier
  apply mul_nonneg (by positivity)
  rw [mollify_eq_integral_kernel_left]
  apply integral_nonneg
  intro y
  exact mul_nonneg ((mollifierBump n (softBarrierIndex j)).nonneg_normed y) infDist_nonneg

theorem convexSoftBarrier_error (K : Set (Space n)) (j : ℕ) (x : Space n) :
    |convexSoftBarrier K j x - ((j : ℝ)+1) * infDist x K| ≤ 2 * cutoffScale j := by
  have hh := dist_mollify_le_of_lipschitz (lipschitz_infDist_pt K) (softBarrierIndex j) x
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hh
  change |((j : ℝ)+1) * mollify (softBarrierIndex j) (fun y => infDist y K) x -
    ((j : ℝ)+1) * infDist x K| ≤ _
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (j : ℝ)+1)]
  calc
    _ ≤ ((j : ℝ)+1) * (2 * cutoffScale (softBarrierIndex j)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = 2 * cutoffScale j := by
      unfold cutoffScale softBarrierIndex
      push_cast
      field_simp
      <;> ring

theorem convexSoftBarrier_tendsto_zero {K : Set (Space n)} {x : Space n} (hx : x ∈ K) :
    Tendsto (fun j => convexSoftBarrier K j x) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => convexSoftBarrier_nonneg K j x)
    (fun j => ?_) (by simpa using cutoffScale_tendsto_zero.const_mul 2)
  have hh := convexSoftBarrier_error K j x
  simpa only [infDist_zero_of_mem hx, mul_zero, sub_zero,
    abs_of_nonneg (convexSoftBarrier_nonneg K j x)] using hh

theorem convexSoftBarrier_tendsto_atTop {K : Set (Space n)}
    (hK : IsClosed K) (hne : K.Nonempty) {x : Space n} (hx : x ∉ K) :
    Tendsto (fun j => convexSoftBarrier K j x) atTop atTop := by
  have hd : 0 < infDist x K := (hK.notMem_iff_infDist_pos hne).mp hx
  have hnat : Tendsto (fun j : ℕ => (j : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun j : ℕ => le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
      tendsto_natCast_atTop_atTop
  have hmain : Tendsto (fun j : ℕ => ((j : ℝ)+1) * infDist x K) atTop atTop :=
    hnat.atTop_mul_const hd
  have he : ∀ j : ℕ, ((j : ℝ)+1) * infDist x K - 2 ≤ convexSoftBarrier K j x := by
    intro j
    have h := (abs_le.mp (convexSoftBarrier_error K j x)).1
    have hs : cutoffScale j ≤ 1 := by
      unfold cutoffScale
      exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))])
    linarith
  apply Filter.tendsto_atTop.2
  intro r
  filter_upwards [hmain.eventually_ge_atTop (r+2)] with j hj
  linarith only [he j, hj]

theorem convexSoftBarrier_exp_tendsto (K : Set (Space n))
    (hK : IsClosed K) (hne : K.Nonempty) (x : Space n) :
    Tendsto (fun j => Real.exp (-convexSoftBarrier K j x)) atTop
      (𝓝 (K.indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : x ∈ K
  · simpa only [indicator_of_mem hx, neg_zero, Real.exp_zero, Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp (convexSoftBarrier_tendsto_zero hx).neg
  · simpa only [indicator_of_notMem hx, Function.comp_def] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (convexSoftBarrier_tendsto_atTop hK hne hx)

theorem strongConvex_add_convexSoftBarrier {K : Set (Space n)}
    (hK : IsClosed K) (hne : K.Nonempty) (hc : Convex ℝ K)
    {V : Space n → ℝ} {κ : ℝ} (hs : StrongConvexOn univ κ V) (j : ℕ) :
    StrongConvexOn univ κ (fun x => V x + convexSoftBarrier K j x) := by
  rw [strongConvexOn_iff_convex] at hs ⊢
  convert hs.add (convexSoftBarrier_convex hK hne hc j) using 1
  funext x
  dsimp only [Pi.add_apply]
  ring

end KLSConstantImprovement.ActualConvexSoftBarrier405
#print axioms KLSConstantImprovement.ActualConvexSoftBarrier405.convexOn_infDist_of_closed_convex
#print axioms KLSConstantImprovement.ActualConvexSoftBarrier405.convexSoftBarrier_smooth
#print axioms KLSConstantImprovement.ActualConvexSoftBarrier405.convexSoftBarrier_convex
#print axioms KLSConstantImprovement.ActualConvexSoftBarrier405.convexSoftBarrier_error
#print axioms KLSConstantImprovement.ActualConvexSoftBarrier405.convexSoftBarrier_exp_tendsto
#print axioms KLSConstantImprovement.ActualConvexSoftBarrier405.strongConvex_add_convexSoftBarrier
