import KLSConstantImprovement.ActualSourceRegularizedWeakCompactness405

/-! Coordinate tests and exact coordinate equalities pass to genuine
finite L2-family weak limits. -/
noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped Topology RealInnerProductSpace ENNReal
namespace KLSConstantImprovement.ActualFiniteFamilyWeakPassage405
open ActualSourceRegularizedWeakCompactness405
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {ν : Measure α}
set_option backward.isDefEq.respectTransparency false

theorem finite_family_weak_coordinate_tendsto
    {W : ℕ → PiLp 2 (fun _ : ι => Lp ℝ 2 ν)} {V : PiLp 2 (fun _ : ι => Lp ℝ 2 ν)}
    (hw : ∀ Y, Tendsto (fun k => inner ℝ (W k) Y) atTop (𝓝 (inner ℝ V Y)))
    (a : ι) (z : Lp ℝ 2 ν) :
    Tendsto (fun k => inner ℝ (W k a) z) atTop (𝓝 (inner ℝ (V a) z)) := by
  let P : PiLp 2 (fun _ : ι => Lp ℝ 2 ν) →L[ℝ] Lp ℝ 2 ν := PiLp.proj 2 (fun _ : ι => Lp ℝ 2 ν) a
  let L := (InnerProductSpace.toDual ℝ (Lp ℝ 2 ν) z).comp P
  have ht := tendsto_real_clm_of_weak_inner hw L
  change Tendsto (fun k => inner ℝ z (W k a)) atTop (𝓝 (inner ℝ z (V a))) at ht
  simpa only [real_inner_comm] using ht

theorem finite_family_coordinate_eq_of_weak_limit
    {W : ℕ → PiLp 2 (fun _ : ι => Lp ℝ 2 ν)} {V : PiLp 2 (fun _ : ι => Lp ℝ 2 ν)}
    (hw : ∀ Y, Tendsto (fun k => inner ℝ (W k) Y) atTop (𝓝 (inner ℝ V Y)))
    (a b : ι) (heq : ∀ k, W k a = W k b) : V a = V b := by
  let z := V a - V b
  have ha := finite_family_weak_coordinate_tendsto hw a z
  have hb := finite_family_weak_coordinate_tendsto hw b z
  have he (k : ℕ) : inner ℝ (W k a) z = inner ℝ (W k b) z :=
    congrArg (fun v : Lp ℝ 2 ν => inner ℝ v z) (heq k)
  have hinner : inner ℝ (V a) z = inner ℝ (V b) z :=
    tendsto_nhds_unique ha (hb.congr fun k => (he k).symm)
  have hz : inner ℝ z z = 0 := by
    change inner ℝ (V a - V b) z = 0
    rw [inner_sub_left]
    exact sub_eq_zero.mpr hinner
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

end KLSConstantImprovement.ActualFiniteFamilyWeakPassage405
#print axioms KLSConstantImprovement.ActualFiniteFamilyWeakPassage405.finite_family_weak_coordinate_tendsto
#print axioms KLSConstantImprovement.ActualFiniteFamilyWeakPassage405.finite_family_coordinate_eq_of_weak_limit
