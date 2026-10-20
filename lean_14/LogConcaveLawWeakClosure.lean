import AdmissibleLawTightness
import KLS.LogConcavityProjection
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! Weak closedness of the original compact-set log-concavity predicate.
Open neighborhoods supply Portmanteau lower bounds, their interpolation
lies in a closed neighborhood, and continuity from above removes it. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem affine_thickening_subset_cthickening {E F : Set (Space n)}
    {ε t : ℝ} (hε : 0 < ε) (ht0 : 0 < t) (ht1 : t < 1) :
    affineSetCombination t (thickening ε E) (thickening ε F) ⊆
      cthickening ε (affineSetCombination t E F) := by
  rintro z ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
  obtain ⟨a,ha,hxa⟩ := mem_thickening_iff.mp hx
  obtain ⟨b,hb,hyb⟩ := mem_thickening_iff.mp hy
  refine mem_cthickening_of_dist_le (t•x+(1-t)•y) (t•a+(1-t)•b) ε
    (affineSetCombination t E F) ⟨(a,b),⟨ha,hb⟩,rfl⟩ ?_
  have he : t•x+(1-t)•y-(t•a+(1-t)•b) = t•(x-a)+(1-t)•(y-b) := by
    simp only [smul_sub]
    abel
  rw [dist_eq_norm,he]
  calc
    _ ≤ ‖t•(x-a)‖+‖(1-t)•(y-b)‖ := norm_add_le _ _
    _ = t*dist x a+(1-t)*dist y b := by
      rw [norm_smul_of_nonneg ht0.le,norm_smul_of_nonneg (by linarith : 0 ≤ 1-t)]
      simp only [dist_eq_norm]
    _ ≤ ε := by
      have h1 := mul_lt_mul_of_pos_left hxa ht0
      have h2 := mul_lt_mul_of_pos_left hyb (by linarith : 0 < 1-t)
      nlinarith

 theorem liminf_rpow_pos {ι : Type*} {l : Filter ι} {u : ι → ℝ≥0∞}
    {t : ℝ} (ht : 0 < t) : (liminf u l)^t = liminf (fun i => (u i)^t) l := by
  exact OrderIso.liminf_apply (ENNReal.orderIsoRpow t ht)
    (by isBoundedDefault) (by isBoundedDefault) (by isBoundedDefault) (by isBoundedDefault)

/-- Log-concavity is preserved by actual weak convergence of probability
measures, for the exact compact-set predicate in the original target. -/
theorem measureLogConcave_of_probability_tendsto
    {ι : Type*} {l : Filter ι} [NeBot l]
    {ν : ι → ProbabilityMeasure (Space n)} {μ : ProbabilityMeasure (Space n)}
    (hlim : Tendsto ν l (𝓝 μ))
    (hLC : ∀ᶠ i in l, measureLogConcave (ν i : Measure (Space n))) :
    measureLogConcave (μ : Measure (Space n)) := by
  intro E F hE hF t ht0 ht1
  have ht : 0 < 1-t := by linarith
  let C := affineSetCombination t E F
  have hC : IsClosed C := (isCompact_affineSetCombination t hE hF).isClosed
  have hbound (ε : ℝ) (hε : 0 < ε) :
      ((μ : Measure (Space n)) E)^t*((μ : Measure (Space n)) F)^(1-t) ≤
        (μ : Measure (Space n)) (cthickening ε C) := by
    have hE' := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
      (isOpen_thickening : IsOpen (thickening ε E))
    have hF' := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
      (isOpen_thickening : IsOpen (thickening ε F))
    have hEL : (μ : Measure (Space n)) E ≤
        liminf (fun i => (ν i : Measure (Space n)) (thickening ε E)) l :=
      (measure_mono (self_subset_thickening hε E)).trans hE'
    have hFL : (μ : Measure (Space n)) F ≤
        liminf (fun i => (ν i : Measure (Space n)) (thickening ε F)) l :=
      (measure_mono (self_subset_thickening hε F)).trans hF'
    have hproduct : ((μ : Measure (Space n)) E)^t*((μ : Measure (Space n)) F)^(1-t) ≤
        liminf (fun i => ((ν i : Measure (Space n)) (thickening ε E))^t*
          ((ν i : Measure (Space n)) (thickening ε F))^(1-t)) l := by
      calc
        _ ≤ (liminf (fun i => (ν i : Measure (Space n)) (thickening ε E)) l)^t*
            (liminf (fun i => (ν i : Measure (Space n)) (thickening ε F)) l)^(1-t) :=
          mul_le_mul' (ENNReal.rpow_le_rpow hEL ht0.le) (ENNReal.rpow_le_rpow hFL ht.le)
        _ ≤ _ := by
          rw [liminf_rpow_pos ht0,liminf_rpow_pos ht]
          exact ENNReal.le_liminf_mul
    have hi : ∀ᶠ i in l,
        ((ν i : Measure (Space n)) (thickening ε E))^t*
          ((ν i : Measure (Space n)) (thickening ε F))^(1-t) ≤
        (ν i : Measure (Space n)) (cthickening ε C) := by
      filter_upwards [hLC] with i hi
      exact hi.le_measure_of_measurable_interpolation isOpen_thickening.measurableSet
        isOpen_thickening.measurableSet ht0 ht1 (affine_thickening_subset_cthickening hε ht0 ht1)
    exact hproduct.trans ((liminf_le_liminf hi).trans
      ((liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)).trans
        (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim isClosed_cthickening)))
  have hct : Tendsto (fun ε : ℝ => (μ : Measure (Space n)) (cthickening ε C))
      (𝓝[>] 0) (𝓝 ((μ : Measure (Space n)) C)) :=
    (tendsto_measure_cthickening_of_isClosed ⟨1,zero_lt_one,measure_ne_top _ _⟩ hC).mono_left
      nhdsWithin_le_nhds
  apply ge_of_tendsto hct
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε

/-- The genuine log-concave probability-law class is weakly closed. -/
theorem isClosed_logConcave_probability_laws :
    IsClosed {μ : ProbabilityMeasure (Space n) | measureLogConcave (μ : Measure (Space n))} := by
  apply IsSeqClosed.isClosed
  intro ν μ hν hlim
  exact measureLogConcave_of_probability_tendsto hlim (.of_forall hν)

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.measureLogConcave_of_probability_tendsto
#print axioms KLS.DeterministicBridgeNext.isClosed_logConcave_probability_laws
