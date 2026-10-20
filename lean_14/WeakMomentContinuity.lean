import LogConcaveLawWeakClosure
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-! Weak convergence of continuous unbounded observables under an actual
uniform squared-moment bound. Scalar clipping provides bounded continuous
approximants and a quantitative L1 error. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 def scalarClip (R t : ℝ) : ℝ := max (-R) (min R t)

 theorem scalarClip_bounds {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    -R ≤ scalarClip R t ∧ scalarClip R t ≤ R := by
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩

 theorem scalarClip_error {R : ℝ} (hR : 0 < R) (t : ℝ) :
    |t-scalarClip R t| ≤ t^2/R := by
  apply (le_div_iff₀ hR).mpr
  by_cases hlow : t ≤ -R
  · have he : scalarClip R t = -R := by
      simp only [scalarClip,min_eq_right (by linarith : t ≤ R),max_eq_left hlow]
    rw [he,abs_of_nonpos (by linarith : t-(-R) ≤ 0)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ -t-R) (by linarith : 0 ≤ -t)]
  · by_cases hhigh : R ≤ t
    · have he : scalarClip R t = R := by
        simp [scalarClip,min_eq_left hhigh,max_eq_right (by linarith : -R ≤ R)]
      rw [he,abs_of_nonneg (by linarith : 0 ≤ t-R)]
      nlinarith [mul_nonneg (by linarith : 0 ≤ t-R) (by linarith : 0 ≤ t)]
    · have he : scalarClip R t = t := by
        simp [scalarClip,min_eq_right (le_of_not_ge hhigh),max_eq_right (le_of_not_ge hlow)]
      rw [he,sub_self,abs_zero]
      nlinarith [sq_nonneg t]

 def boundedClip {E : Type*} [TopologicalSpace E] (f : E → ℝ) (hf : Continuous f)
    (R : ℝ) (hR : 0 ≤ R) : BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => scalarClip R (f x),by unfold scalarClip; fun_prop⟩
    (2*R) (by
      intro x y
      have hx := scalarClip_bounds hR (f x)
      have hy := scalarClip_bounds hR (f y)
      change dist (scalarClip R (f x)) (scalarClip R (f y)) ≤ 2*R
      rw [Real.dist_eq,abs_le]
      constructor <;> linarith)

 theorem integral_clip_error {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
    {f : E → ℝ} (hf : Continuous f) (hf2 : MemLp f 2 μ) {R : ℝ} (hR : 0 < R) :
    |(∫ x, f x ∂μ)-(∫ x, boundedClip f hf R hR.le x ∂μ)| ≤
      (∫ x, f x^2 ∂μ)/R := by
  have hfi := hf2.integrable (by norm_num)
  have hgi : Integrable (boundedClip f hf R hR.le) μ :=
    (boundedClip f hf R hR.le).integrable μ
  have hsq := (memLp_two_iff_integrable_sq hf2.aestronglyMeasurable).mp hf2
  rw [← integral_sub hfi hgi]
  calc
    _ ≤ ∫ x, ‖f x-boundedClip f hf R hR.le x‖ ∂μ := by simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (fun x => f x-boundedClip f hf R hR.le x))
    _ ≤ ∫ x, f x^2/R ∂μ := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hsq.div_const R)
      exact ae_of_all _ fun x => by
        change |f x-scalarClip R (f x)| ≤ f x^2/R
        exact scalarClip_error hR (f x)
    _ = _ := integral_div _ _

/-- A genuine weak limit preserves continuous observable expectations when
an actual uniform squared-moment bound is available. -/
theorem tendsto_integral_of_uniform_sq_moment
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    {ι : Type*} {l : Filter ι} {ν : ι → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hlim : Tendsto ν l (𝓝 μ)) {f : E → ℝ} (hf : Continuous f)
    (hμf : MemLp f 2 (μ : Measure E)) (hνf : ∀ i, MemLp f 2 (ν i : Measure E))
    (C : ℝ) (hC : ∀ᶠ i in l, (∫ x, f x^2 ∂(ν i : Measure E)) ≤ C) :
    Tendsto (fun i => ∫ x, f x ∂(ν i : Measure E)) l (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let M := |C|+(∫ x, f x^2 ∂(μ : Measure E))+1
  have hμnonneg : 0 ≤ ∫ x, f x^2 ∂(μ : Measure E) := integral_nonneg fun x => sq_nonneg _
  have hM : 0 < M := by dsimp [M]; positivity
  let R := 4*M/ε
  have hR : 0 < R := div_pos (by positivity) hε
  have hMR : M/R = ε/4 := by dsimp [R]; field_simp
  have hclip := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim)
    (boundedClip f hf R hR.le)
  have hevent := Metric.tendsto_nhds.mp hclip (ε/2) (by positivity)
  filter_upwards [hC,hevent] with i hi hclose
  rw [Real.dist_eq] at hclose ⊢
  have hνerror := integral_clip_error hf (hνf i) hR
  have hμerror := integral_clip_error hf hμf hR
  have hνle : (∫ x, f x^2 ∂(ν i : Measure E))/R ≤ ε/4 := by
    rw [← hMR]
    apply div_le_div_of_nonneg_right _ hR.le
    dsimp [M]
    linarith [le_abs_self C]
  have hμle : (∫ x, f x^2 ∂(μ : Measure E))/R ≤ ε/4 := by
    rw [← hMR]
    apply div_le_div_of_nonneg_right _ hR.le
    dsimp [M]
    linarith [abs_nonneg C]
  have htri : |(∫ x, f x ∂(ν i : Measure E))-(∫ x, f x ∂(μ : Measure E))| ≤
      |(∫ x, f x ∂(ν i : Measure E))-(∫ x, boundedClip f hf R hR.le x ∂(ν i : Measure E))| +
      |(∫ x, boundedClip f hf R hR.le x ∂(ν i : Measure E))-
        (∫ x, boundedClip f hf R hR.le x ∂(μ : Measure E))| +
      |(∫ x, f x ∂(μ : Measure E))-(∫ x, boundedClip f hf R hR.le x ∂(μ : Measure E))| := by
    have h1 := dist_triangle (∫ x, f x ∂(ν i : Measure E))
      (∫ x, boundedClip f hf R hR.le x ∂(ν i : Measure E))
      (∫ x, f x ∂(μ : Measure E))
    have h2 := dist_triangle (∫ x, boundedClip f hf R hR.le x ∂(ν i : Measure E))
      (∫ x, boundedClip f hf R hR.le x ∂(μ : Measure E))
      (∫ x, f x ∂(μ : Measure E))
    rw [Real.dist_eq,Real.dist_eq,Real.dist_eq] at h1 h2
    rw [abs_sub_comm (∫ x, boundedClip f hf R hR.le x ∂(μ : Measure E))
      (∫ x, f x ∂(μ : Measure E))] at h2
    linarith
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.tendsto_integral_of_uniform_sq_moment
