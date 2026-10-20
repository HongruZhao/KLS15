import KLSConstantImprovement.ActualLocalBoundedWeakAlgebra405

/-! Compact cutoffs of genuine locally bounded raw H1 functions are
bounded compact weak tests. This supplies ordinary local test domains;
it makes no assertion about a global canonical metric energy. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualLocalCompactWeakTests405
open KLS ActualLocalBoundedWeakAlgebra405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def smoothLocalRawTest {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) : LocalRawTest n where
  value := f
  derivative := coordinateDerivative f
  value_local_top := fun E hE => memLp_continuous_top_on_compact hf.continuous hE
  derivative_local := by
    intro a E hE
    letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
    exact (memLp_continuous_top_on_compact
      (contDiff_coordinateDerivative hf (m := 0) (by norm_num) a).continuous hE).mono_exponent (by simp)
  weak_derivative := hasLocalWeakCoordinateDerivative_of_contDiff hf

theorem compact_localRawTest_memLp_top (f : LocalRawTest n) (hc : HasCompactSupport f.value) :
    MemLp f.value ∞ (volume : Measure (Space n)) := by
  have hi : MemLp ((tsupport f.value).indicator f.value) ∞ volume :=
    (memLp_indicator_iff_restrict hc.measurableSet.nullMeasurableSet).mpr (f.value_local_top _ hc)
  have he : (tsupport f.value).indicator f.value = f.value := by
    funext x
    by_cases hx : x ∈ tsupport f.value
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
  rwa [he] at hi

theorem compact_localRawTest_bound (f : LocalRawTest n) (hc : HasCompactSupport f.value) :
    ∃ B : ℝ, ∀ᵐ x ∂(volume : Measure (Space n)), ‖f.value x‖ ≤ B := by
  have hm := compact_localRawTest_memLp_top f hc
  have he := hm.eLpNorm_lt_top
  rw [eLpNorm_exponent_top hm.aestronglyMeasurable] at he
  obtain ⟨B, hB⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp he
  have hBn : ∀ᵐ x ∂(volume : Measure (Space n)), ‖f.value x‖₊ ≤ B :=
    Filter.eventually_map.mp hB
  refine ⟨(B : ℝ), hBn.mono fun x hx => ?_⟩
  exact_mod_cast hx

def cutoffLocalRawTest {θ : Space n → ℝ} (hθ : ContDiff ℝ 1 θ) (f : LocalRawTest n) :
    LocalRawTest n := (smoothLocalRawTest hθ).mul f

theorem cutoffLocalRawTest_bound {θ : Space n → ℝ} (hθ : ContDiff ℝ 1 θ)
    (hc : HasCompactSupport θ) (f : LocalRawTest n) :
    ∃ B : ℝ, ∀ᵐ x ∂(volume : Measure (Space n)), ‖θ x * f.value x‖ ≤ B :=
  compact_localRawTest_bound (cutoffLocalRawTest hθ f) hc.mul_right

end KLSConstantImprovement.ActualLocalCompactWeakTests405

#print axioms KLSConstantImprovement.ActualLocalCompactWeakTests405.compact_localRawTest_bound
#print axioms KLSConstantImprovement.ActualLocalCompactWeakTests405.cutoffLocalRawTest_bound
