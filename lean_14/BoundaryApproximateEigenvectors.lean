import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Tactic

/-! Concrete approximate eigenvectors at boundary spectral points.  The
proof uses actual inverse operators at nearby resolvent points; approximate
point-spectrum membership is a conclusion, not an assumed property. -/
noncomputable section
open Filter Set
open scoped Topology NNReal ENNReal
namespace KLSBelow25
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

def spectralShift (T : H →L[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  algebraMap ℂ (H →L[ℂ] H) z-T

@[simp] theorem spectralShift_apply (T : H →L[ℂ] H) (z : ℂ) (x : H) :
    spectralShift T z x = z • x-T x := by simp [spectralShift]

theorem spectralShift_sub_norm (T : H →L[ℂ] H) (z w : ℂ) :
    ‖spectralShift T z-spectralShift T w‖ = ‖z-w‖ := by
  simp only [spectralShift,sub_sub_sub_cancel_right,← map_sub,norm_algebraMap,norm_one,mul_one]

/-- A spectral point cannot lie inside the Neumann perturbation radius
of a genuine resolvent operator. -/
theorem spectral_distance_inverse_lower (T : H →L[ℂ] H) {z w : ℂ}
    (hz : z ∈ spectrum ℂ T) (V : (H →L[ℂ] H)ˣ)
    (hV : (V : H →L[ℂ] H) = spectralShift T w) :
    1 ≤ ‖z-w‖*‖(↑V⁻¹ : H →L[ℂ] H)‖ := by
  by_contra hn
  have hinv : 0 < ‖(↑V⁻¹ : H →L[ℂ] H)‖ := Units.norm_pos _
  have hsmall : ‖spectralShift T z-(V : H →L[ℂ] H)‖ <
      ‖(↑V⁻¹ : H →L[ℂ] H)‖⁻¹ := by
    rw [hV,spectralShift_sub_norm]
    rw [← one_div]
    apply (lt_div_iff₀ hinv).mpr
    simpa only [mul_comm] using (not_le.mp hn)
  have hu : IsUnit (spectralShift T z) := (V.ofNearby _ hsmall).isUnit
  exact (spectrum.mem_iff.mp hz) hu

theorem exists_unit_residual_lt_of_mem_frontier (T : H →L[ℂ] H) {z : ℂ}
    (hz : z ∈ frontier (spectrum ℂ T)) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ v : H, ‖v‖ = 1 ∧ ‖T v-z • v‖ < epsilon := by
  have hzspec : z ∈ spectrum ℂ T :=
    (spectrum.isClosed (𝕜:=ℂ) T).closure_eq ▸ frontier_subset_closure hz
  have hzcomp : z ∈ closure (spectrum ℂ T)ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hz
    exact hz.2
  obtain ⟨w,hw,hdist⟩ := Metric.mem_closure_iff.mp hzcomp (epsilon/4) (by positivity)
  have hwunit : IsUnit (spectralShift T w) := spectrum.notMem_iff.mp hw
  let V := hwunit.unit
  have hV : (V : H →L[ℂ] H) = spectralShift T w := hwunit.unit_spec
  have hprod := spectral_distance_inverse_lower T hzspec V hV
  have hdist' : ‖z-w‖ < epsilon/4 := by simpa [dist_eq_norm] using hdist
  have hlarge : 2/epsilon < ‖(↑V⁻¹ : H →L[ℂ] H)‖ := by
    have hsmall : ‖z-w‖*(2/epsilon) < 1 := by
      calc
        _ < (epsilon/4)*(2/epsilon) := mul_lt_mul_of_pos_right hdist' (by positivity)
        _ = 1/2 := by field_simp <;> norm_num
        _ < 1 := by norm_num
    nlinarith [norm_nonneg (z-w)]
  obtain ⟨y,hy,hybig⟩ := (↑V⁻¹ : H →L[ℂ] H).exists_lt_apply_of_lt_opNorm hlarge
  let x : H := (↑V⁻¹ : H →L[ℂ] H) y
  have hxpos : 0 < ‖x‖ := lt_trans (by positivity : 0 < 2/epsilon) hybig
  let c : ℂ := (‖x‖⁻¹ : ℝ)
  let v : H := c • x
  have hvnorm : ‖v‖ = 1 := by
    dsimp [v,c]
    simp [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hxpos),ne_of_gt hxpos]
  have hVx : spectralShift T w x = y := by
    rw [← hV]
    change ((V : H →L[ℂ] H)*(↑V⁻¹ : H →L[ℂ] H)) y=y
    simp
  have hidentity : T v-z • v = (w-z) • v-c • y := by
    have hx : w • x-T x=y := by simpa using hVx
    dsimp [v]
    rw [map_smul,← hx]
    module
  have hres : ‖T v-z • v‖ ≤ ‖w-z‖+‖x‖⁻¹*‖y‖ := by
    rw [hidentity]
    calc
      _ ≤ ‖(w-z) • v‖+‖c • y‖ := norm_sub_le _ _
      _ = _ := by simp [norm_smul,hvnorm,c,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hxpos)]
  have hinv : ‖x‖⁻¹ < epsilon/2 := by
    rw [← one_div]
    apply (div_lt_iff₀ hxpos).mpr
    have ht : 2 < epsilon*‖x‖ := by simpa [x,mul_comm] using (div_lt_iff₀ he).mp hybig
    nlinarith
  have hsecond : ‖x‖⁻¹*‖y‖ < epsilon/2 := by
    have hle : ‖x‖⁻¹*‖y‖ ≤ ‖x‖⁻¹ := by nlinarith [inv_pos.mpr hxpos]
    exact hle.trans_lt hinv
  refine ⟨v,hvnorm,?_⟩
  have hd : ‖w-z‖ < epsilon/4 := by simpa [norm_sub_rev] using hdist'
  linarith

theorem exists_approximate_eigenvectors_of_mem_frontier (T : H →L[ℂ] H) {z : ℂ}
    (hz : z ∈ frontier (spectrum ℂ T)) :
    ∃ v : ℕ → H, (∀ n, ‖v n‖=1) ∧
      Tendsto (fun n => T (v n)-z • v n) atTop (𝓝 0) := by
  have hv : ∀ n : ℕ, ∃ v : H, ‖v‖=1 ∧ ‖T v-z • v‖ < 1/((n : ℝ)+1) := by
    intro n
    exact exists_unit_residual_lt_of_mem_frontier T hz (by positivity)
  choose v hvnorm hvsmall using hv
  refine ⟨v,hvnorm,tendsto_zero_iff_norm_tendsto_zero.mpr ?_⟩
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => (hvsmall n).le) tendsto_one_div_add_atTop_nhds_zero_nat

/-- An actual spectral point attaining the spectral radius has a normalized
approximate eigenvector sequence. The point and sequence are constructed. -/
theorem exists_maximal_modulus_approximate_eigenvectors (T : H →L[ℂ] H) :
    ∃ z ∈ spectrum ℂ T, (‖z‖₊ : ℝ≥0∞)=spectralRadius ℂ T ∧
      ∃ v : ℕ → H, (∀ n, ‖v n‖=1) ∧
        Tendsto (fun n => T (v n)-z • v n) atTop (𝓝 0) := by
  obtain ⟨z,hz,hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm
    (spectrum.isBounded (𝕜:=ℂ) T) (spectrum.nonempty T)
    (Differentiable.diffContOnCl (differentiable_id : Differentiable ℂ (id : ℂ → ℂ)))
  have hzspec : z ∈ spectrum ℂ T :=
    (spectrum.isClosed (𝕜:=ℂ) T).closure_eq ▸ frontier_subset_closure hz
  have hnormle : (‖z‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ T := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup₂ (f:=fun k (_ : k ∈ spectrum ℂ T) => (‖k‖₊ : ℝ≥0∞)) z hzspec
  obtain ⟨w,hw,hwrad⟩ := spectrum.exists_nnnorm_eq_spectralRadius T
  have hnorm : ‖w‖ ≤ ‖z‖ := (hmax (subset_closure hw)).out
  have hradle : spectralRadius ℂ T ≤ (‖z‖₊ : ℝ≥0∞) := by
    rw [← hwrad]
    exact_mod_cast hnorm
  refine ⟨z,hzspec,le_antisymm hnormle hradle,?_⟩
  exact exists_approximate_eigenvectors_of_mem_frontier T hz

#print axioms exists_unit_residual_lt_of_mem_frontier
#print axioms exists_approximate_eigenvectors_of_mem_frontier
#print axioms exists_maximal_modulus_approximate_eigenvectors
end KLSBelow25
