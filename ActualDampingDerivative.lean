import ActualLawTiltSmooth
import KLS.GlobalQuadraticDamping
import Mathlib

/-! Genuine one-sided differentiation of normalized nonnegative damping.
Only an integrable first rate-weighted observable is needed for the
numerator. This is not a formal or assumed evolution equation. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
set_option maxHeartbeats 1000000

 theorem damping_slope_bound {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) :
    |(Real.exp (-s*a)-1)/s| ≤ a := by
  have he : Real.exp (-s*a) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hl := Real.add_one_le_exp (-s*a)
  rw [abs_div,abs_of_pos hs,abs_of_nonpos (sub_nonpos.mpr he),div_le_iff₀ hs]
  nlinarith

 theorem hasDerivWithinAt_damping_numerator
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f a : α → ℝ}
    (hf : Integrable f μ) (ha : AEStronglyMeasurable a μ) (ha0 : ∀ x, 0 ≤ a x)
    (hfa : Integrable (fun x => ‖f x‖*a x) μ) :
    HasDerivWithinAt (fun s : ℝ => ∫ x, f x*Real.exp (-s*a x) ∂μ)
      (-∫ x, f x*a x ∂μ) (Ici 0) 0 := by
  let F : ℝ → α → ℝ := fun s x => f x*((Real.exp (-s*a x)-1)/s)
  have hlim : Tendsto (fun s => ∫ x, F s x ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, -f x*a x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖*a x)
    · exact Eventually.of_forall fun s => by
        dsimp [F]
        convert hf.aestronglyMeasurable.mul
          (((Real.continuous_exp.comp_aestronglyMeasurable (ha.const_mul (-s))).sub
            (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : α => (1 : ℝ)) μ)).mul_const s⁻¹) using 1
        funext x
        simp only [div_eq_mul_inv,Pi.mul_apply,Pi.sub_apply]
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Eventually.of_forall fun x => by
        dsimp [F]
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (damping_slope_bound hs (ha0 x)) (abs_nonneg _)
    · exact hfa
    · exact Eventually.of_forall fun x => by
        have hd : HasDerivAt (fun s : ℝ => f x*Real.exp (-s*a x)) (-f x*a x) 0 := by
          convert ((((hasDerivAt_id (0 : ℝ)).neg.mul_const (a x)).exp).const_mul (f x)) using 1 <;> simp <;> ring
        have ht := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp
          (hd.hasDerivWithinAt (s := Ioi 0))
        convert ht using 1
        funext s
        simp only [F,slope_def_field,neg_zero,zero_mul,Real.exp_zero,mul_one,sub_zero]
        ring
  have hif (s : ℝ) (hs : 0 ≤ s) : Integrable (fun x => f x*Real.exp (-s*a x)) μ := by
    apply hf.mul_bdd (Real.continuous_exp.comp_aestronglyMeasurable (ha.const_mul (-s)))
    exact Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith [ha0 x])
  have he : (fun s => ∫ x, F s x ∂μ) =ᶠ[𝓝[>] (0 : ℝ)]
      slope (fun s : ℝ => ∫ x, f x*Real.exp (-s*a x) ∂μ) 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [slope_def_field,neg_zero,zero_mul,Real.exp_zero,mul_one,sub_zero]
    rw [← integral_sub (hif s hs.le) hf,← integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp [F]; ring
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mpr
  have hv : (∫ x, -f x*a x ∂μ) = -(∫ x, f x*a x ∂μ) := by
    simp_rw [neg_mul]
    rw [integral_neg]
  rw [← hv]
  exact hlim.congr' he

/-- The normalized tilted expectation has the actual right derivative
minus its covariance with the damping rate. -/
 theorem hasDerivWithinAt_normalized_damping
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f a : α → ℝ} (hf : Integrable f μ) (ha : Integrable a μ)
    (ha0 : ∀ x, 0 ≤ a x) (hfa : Integrable (fun x => ‖f x‖*a x) μ) :
    HasDerivWithinAt (fun s : ℝ => ∫ x, f x ∂μ.tilted (fun x => -s*a x))
      ((∫ x, f x ∂μ)*(∫ x, a x ∂μ)-(∫ x, f x*a x ∂μ)) (Ici 0) 0 := by
  have hn := hasDerivWithinAt_damping_numerator hf ha.aestronglyMeasurable ha0 hfa
  have h1a : Integrable (fun x : α => ‖(1 : ℝ)‖*a x) μ := by simpa only [norm_one,one_mul] using ha
  have hd := hasDerivWithinAt_damping_numerator (integrable_const (1 : ℝ))
    ha.aestronglyMeasurable ha0 h1a
  have hd' : HasDerivWithinAt (fun s : ℝ => ∫ x, Real.exp (-s*a x) ∂μ)
      (-∫ x, a x ∂μ) (Ici 0) 0 := by simpa only [one_mul] using hd
  have hden : (∫ x : α, Real.exp (-(0 : ℝ)*a x) ∂μ) ≠ 0 := by simp
  have hq := hn.div hd' hden
  have he : (fun s : ℝ => ∫ x, f x ∂μ.tilted (fun x => -s*a x)) =
      (fun s : ℝ => (∫ x, f x*Real.exp (-s*a x) ∂μ)/(∫ x, Real.exp (-s*a x) ∂μ)) := by
    funext s
    rw [integral_tilted (fun x => -s*a x) f]
    simp only [smul_eq_mul]
    simp_rw [div_mul_eq_mul_div,mul_comm (Real.exp _) (f _),div_eq_mul_inv]
    exact integral_mul_const _ _
  rw [he]
  convert hq using 1 <;> simp <;> ring

 theorem integrable_norm_mul_quadratic_rate
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    Integrable (fun x => ‖f x‖*(‖x‖^2/2)) μ := by
  obtain ⟨r,hr,hfD,h1D⟩ := exists_common_local_exponential_domains hLC hf
  apply (hfD.2 2).mono' ((hf.aestronglyMeasurable.norm).mul (by fun_prop))
  exact Eventually.of_forall fun x => by
    change |‖f x‖*(‖x‖^2/2)| ≤ ‖f x‖*‖x‖^2*Real.exp (r*‖x‖)
    rw [abs_of_nonneg (by positivity)]
    have he : 1 ≤ Real.exp (r*‖x‖) := Real.one_le_exp_iff.mpr (by positivity)
    nlinarith [mul_nonneg (norm_nonneg (f x)) (sq_nonneg ‖x‖)]

/-- The literal one-sided damping derivative in (3.6), at theta=0,
for every L² observable of an arbitrary log-concave probability law. -/
 theorem hasDerivWithinAt_quadratic_damping_average
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    HasDerivWithinAt
      (fun s : ℝ => ∫ x, f x ∂μ.tilted (fun x => -s*(‖x‖^2/2)))
      ((∫ x, f x ∂μ)*(∫ x, ‖x‖^2/2 ∂μ)-(∫ x, f x*(‖x‖^2/2) ∂μ))
      (Ici 0) 0 := by
  have ha : Integrable (fun x : Space n => ‖x‖^2/2) μ := by
    simpa only [norm_one,one_mul] using
      integrable_norm_mul_quadratic_rate hLC (memLp_const (1 : ℝ))
  exact hasDerivWithinAt_normalized_damping (hf.integrable (by norm_num)) ha
    (fun _ => by positivity) (integrable_norm_mul_quadratic_rate hLC hf)

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.hasDerivWithinAt_damping_numerator

#print axioms KLS.DeterministicBridgeIntegration.hasDerivWithinAt_quadratic_damping_average
