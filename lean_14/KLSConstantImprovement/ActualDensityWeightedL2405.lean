import KLS.WeightedLocalDistribution
import KLS.WeakGradientExtraction

/-! Put fields from different genuine probability sources in one fixed
Lebesgue L2 space by multiplying by exp(-phi/2).  Both directions and
their exact norms are proved from the actual density definition. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ENNReal
namespace KLSConstantImprovement.ActualDensityWeightedL2405
open KLS
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ}

def densityHalf (φ : Space n → ℝ) (x : Space n) : ℝ := Real.exp (-φ x / 2)
def inverseDensityHalf (φ : Space n → ℝ) (x : Space n) : ℝ := Real.exp (φ x / 2)

theorem densityHalf_square (φ : Space n → ℝ) (x : Space n) :
    densityHalf φ x ^ 2 = Real.exp (-φ x) := by
  unfold densityHalf
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem inverseDensityHalf_square_density (φ : Space n → ℝ) (x : Space n) :
    inverseDensityHalf φ x ^ 2 * Real.exp (-φ x) = 1 := by
  unfold inverseDensityHalf
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  rw [show φ x / 2 + φ x / 2 + -φ x = 0 by ring, Real.exp_zero]

theorem densityHalf_inverseDensityHalf (φ : Space n → ℝ) (x : Space n) :
    densityHalf φ x * inverseDensityHalf φ x = 1 := by
  unfold densityHalf inverseDensityHalf
  rw [← Real.exp_add]
  rw [show -φ x / 2 + φ x / 2 = 0 by ring, Real.exp_zero]

theorem memLp_densityHalf_mul {φ f : Space n → ℝ} (hφ : Continuous φ)
    (hf : MemLp f 2 (potentialMeasure φ)) :
    MemLp (fun x => densityHalf φ x * f x) 2 volume := by
  have hm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable.mono_ac
    (volume_absolutelyContinuous_potentialMeasure hφ)
  have hρ : Continuous (densityHalf φ) := Real.continuous_exp.comp (hφ.neg.div_const 2)
  apply (memLp_two_iff_integrable_sq (hρ.aestronglyMeasurable.mul hm)).mpr
  have hi := (integrable_potentialMeasure_iff hφ.measurable).mp hf.integrable_sq
  convert hi using 1
  funext x
  change (densityHalf φ x * f x) ^ 2 = _
  rw [mul_pow, densityHalf_square]
  ring

theorem memLp_inverseDensityHalf_mul {φ F : Space n → ℝ} (hφ : Continuous φ)
    (hF : MemLp F 2 (volume : Measure (Space n))) :
    MemLp (fun x => inverseDensityHalf φ x * F x) 2 (potentialMeasure φ) := by
  have hac : potentialMeasure φ ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  have hρ : Continuous (inverseDensityHalf φ) := Real.continuous_exp.comp (hφ.div_const 2)
  apply (memLp_two_iff_integrable_sq
    (hρ.aestronglyMeasurable.mul (hF.aestronglyMeasurable.mono_ac hac))).mpr
  apply (integrable_potentialMeasure_iff hφ.measurable).mpr
  convert hF.integrable_sq using 1
  funext x
  change (inverseDensityHalf φ x * F x) ^ 2 * Real.exp (-φ x) = _
  rw [mul_pow]
  calc
    inverseDensityHalf φ x ^ 2 * F x ^ 2 * Real.exp (-φ x) =
      (inverseDensityHalf φ x ^ 2 * Real.exp (-φ x)) * F x ^ 2 := by ring
    _ = _ := by rw [inverseDensityHalf_square_density, one_mul]

theorem integral_densityHalf_square {φ : Space n → ℝ} (hφ : Continuous φ)
    (f : Space n → ℝ) :
    (∫ x, (densityHalf φ x * f x) ^ 2) = ∫ x, f x ^ 2 ∂potentialMeasure φ := by
  rw [integral_potentialMeasure hφ.measurable]
  congr 1
  funext x
  rw [mul_pow, densityHalf_square]
  ring

def toVolumeL2 {φ : Space n → ℝ} (hφ : Continuous φ)
    (f : Lp ℝ 2 (potentialMeasure φ)) : Lp ℝ 2 (volume : Measure (Space n)) :=
  (memLp_densityHalf_mul hφ (Lp.memLp f)).toLp (fun x => densityHalf φ x * f x)

def fromVolumeL2 {φ : Space n → ℝ} (hφ : Continuous φ)
    (F : Lp ℝ 2 (volume : Measure (Space n))) : Lp ℝ 2 (potentialMeasure φ) :=
  (memLp_inverseDensityHalf_mul hφ (Lp.memLp F)).toLp (fun x => inverseDensityHalf φ x * F x)

theorem toVolumeL2_ae {φ : Space n → ℝ} (hφ : Continuous φ)
    (f : Lp ℝ 2 (potentialMeasure φ)) :
    (toVolumeL2 hφ f : Space n → ℝ) =ᵐ[volume] fun x => densityHalf φ x * f x :=
  (memLp_densityHalf_mul hφ (Lp.memLp f)).coeFn_toLp

theorem fromVolumeL2_ae {φ : Space n → ℝ} (hφ : Continuous φ)
    (F : Lp ℝ 2 (volume : Measure (Space n))) :
    (fromVolumeL2 hφ F : Space n → ℝ) =ᵐ[potentialMeasure φ]
      fun x => inverseDensityHalf φ x * F x :=
  (memLp_inverseDensityHalf_mul hφ (Lp.memLp F)).coeFn_toLp

theorem toVolumeL2_norm {φ : Space n → ℝ} (hφ : Continuous φ)
    (f : Lp ℝ 2 (potentialMeasure φ)) : ‖toVolumeL2 hφ f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hn {ν : Measure (Space n)} (u : Lp ℝ 2 ν) :
      ‖u‖ ^ 2 = ∫ x, u x ^ 2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial, pow_two]
  rw [hn, hn]
  calc
    _ = ∫ x, (densityHalf φ x * f x) ^ 2 :=
      integral_congr_ae ((toVolumeL2_ae hφ f).mono fun x hx => congrArg (fun z : ℝ => z ^ 2) hx)
    _ = _ := integral_densityHalf_square hφ f

theorem toVolumeL2_fromVolumeL2 {φ : Space n → ℝ} (hφ : Continuous φ)
    (F : Lp ℝ 2 (volume : Measure (Space n))) :
    toVolumeL2 hφ (fromVolumeL2 hφ F) = F := by
  apply Lp.ext
  have he := (volume_absolutelyContinuous_potentialMeasure hφ).ae_eq (fromVolumeL2_ae hφ F)
  filter_upwards [toVolumeL2_ae hφ (fromVolumeL2 hφ F), he] with x hx hy
  rw [hx, hy, ← mul_assoc, densityHalf_inverseDensityHalf, one_mul]

theorem fromVolumeL2_norm {φ : Space n → ℝ} (hφ : Continuous φ)
    (F : Lp ℝ 2 (volume : Measure (Space n))) : ‖fromVolumeL2 hφ F‖ = ‖F‖ := by
  rw [← toVolumeL2_norm hφ (fromVolumeL2 hφ F), toVolumeL2_fromVolumeL2]

end KLSConstantImprovement.ActualDensityWeightedL2405
#print axioms KLSConstantImprovement.ActualDensityWeightedL2405.memLp_densityHalf_mul
#print axioms KLSConstantImprovement.ActualDensityWeightedL2405.memLp_inverseDensityHalf_mul
#print axioms KLSConstantImprovement.ActualDensityWeightedL2405.toVolumeL2_norm
#print axioms KLSConstantImprovement.ActualDensityWeightedL2405.toVolumeL2_fromVolumeL2
#print axioms KLSConstantImprovement.ActualDensityWeightedL2405.fromVolumeL2_norm
