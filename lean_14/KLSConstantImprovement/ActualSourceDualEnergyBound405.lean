import KLSConstantImprovement.ActualSourceCovariance405
import KLSConstantImprovement.ActualBoundedSourceCalculus
import KLS.MomentPerturbationNormalization
import KLS.MomentLegendreRegularity
import KLS.ConvexPotentialCoercivity

/-! A normalization estimate for the actual bounded-target sources used in
full-support exhaustion. Translate to a true minimum and set its value to
zero. Its genuine target Legendre energy is at most the dimension, independent
of the target radius. This is a compactness input, not a full-support source
construction or a natural inverse mass estimate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators Topology ENNReal NNReal
namespace KLSConstantImprovement.ActualSourceDualEnergyBound405
open KLS ActualBoundedCanonicalSource ActualSourceCovariance405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_source_coordinate_score (d : SourceData μ) (a : Space n) (i : Fin n) :
    Integrable (fun x => (x i - a i) * gradient d.potential x i)
      (potentialMeasure d.potential) ∧
    (∫ x, (x i - a i) * gradient d.potential x i ∂potentialMeasure d.potential) = 1 := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let g : Space n → ℝ := fun x => x i - a i
  have hcoord : MemLp (fun x : Space n => x i) 2 (potentialMeasure d.potential) :=
    d.source_id_memLp.norm.mono' (by fun_prop)
      (Eventually.of_forall fun x => PiLp.norm_apply_le x i)
  have hg2 : MemLp g 2 (potentialMeasure d.potential) := hcoord.sub (memLp_const _)
  have hX : MemLp (fun x => gradient d.potential x i) 2 (potentialMeasure d.potential) :=
    d.continuous_comp_gradient_memLp (EuclideanSpace.proj i).continuous 2
  have hi : Integrable (fun x => g x * gradient d.potential x i)
      (potentialMeasure d.potential) := hg2.integrable_mul hX
  have hdg (x : Space n) : HasFDerivAt g (EuclideanSpace.proj i : Space n →L[ℝ] ℝ) x := by
    change HasFDerivAt (fun z : Space n => (EuclideanSpace.proj i : Space n →L[ℝ] ℝ) z - a i)
      (EuclideanSpace.proj i : Space n →L[ℝ] ℝ) x
    exact (EuclideanSpace.proj i : Space n →L[ℝ] ℝ).hasFDerivAt.sub_const (a i)
  have hdgv (x : Space n) : fderiv ℝ g x (EuclideanSpace.single i 1) = 1 := by
    rw [(hdg x).fderiv]
    simp
  have hdφ (x : Space n) :
      fderiv ℝ d.potential x (EuclideanSpace.single i 1) = gradient d.potential x i := by
    exact coordinateDerivative_eq_gradient d.potential i x
  have hfg : Integrable (fun x => (1 : ℝ) * g x) (potentialMeasure d.potential) := by
    simpa only [one_mul] using hg2.integrable (by norm_num)
  have hdfg : Integrable (fun x => fderiv ℝ (fun _ : Space n => (1 : ℝ)) x
      (EuclideanSpace.single i 1) * g x) (potentialMeasure d.potential) := by
    simp
  have hfdg : Integrable (fun x => (1 : ℝ) * fderiv ℝ g x
      (EuclideanSpace.single i 1)) (potentialMeasure d.potential) := by
    simpa only [hdgv, one_mul] using (integrable_const (1 : ℝ) (μ := potentialMeasure d.potential))
  have hfgdφ : Integrable (fun x => (1 : ℝ) * g x * fderiv ℝ d.potential x
      (EuclideanSpace.single i 1)) (potentialMeasure d.potential) := by
    simpa only [one_mul, hdφ] using hi
  have he := integral_mul_fderiv_potentialMeasure
    (d.source_C1.differentiable (by norm_num)) (differentiable_const (1 : ℝ))
    (fun x => (hdg x).differentiableAt) (EuclideanSpace.single i 1) hfg hdfg hfdg hfgdφ
  have hz (x : Space n) : fderiv ℝ (fun _ : Space n => (1 : ℝ)) x
      (EuclideanSpace.single i 1) = 0 := by simp
  simp only [hdgv, one_mul, hdφ, hz, zero_mul, integral_zero, sub_zero,
    integral_const, probReal_univ, smul_eq_mul, one_mul] at he
  exact ⟨hi, he.symm⟩

theorem actual_source_radial_score (d : SourceData μ) (a : Space n) :
    Integrable (fun x => inner ℝ (gradient d.potential x) (x - a))
      (potentialMeasure d.potential) ∧
    (∫ x, inner ℝ (gradient d.potential x) (x - a) ∂potentialMeasure d.potential) = n := by
  have he (x : Space n) : inner ℝ (gradient d.potential x) (x - a) =
      ∑ i : Fin n, (x i - a i) * gradient d.potential x i := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.sub_apply]
  have hi : Integrable (fun x => ∑ i : Fin n,
      (x i - a i) * gradient d.potential x i) (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ (fun i _ => (actual_source_coordinate_score d a i).1)
  constructor
  · simpa only [he] using hi
  · simp_rw [he]
    rw [integral_finsetSum Finset.univ (fun i _ => (actual_source_coordinate_score d a i).1)]
    simp only [(actual_source_coordinate_score d a _).2, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem actual_source_normalized_dualEnergy_le_dim (d : SourceData μ)
    (a : Space n) (hmin : ∀ x, d.potential a ≤ d.potential x) :
    momentDualEnergy μ (normalizeMomentPotentialAt d.potential a) ≤ ENNReal.ofReal n := by
  let ψ := normalizeMomentPotentialAt d.potential a
  have hzero : ψ 0 = 0 := normalizeMomentPotentialAt_zero _ _
  have hn (x : Space n) : 0 ≤ ψ x := normalizeMomentPotentialAt_nonneg hmin x
  have hs (x : Space n) : gradient d.potential x ∈ convexSubgradient ψ (x - a) := by
    intro z
    have h := gradient_mem_convexSubgradient d.source_convex
      (d.source_C1.differentiable (by norm_num) x) (z + a)
    have he : z + a - x = z - (x - a) := by abel
    rw [he] at h
    change d.potential ((x - a) + a) - d.potential a +
      inner ℝ (gradient d.potential x) (z - (x - a)) ≤ d.potential (z + a) - d.potential a
    rw [sub_add_cancel]
    linarith only [h]
  have hb (x : Space n) : normalizedLegendreTransform ψ (gradient d.potential x) ≤
      ENNReal.ofReal (inner ℝ (gradient d.potential x) (x - a)) := by
    rw [normalizedLegendreTransform_eq_of_mem_convexSubgradient hzero (hs x)]
    exact ENNReal.ofReal_le_ofReal (sub_le_self _ (hn _))
  have hscore (x : Space n) : 0 ≤ inner ℝ (gradient d.potential x) (x - a) := by
    have h := hs x 0
    rw [hzero, zero_sub, inner_neg_right] at h
    linarith [hn (x - a)]
  have hi := actual_source_radial_score d a
  change (∫⁻ y, normalizedLegendreTransform ψ y ∂μ) ≤ _
  rw [← d.pushforward]
  change (∫⁻ y, normalizedLegendreTransform ψ y ∂
    (potentialMeasure d.potential).map (gradient d.potential)) ≤ _
  rw [lintegral_map (measurable_normalizedLegendreTransform ψ) (measurable_gradient _)]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (inner ℝ (gradient d.potential x) (x - a))
        ∂potentialMeasure d.potential := lintegral_mono hb
    _ = ENNReal.ofReal n := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi.1 (Eventually.of_forall hscore), hi.2]

theorem exists_actual_source_normalization_dualEnergy_bound (d : SourceData μ) :
    ∃ a : Space n, (∀ x, d.potential a ≤ d.potential x) ∧
      normalizeMomentPotentialAt d.potential a 0 = 0 ∧
      (∀ x, 0 ≤ normalizeMomentPotentialAt d.potential a x) ∧
      momentDualEnergy μ (normalizeMomentPotentialAt d.potential a) ≤ ENNReal.ofReal n := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨a, ha⟩ := exists_minimizer_of_finite_potentialMeasure d.source_C1.continuous d.source_convex
  exact ⟨a, ha, normalizeMomentPotentialAt_zero _ _, normalizeMomentPotentialAt_nonneg ha,
    actual_source_normalized_dualEnergy_le_dim d a ha⟩

end KLSConstantImprovement.ActualSourceDualEnergyBound405
#print axioms KLSConstantImprovement.ActualSourceDualEnergyBound405.actual_source_coordinate_score
#print axioms KLSConstantImprovement.ActualSourceDualEnergyBound405.actual_source_radial_score
#print axioms KLSConstantImprovement.ActualSourceDualEnergyBound405.actual_source_normalized_dualEnergy_le_dim
#print axioms KLSConstantImprovement.ActualSourceDualEnergyBound405.exists_actual_source_normalization_dualEnergy_bound
