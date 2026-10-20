import KLSConstantImprovement.ActualSoftTargetIntegrals405
import KLSConstantImprovement.ActualStrongPotentialMoments405
import KLS.QuadraticDamping
import KLS.MomentGradientRange

/-! Actual probability normalization of the smooth soft-barrier targets on
growing balls.  The same original strong-convexity modulus is retained. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualSoftTargetNormalization405
open KLS ActualConvexSoftBarrier405 ActualSoftTargetIntegrals405 ActualStrongPotentialMoments405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

def softTargetMass (V : Space n → ℝ) (K : Set (Space n)) (j : ℕ) : ℝ :=
  ∫ _x, (1 : ℝ) ∂rawSoftTargetMeasure V K j

def normalizedSoftTargetPotential (V : Space n → ℝ) (K : Set (Space n)) (j : ℕ) : Space n → ℝ :=
  fun x => softTargetPotential V K j x + Real.log (softTargetMass V K j)

def softTargetMeasure (V : Space n → ℝ) (K : Set (Space n)) (j : ℕ) : Measure (Space n) :=
  (potentialMeasure (normalizedSoftTargetPotential V K j)).restrict (ball 0 ((j : ℝ)+1))

theorem rawSoftTargetMeasure_finite {V : Space n → ℝ} (hV : Measurable V)
    [IsFiniteMeasure (potentialMeasure V)] (K : Set (Space n)) (j : ℕ) :
    IsFiniteMeasure (rawSoftTargetMeasure V K j) :=
  (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp
    (integrable_rawSoftTargetMeasure hV K j (integrable_const (1 : ℝ)))

theorem softTargetMass_pos {V : Space n → ℝ} (hV : Measurable V)
    [IsFiniteMeasure (potentialMeasure V)] (K : Set (Space n)) (j : ℕ) :
    0 < softTargetMass V K j := by
  letI := rawSoftTargetMeasure_finite hV K j
  have hn : rawSoftTargetMeasure V K j univ ≠ 0 := by
    intro hz
    have hz' : potentialMeasure (softTargetPotential V K j) (ball (0 : Space n) ((j : ℝ)+1)) = 0 := by
      simpa only [rawSoftTargetMeasure, Measure.restrict_apply MeasurableSet.univ, univ_inter] using hz
    have hv := volume_absolutelyContinuous_potentialMeasure_of_measurable
      (hV.add (convexSoftBarrier_smooth K j).continuous.measurable) hz'
    exact (measure_ball_pos volume (0 : Space n) (by positivity : (0 : ℝ) < (j : ℝ)+1)).ne' hv
  simpa only [softTargetMass, integral_const, smul_eq_mul, mul_one, measureReal_def] using
    ENNReal.toReal_pos hn (measure_ne_top (rawSoftTargetMeasure V K j) univ)

theorem softTargetMeasure_eq_smul {V : Space n → ℝ} (hV : Measurable V)
    [IsFiniteMeasure (potentialMeasure V)] (K : Set (Space n)) (j : ℕ) :
    softTargetMeasure V K j = ENNReal.ofReal ((softTargetMass V K j)⁻¹) • rawSoftTargetMeasure V K j := by
  have hp := softTargetMass_pos hV K j
  have hW : Measurable (softTargetPotential V K j) :=
    hV.add (convexSoftBarrier_smooth K j).continuous.measurable
  unfold softTargetMeasure normalizedSoftTargetPotential
  rw [potentialMeasure_add_const hW,
    Measure.restrict_smul]
  congr 1
  rw [Real.exp_neg, Real.exp_log hp]

theorem softTargetMeasure_probability {V : Space n → ℝ} (hV : Measurable V)
    [IsFiniteMeasure (potentialMeasure V)] (K : Set (Space n)) (j : ℕ) :
    IsProbabilityMeasure (softTargetMeasure V K j) := by
  letI := rawSoftTargetMeasure_finite hV K j
  have hp := softTargetMass_pos hV K j
  have hm : ENNReal.ofReal (softTargetMass V K j) = rawSoftTargetMeasure V K j univ := by
    simp only [softTargetMass, integral_const, smul_eq_mul, mul_one]
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  constructor
  rw [softTargetMeasure_eq_smul hV, Measure.smul_apply, smul_eq_mul, ← hm,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hp.le)]
  simp only [inv_mul_cancel₀ hp.ne', ENNReal.ofReal_one]

theorem softTargetMeasure_integral {V : Space n → ℝ} (hV : Measurable V)
    [IsFiniteMeasure (potentialMeasure V)] (K : Set (Space n)) (j : ℕ) (f : Space n → ℝ) :
    (∫ x, f x ∂softTargetMeasure V K j) =
      (∫ x, f x ∂rawSoftTargetMeasure V K j) / softTargetMass V K j := by
  rw [softTargetMeasure_eq_smul hV, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (softTargetMass_pos hV K j).le), smul_eq_mul]
  exact mul_comm _ _ |>.trans (div_eq_mul_inv _ _).symm

theorem softTargetMeasure_integrable {V : Space n → ℝ} (hV : Measurable V)
    [IsFiniteMeasure (potentialMeasure V)] (K : Set (Space n)) (j : ℕ)
    {f : Space n → ℝ} (hf : Integrable f (potentialMeasure V)) :
    Integrable f (softTargetMeasure V K j) := by
  rw [softTargetMeasure_eq_smul hV]
  exact (integrable_rawSoftTargetMeasure hV K j hf).smul_measure ENNReal.ofReal_ne_top

theorem tendsto_softTargetMeasure_integral {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {V : Space n → ℝ} (hV : Measurable V) [IsFiniteMeasure (potentialMeasure V)]
    (K : Set (Space n)) (hK : IsClosed K) (hne : K.Nonempty)
    (heq : μ = (potentialMeasure V).restrict K)
    {f : Space n → ℝ} (hf : Integrable f (potentialMeasure V)) :
    Tendsto (fun j => ∫ x, f x ∂softTargetMeasure V K j) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hn := tendsto_rawSoftTargetMeasure_integral hV K hK hne hf
  have hd := tendsto_rawSoftTargetMeasure_integral hV K hK hne (integrable_const (1 : ℝ))
  rw [← heq] at hn hd
  have hd' : Tendsto (softTargetMass V K) atTop (𝓝 1) := by
    change Tendsto (fun j => ∫ _x, (1 : ℝ) ∂rawSoftTargetMeasure V K j) atTop (𝓝 1)
    simpa only [integral_const, probReal_univ, smul_eq_mul, mul_one] using hd
  simpa only [softTargetMeasure_integral hV K, div_one, Pi.div_def] using
    hn.div hd' one_ne_zero

theorem normalizedSoftTargetPotential_regular {V : Space n → ℝ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) {κ : ℝ} (hs : StrongConvexOn univ κ V)
    {K : Set (Space n)} (hK : IsClosed K) (hne : K.Nonempty) (hc : Convex ℝ K) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (normalizedSoftTargetPotential V K j) ∧
      StrongConvexOn univ κ (normalizedSoftTargetPotential V K j) := by
  exact ⟨(hV.add (convexSoftBarrier_smooth K j)).add contDiff_const,
    strongConvexOn_add_const (strongConvex_add_convexSoftBarrier hK hne hc hs j) _⟩

theorem softTargetMeasure_logConcave {V : Space n → ℝ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) {κ : ℝ} (hκ : 0 ≤ κ)
    (hs : StrongConvexOn univ κ V)
    {K : Set (Space n)} (hK : IsClosed K) (hne : K.Nonempty) (hc : Convex ℝ K) (j : ℕ) :
    measureLogConcave (softTargetMeasure V K j) := by
  obtain ⟨hr, hs'⟩ := normalizedSoftTargetPotential_regular hV hs hK hne hc j
  exact measureLogConcave_restrict_potentialMeasure hr.continuous.measurable
    (convexOn_of_strongConvexOn_nonneg hκ hs') isOpen_ball.measurableSet (convex_ball _ _)

end KLSConstantImprovement.ActualSoftTargetNormalization405
#print axioms KLSConstantImprovement.ActualSoftTargetNormalization405.softTargetMass_pos
#print axioms KLSConstantImprovement.ActualSoftTargetNormalization405.softTargetMeasure_probability
#print axioms KLSConstantImprovement.ActualSoftTargetNormalization405.tendsto_softTargetMeasure_integral
#print axioms KLSConstantImprovement.ActualSoftTargetNormalization405.normalizedSoftTargetPotential_regular
#print axioms KLSConstantImprovement.ActualSoftTargetNormalization405.softTargetMeasure_logConcave
