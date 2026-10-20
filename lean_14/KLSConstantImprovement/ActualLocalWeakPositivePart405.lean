import KLSConstantImprovement.ActualLocalC1LipschitzScalarChain405
import KLSConstantImprovement.ActualSmoothPositivePart405
import KLS.LocalL2CompactPairings
import KLS.MollificationLocalization

/-! The actual positive part of a raw local-H1 function has a genuine
weak derivative, with the limiting slope 1/2 at zero.  Positive-part values
and derivatives have their local L2 domains.  The proof passes the C1
Lipschitz regularizers through actual compact-test integral pairings. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualLocalWeakPositivePart405
open KLS ActualLocalC1LipschitzScalarChain405 ActualSmoothPositivePart405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem positivePartSlope_measurable : Measurable positivePartSlope := by
  exact Measurable.ite measurableSet_Ioi measurable_const
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

theorem positivePart_raw_local_L2
    {f F : Space n → ℝ}
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E))
    (hF : ∀ E, IsCompact E → MemLp F 2 (volume.restrict E))
    (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (fun x => max (f x) 0) 2 (volume.restrict E) ∧
      MemLp (fun x => positivePartSlope (f x)*F x) 2 (volume.restrict E) := by
  have hv : MemLp (fun x => max (f x) 0) 2 (volume.restrict E) := by
    apply (hf E hE).norm.mono'
      (((continuous_id.max continuous_const : Continuous (fun t : ℝ => max t 0))).comp_aestronglyMeasurable
        (hf E hE).aestronglyMeasurable)
    exact Eventually.of_forall fun x => by
      change |max (f x) 0| ≤ |f x|
      rw [abs_of_nonneg (le_max_right (f x) 0)]
      exact max_le (le_abs_self _) (abs_nonneg _)
  have hm : AEStronglyMeasurable (fun x => positivePartSlope (f x)) (volume.restrict E) :=
    (positivePartSlope_measurable.comp_aemeasurable (hf E hE).aemeasurable).aestronglyMeasurable
  have hs : MemLp (fun x => positivePartSlope (f x)) ∞ (volume.restrict E) := by
    apply memLp_top_of_bound hm 1
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (positivePartSlope_bounds (f x)).1]
      exact (positivePartSlope_bounds (f x)).2
  exact ⟨hv, hs.mul (hF E hE)⟩

theorem local_positivePart_weak_chain
    {f F : Space n → ℝ} {i : Fin n}
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E))
    (hFloc : ∀ E, IsCompact E → MemLp F 2 (volume.restrict E))
    (hw : HasLocalWeakCoordinateDerivative f F i) :
    HasLocalWeakCoordinateDerivative (fun x => max (f x) 0)
      (fun x => positivePartSlope (f x)*F x) i := by
  have hfmeas := (locallyIntegrable_of_memLp_two_on_compacts hf).aestronglyMeasurable
  have hFmeas := (locallyIntegrable_of_memLp_two_on_compacts hFloc).aestronglyMeasurable
  have hsc (k : ℕ) : Continuous (smoothPositivePartSlope (cutoffScale k)) := by
    have he : deriv (smoothPositivePart (cutoffScale k)) = smoothPositivePartSlope (cutoffScale k) :=
      funext fun t => (smoothPositivePart_hasDerivAt (cutoffScale_pos k) t).deriv
    rw [← he]
    exact (smoothPositivePart_contDiff (cutoffScale_pos k)).continuous_deriv_one
  have hchain (k : ℕ) : HasLocalWeakCoordinateDerivative
      (fun x => smoothPositivePart (cutoffScale k) (f x))
      (fun x => smoothPositivePartSlope (cutoffScale k) (f x)*F x) i := by
    have he (t : ℝ) : deriv (smoothPositivePart (cutoffScale k)) t =
        smoothPositivePartSlope (cutoffScale k) t :=
      (smoothPositivePart_hasDerivAt (cutoffScale_pos k) t).deriv
    have hh := local_C1_lipschitz_scalar_chain hf hFloc hw
      (smoothPositivePart_contDiff (cutoffScale_pos k))
      (smoothPositivePart_lipschitz (cutoffScale_pos k))
    simpa only [he] using hh
  intro ψ hψ hcψ
  have hDψ : Continuous (coordinateDerivative ψ i) :=
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous
  have hcDψ : HasCompactSupport (coordinateDerivative ψ i) :=
    hasCompactSupport_coordinateDerivative hcψ i
  have hfD := integrable_mul_continuous_compact_of_localL2 hDψ hcDψ hf
  have hDψI : Integrable (coordinateDerivative ψ i) (volume : Measure (Space n)) :=
    hDψ.integrable_of_hasCompactSupport hcDψ
  have hFψ := integrable_mul_continuous_compact_of_localL2 hψ.continuous hcψ hFloc
  have hdomL : Integrable (fun x => (‖f x‖+1)*‖coordinateDerivative ψ i x‖)
      (volume : Measure (Space n)) := by
    convert hfD.norm.add hDψI.norm using 1
    funext x
    dsimp only [Pi.add_apply]
    rw [norm_mul]
    ring
  have hdomR : Integrable (fun x => ‖F x‖*‖ψ x‖) (volume : Measure (Space n)) := by
    simpa only [norm_mul] using hFψ.norm
  have hmL (k : ℕ) : AEStronglyMeasurable
      (fun x => smoothPositivePart (cutoffScale k) (f x)*coordinateDerivative ψ i x) volume :=
    (((smoothPositivePart_contDiff (cutoffScale_pos k)).continuous.comp_aestronglyMeasurable
      hfmeas).mul hDψ.aestronglyMeasurable)
  have hmR (k : ℕ) : AEStronglyMeasurable
      (fun x => (smoothPositivePartSlope (cutoffScale k) (f x)*F x)*ψ x) volume :=
    (((hsc k).comp_aestronglyMeasurable hfmeas).mul hFmeas).mul hψ.continuous.aestronglyMeasurable
  have hbL (k : ℕ) : ∀ᵐ x ∂(volume : Measure (Space n)),
      ‖smoothPositivePart (cutoffScale k) (f x)*coordinateDerivative ψ i x‖ ≤
        (‖f x‖+1)*‖coordinateDerivative ψ i x‖ := Eventually.of_forall fun x => by
    have hb := smoothPositivePart_value_bounds (cutoffScale_pos k) (cutoffScale_le_one k) (f x)
    rw [norm_mul, Real.norm_eq_abs (smoothPositivePart (cutoffScale k) (f x)), abs_of_nonneg hb.1]
    exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hb.2) (norm_nonneg _)
  have hbR (k : ℕ) : ∀ᵐ x ∂(volume : Measure (Space n)),
      ‖(smoothPositivePartSlope (cutoffScale k) (f x)*F x)*ψ x‖ ≤ ‖F x‖*‖ψ x‖ :=
    Eventually.of_forall fun x => by
      have hb := smoothPositivePartSlope_bounds (cutoffScale_pos k) (f x)
      rw [norm_mul, norm_mul, Real.norm_eq_abs (smoothPositivePartSlope (cutoffScale k) (f x)),
        abs_of_nonneg hb.1]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (norm_nonneg _) hb.2) (norm_nonneg _)
  have hl := tendsto_integral_of_dominated_convergence
    (fun x => (‖f x‖+1)*‖coordinateDerivative ψ i x‖) hmL hdomL hbL
    (Eventually.of_forall fun x =>
      (smoothPositivePart_cutoffScale_tendsto (f x)).mul_const (coordinateDerivative ψ i x))
  have hr := tendsto_integral_of_dominated_convergence (fun x => ‖F x‖*‖ψ x‖) hmR hdomR hbR
    (Eventually.of_forall fun x =>
      ((smoothPositivePartSlope_cutoffScale_tendsto (f x)).mul_const (F x)).mul_const (ψ x))
  exact tendsto_nhds_unique hl
    (hr.neg.congr' (Eventually.of_forall fun k => (hchain k ψ hψ hcψ).symm))

end KLSConstantImprovement.ActualLocalWeakPositivePart405
#print axioms KLSConstantImprovement.ActualLocalWeakPositivePart405.positivePartSlope_measurable
#print axioms KLSConstantImprovement.ActualLocalWeakPositivePart405.positivePart_raw_local_L2
#print axioms KLSConstantImprovement.ActualLocalWeakPositivePart405.local_positivePart_weak_chain
