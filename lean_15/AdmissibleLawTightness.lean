import KLS.UniformGeometricMoments
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! Genuine fixed-dimensional tightness and relative compactness of the
original admissible-law class, using the released uniform geometric tails.
Compactness of the class itself additionally requires its weak closedness. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

/-- The literal original admissible law class, as probability measures. -/
def admissibleProbabilityLaws (n : ℕ) : Set (ProbabilityMeasure (Space n)) :=
  {μ | admissibleMeasure (μ : Measure (Space n))}

/-- The full original class is tight in each fixed dimension. -/
theorem admissible_laws_tight :
    IsTightMeasureSet {μ : Measure (Space n) | admissibleMeasure μ} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal ((1/4:ℝ)*(1/3:ℝ)^k))
      atTop (𝓝 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/3)
      (by norm_num : (1/3:ℝ) < 1)).const_mul (1/4:ℝ)
    simpa using ENNReal.tendsto_ofReal hp
  obtain ⟨k,hk⟩ := ((tendsto_order.mp hlim).2 ε hε).exists
  refine ⟨closedBall (0 : Space n) ((2*(k:ℝ)+1)*isotropicTailRadius n),
    isCompact_closedBall _ _, ?_⟩
  intro μ hμ
  letI : IsProbabilityMeasure μ := hμ.isProb
  have ht := hμ.logConcave.isotropic_norm_tail_le hμ.isotropic k
  have hcomp : (closedBall (0 : Space n) ((2*(k:ℝ)+1)*isotropicTailRadius n))ᶜ =
      {x | (2*(k:ℝ)+1)*isotropicTailRadius n < ‖x‖} := by ext x; simp
  rw [hcomp]
  calc
    μ {x | (2*(k:ℝ)+1)*isotropicTailRadius n < ‖x‖} =
        ENNReal.ofReal (μ.real {x | (2*(k:ℝ)+1)*isotropicTailRadius n < ‖x‖}) := by
      exact (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    _ ≤ ENNReal.ofReal ((1/4:ℝ)*(1/3:ℝ)^k) := ENNReal.ofReal_le_ofReal ht
    _ ≤ ε := hk.le

/-- Prokhorov gives genuine compact closure of the actual admissible law
set. The conclusion deliberately does not assert closure preserves isotropy. -/
theorem admissible_probability_laws_compact_closure :
    IsCompact (closure (admissibleProbabilityLaws n)) := by
  apply isCompact_closure_of_isTightMeasureSet
  apply admissible_laws_tight.subset
  rintro μ ⟨ν,hν,rfl⟩
  exact hν

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.admissible_laws_tight
#print axioms KLS.DeterministicBridgeNext.admissible_probability_laws_compact_closure
