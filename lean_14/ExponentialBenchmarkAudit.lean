import KLS14452512512Combined
import CorrelatedCubicRationalTangents239

/-! Actual scalar quartic benchmark, quantitative failure of the imported
decreasing cubic seed to attain that benchmark, and the algebraic floor of
the current norm-based endgame. The quartic theorem here is scalar; the
all-dimensional mathematical support decomposition is documented separately. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace KLSImprovement.CombinedExponentialAudit
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSImprovement.ActualProductCumulants KLSImprovement.ProductAdmissible
open KLSImprovement.Exponential KLSImprovement.ExponentialCriticalGram
open KLSImprovement.ActualScalarCritical KLSImprovement.ProductCubic
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)
local instance : IsProbabilityMeasure (centeredProductMeasure 1) :=
  centeredProduct_isProbability 1

theorem scalar_quartic_observation_le {f : Space 1 → ℝ}
    (hf : MemLp f 2 (centeredProductMeasure 1)) :
    actualAppellEnergy (centeredProductMeasure 1) f 4 / (Nat.factorial 4 : ℝ)^2 ≤
      20 * (∫ x, (f x)^2 ∂centeredProductMeasure 1) := by
  have h := KLSImprovement.FiniteIntegralGram.observation_le_of_integral_gram_rows
    (expMeasure 1) (fun _ : Fin 1 => appell 3)
    (fun _ => (show MemLp (appell 3) 2 (expMeasure 1) from scalarAppell_memLp 4))
    (by norm_num : (0 : ℝ) < 11520)
    (by
      intro i
      simp only [Fintype.sum_unique, ←pow_two, integral_appell_sq]
      norm_num)
    (pullback_memLp hf)
  rw [original_energy_one, original_coefficient_eq_scalar_integral hf 3, centered_integral]
  simp only [Fintype.sum_unique] at h
  norm_num only [Nat.factorial, Nat.cast_ofNat] at ⊢
  simp only [pullback] at h ⊢
  linarith

def quarticWitness (x : Space 1) : ℝ := (x 0)^4 - 6*(x 0)^2 - 8*x 0 - 3

theorem centered_coordinate_power_memLp (k : ℕ) :
    MemLp (fun x : Space 1 => (x 0)^k) 2 (centeredProductMeasure 1) := by
  apply ((centeredProduct_logConcave 1).memLp_two_norm_pow k).mono' (by fun_prop)
  exact .of_forall (fun x => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le x 0) k)

theorem quarticWitness_memLp : MemLp quarticWitness 2 (centeredProductMeasure 1) := by
  have hp := ((centered_coordinate_power_memLp 4).sub
    ((centered_coordinate_power_memLp 2).const_mul 6)).sub
    (((centeredProduct_isIsotropic 1).memLp_coordinate 0).const_mul 8)
  exact hp.sub (memLp_const (μ := centeredProductMeasure 1) (p := 2) (3 : ℝ))

theorem pullback_quarticWitness : pullback quarticWitness = appell 3 := by
  funext y
  change ((-1 : ℝ)+y)^4 - 6*((-1 : ℝ)+y)^2 - 8*((-1 : ℝ)+y) - 3 = appell 3 y
  norm_num [appell]
  ring

theorem quarticWitness_square :
    (∫ x, (quarticWitness x)^2 ∂centeredProductMeasure 1) = 11520 := by
  rw [centered_integral]
  change (∫ y, (pullback quarticWitness y)^2 ∂expMeasure 1) = 11520
  rw [pullback_quarticWitness, integral_appell_sq]
  norm_num

theorem quarticWitness_energy_four :
    actualAppellEnergy (centeredProductMeasure 1) quarticWitness 4 = 11520^2 := by
  rw [original_energy_one, original_coefficient_eq_scalar_integral quarticWitness_memLp 3,
    pullback_quarticWitness, integral_appell_mul]
  norm_num

theorem scalar_quartic_cap_is_sharp {C : ℝ}
    (hC : ∀ f : Space 1 → ℝ, MemLp f 2 (centeredProductMeasure 1) →
      actualAppellEnergy (centeredProductMeasure 1) f 4 / (Nat.factorial 4 : ℝ)^2 ≤
        C * (∫ x, (f x)^2 ∂centeredProductMeasure 1)) : 20 ≤ C := by
  have h := hC quarticWitness quarticWitness_memLp
  rw [quarticWitness_energy_four, quarticWitness_square] at h
  norm_num at h
  linarith

theorem imported_quartic_flat_ratio : (200000 : ℝ) / 11520 = 625 / 36 := by norm_num

def normalizedHead (i : Fin 3) (y : ℝ) : ℝ :=
  appell (i.val + 1) y / ((i.val + 2).factorial : ℝ)

def threeHeadGram : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![2, 3, 4], ![3, 6, 10], ![4, 10, 20]]

/-- The genuine scalar measure Gram of the normalized quadratic, cubic,
and quartic Appell observations. -/
theorem actual_three_head_gram (i j : Fin 3) :
    (∫ y, normalizedHead i y * normalizedHead j y ∂expMeasure 1) =
      threeHeadGram i j := by
  unfold normalizedHead
  simp_rw [div_mul_div_comm]
  rw [integral_div, integral_appell_mul]
  fin_cases i <;> fin_cases j <;> norm_num [threeHeadGram]

/-- Even the curved seed coefficient stays strictly above 10.7769641 on
the whole parameter interval, whereas the product flat cubic cap is 6. -/
theorem imported_cubic_shape_global_lower {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (107769641 / 10000000 : ℝ) <
      KLSBelow25.CreationSeed239.B * KLSBelow25.CreationSeed239.seedPhi u := by
  have h := (KLSBelow25.CreationSeed239.seedPhi_range hu).1
  norm_num only [KLSBelow25.CreationSeed239.seedT] at h
  norm_num only [KLSBelow25.CreationSeed239.B]
  linarith

/-- The current scalar certificate uses p>1. At any benchmark-admissible
rate K>=4, converting its norm estimate by 1+Kp cannot attain four or five. -/
theorem current_norm_endgame_strictly_above_five {K p : ℝ}
    (hK : 4 ≤ K) (hp : 1 < p) : 5 < 1 + K*p := by
  have hprod := mul_nonneg (sub_nonneg.mpr hK) (sub_pos.mpr hp).le
  nlinarith

theorem imported_endgame_parameters :
    KLSBelow25.ProjectionThreeHeadRefinedNumerics.K = (8051 / 625 : ℝ) ∧
    KLSBelow25.ProjectionThreeHeadRefinedNumerics.C = (1957 / 40000 : ℝ) ∧
    KLSBelow25.ProjectionThreeHeadRefinedNumerics.p = (13054 / 12500 : ℝ) := by
  exact ⟨rfl, rfl, rfl⟩

end KLSImprovement.CombinedExponentialAudit
#print axioms KLSImprovement.CombinedExponentialAudit.scalar_quartic_observation_le
#print axioms KLSImprovement.CombinedExponentialAudit.quarticWitness_memLp
#print axioms KLSImprovement.CombinedExponentialAudit.quarticWitness_square
#print axioms KLSImprovement.CombinedExponentialAudit.quarticWitness_energy_four
#print axioms KLSImprovement.CombinedExponentialAudit.scalar_quartic_cap_is_sharp
#print axioms KLSImprovement.CombinedExponentialAudit.imported_quartic_flat_ratio
#print axioms KLSImprovement.CombinedExponentialAudit.actual_three_head_gram
#print axioms KLSImprovement.CombinedExponentialAudit.imported_cubic_shape_global_lower
#print axioms KLSImprovement.CombinedExponentialAudit.current_norm_endgame_strictly_above_five
#print axioms KLSImprovement.CombinedExponentialAudit.imported_endgame_parameters
