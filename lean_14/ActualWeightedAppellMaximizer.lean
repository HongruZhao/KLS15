import ActualWeightedAppellEnergy
import ActualJointL2QuotientMaximizer
import ActualTiltMaximum

/-! Attainment of the finite weighted Appell Rayleigh quotient over the
literal admissible law class and every actual L2 test. -/
noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_normalized_weighted_polynomial_maximizer {n N : ℕ}
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n)))
    (K : ℝ) :
    ∃ z∈normalizedPolynomialPairs (degreeExponent n N),
      ∀ w∈normalizedPolynomialPairs (degreeExponent n N),
        actualWeightedAppellEnergy (w.1 : Measure (Space n))
          (polynomialEval (boundedDegreePolynomial w.2)) K N ≤
        actualWeightedAppellEnergy (z.1 : Measure (Space n))
          (polynomialEval (boundedDegreePolynomial z.2)) K N :=
  (isCompact_boundedDegree_normalizedPolynomialPairs n N).exists_isMaxOn
    (normalizedPolynomialPairs_nonempty_of_admissible hμ₀)
    (actualWeightedAppellEnergy_polynomial_continuousOn K)

theorem weighted_polynomial_bound_of_normalized_maximum {n N : ℕ} {K : ℝ} (hK : 0<K)
    (z : ProbabilityMeasure (Space n) × (DegreeIndex n N → ℝ))
    (hz : z∈normalizedPolynomialPairs (degreeExponent n N))
    (hmax : ∀ w∈normalizedPolynomialPairs (degreeExponent n N),
      actualWeightedAppellEnergy (w.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial w.2)) K N ≤
      actualWeightedAppellEnergy (z.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial z.2)) K N)
    {ν : ProbabilityMeasure (Space n)} (hν : admissibleMeasure (ν : Measure (Space n)))
    (c : DegreeIndex n N → ℝ) :
    actualWeightedAppellEnergy (ν : Measure (Space n))
      (polynomialLp hν.logConcave (boundedDegreePolynomial c)) K N ≤
    actualWeightedAppellEnergy (z.1 : Measure (Space n))
      (polynomialEval (boundedDegreePolynomial z.2)) K N*
        ‖polynomialLp hν.logConcave (boundedDegreePolynomial c)‖^2 := by
  let p := polynomialLp hν.logConcave (boundedDegreePolynomial c)
  have hnonneg := actualWeightedAppellEnergy_nonneg (z.1 : Measure (Space n))
    (polynomialEval (boundedDegreePolynomial z.2)) hK N
  by_cases hp : p=0
  · change actualWeightedAppellEnergy _ p _ _ ≤ _*‖p‖^2
    rw [hp,actualWeightedAppellEnergy_zero hν.logConcave]
    simp
  · obtain ⟨a,ha,han⟩ := normalize_actual_polynomial_pair hν c hp
    have hm := hmax (ν,a • c) han
    rw [←actualWeightedAppellEnergy_polynomialLp hν.logConcave] at hm
    change actualWeightedAppellEnergy (ν : Measure (Space n))
      (polynomialLp hν.logConcave (polynomialCombination (degreeExponent n N) (a • c))) K N ≤ _ at hm
    rw [polynomialLp_combination_smul,actualWeightedAppellEnergy_smul hν.logConcave] at hm
    have hn : a^2*‖p‖^2=1 := by
      have h := (polynomialCoefficientEnergy_eq_norm_sq _ hν (a • c)).symm.trans han.2
      change ‖polynomialLp hν.logConcave (polynomialCombination (degreeExponent n N) (a • c))‖^2=1 at h
      rw [polynomialLp_combination_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at h
      exact h
    have hp2 : 0<‖p‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hp)
    have hm' := mul_le_mul_of_nonneg_right hm hp2.le
    change _*actualWeightedAppellEnergy _ p _ _*‖p‖^2 ≤ _ at hm'
    have hid : a^2*actualWeightedAppellEnergy (ν : Measure (Space n)) p K N*‖p‖^2=
        actualWeightedAppellEnergy (ν : Measure (Space n)) p K N := by
      calc
        _ = (a^2*‖p‖^2)*actualWeightedAppellEnergy (ν : Measure (Space n)) p K N := by ring
        _ = _ := by rw [hn,one_mul]
    rw [hid] at hm'
    exact hm'

theorem weighted_L2_bound_of_normalized_maximum {n N : ℕ} {K : ℝ} (hK : 0<K)
    (z : ProbabilityMeasure (Space n) × (DegreeIndex n N → ℝ))
    (hz : z∈normalizedPolynomialPairs (degreeExponent n N))
    (hmax : ∀ w∈normalizedPolynomialPairs (degreeExponent n N),
      actualWeightedAppellEnergy (w.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial w.2)) K N ≤
      actualWeightedAppellEnergy (z.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial z.2)) K N)
    {ν : ProbabilityMeasure (Space n)} (hν : admissibleMeasure (ν : Measure (Space n)))
    (g : Lp ℝ 2 (ν : Measure (Space n))) :
    actualWeightedAppellEnergy (ν : Measure (Space n)) g K N ≤
      actualWeightedAppellEnergy (z.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial z.2)) K N*‖g‖^2 := by
  obtain ⟨c,hcnorm,hce⟩ := exists_actual_polynomial_Appell_energy_projection (d:=N) hν g
  have he : actualWeightedAppellEnergy (ν : Measure (Space n))
      (polynomialLp hν.logConcave (boundedDegreePolynomial c)) K N=
        actualWeightedAppellEnergy (ν : Measure (Space n)) g K N := by
    rw [actualWeightedAppellEnergy_polynomialLp]
    unfold actualWeightedAppellEnergy
    apply Finset.sum_congr rfl
    intro d hd
    rw [hce d (Finset.mem_Icc.mp hd).2]
  have hb := weighted_polynomial_bound_of_normalized_maximum hK z hz hmax hν c
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hcnorm)
    (actualWeightedAppellEnergy_nonneg _ _ hK N))

theorem exists_actual_weighted_L2_maximizer {n N : ℕ} {K : ℝ} (hK : 0<K)
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n))) :
    ∃ (μ : ProbabilityMeasure (Space n)) (hμ : admissibleMeasure (μ : Measure (Space n)))
      (c : DegreeIndex n N → ℝ),
      let f := polynomialLp hμ.logConcave (boundedDegreePolynomial c)
      ‖f‖=1 ∧
      ∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν : Measure (Space n)))
        (g : Lp ℝ 2 (ν : Measure (Space n))),
        actualWeightedAppellEnergy (ν : Measure (Space n)) g K N ≤
          actualWeightedAppellEnergy (μ : Measure (Space n)) f K N*‖g‖^2 := by
  obtain ⟨z,hz,hm⟩ := exists_actual_normalized_weighted_polynomial_maximizer hμ₀ K
  have hn : ‖polynomialLp hz.1.logConcave (boundedDegreePolynomial z.2)‖^2=1 :=
    (polynomialCoefficientEnergy_eq_norm_sq _ hz.1 z.2).symm.trans hz.2
  refine ⟨z.1,hz.1,z.2,by nlinarith [norm_nonneg (polynomialLp hz.1.logConcave
    (boundedDegreePolynomial z.2))],?_⟩
  intro ν hν g
  simpa only [actualWeightedAppellEnergy_polynomialLp] using
    weighted_L2_bound_of_normalized_maximum hK z hz hm hν g

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.exists_actual_weighted_L2_maximizer
