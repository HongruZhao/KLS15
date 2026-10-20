import ActualAppellQuotientReduction

/-! The constructed polynomial/law maximum is a genuine maximum over the
entire actual L² test-function class. Projection is justified internally. -/
noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem actualLp_norm_sq_eq_integral {n : ℕ} {μ : Measure (Space n)} (f : Lp ℝ 2 μ) :
    ‖f‖^2 = ∫ x, (f x)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [RCLike.inner_apply,conj_trivial,pow_two]

 theorem actualAppell_ratio_mem_Icc {n k : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    {h : ℝ} (hh : 0 < h)
    (hprevious : ∀ (ν : Measure (Space n)), admissibleMeasure ν → ∀ f : Space n → ℝ,
      MemLp f 2 ν → actualAppellEnergy ν f k ≤ h*(∫ x, (f x)^2 ∂ν))
    (f : Lp ℝ 2 μ) (hf : f ≠ 0) :
    ‖fullClassAppellTensor k f‖^2/(h*‖f‖^2) ∈ Icc (0 : ℝ) 1 := by
  have hn : 0 < ‖f‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  constructor
  · exact div_nonneg (sq_nonneg _) (mul_nonneg hh.le hn.le)
  · apply (div_le_one (mul_pos hh hn)).mpr
    have hp := hprevious μ hμ f (Lp.memLp f)
    rwa [actualAppellEnergy_eq_norm_sq,← actualLp_norm_sq_eq_integral] at hp

 theorem barrier_denominator_le_of_projection {φ : ℝ → ℝ}
    (hφpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < φ u)
    (hφanti : AntitoneOn φ (Icc (0 : ℝ) 1))
    {h y g₁ g₂ : ℝ} (hh : 0 < h) (hy : 0 ≤ y) (hg₁ : 0 < g₁) (hg : g₁ ≤ g₂)
    (hu₁ : y/(h*g₁) ∈ Icc (0 : ℝ) 1) (hu₂ : y/(h*g₂) ∈ Icc (0 : ℝ) 1) :
    g₁*φ (y/(h*g₁)) ≤ g₂*φ (y/(h*g₂)) := by
  have hu : y/(h*g₂) ≤ y/(h*g₁) :=
    div_le_div_of_nonneg_left hy (mul_pos hh hg₁) (mul_le_mul_of_nonneg_left hg hh.le)
  exact mul_le_mul hg (hφanti hu₂ hu₁ hu)
    (hφpos _ hu₁).le (hg₁.le.trans hg)

 theorem normalized_polynomial_maximizer_nonneg {n k : ℕ}
    {h : ℝ} (hh : 0 < h) {φ : ℝ → ℝ}
    (hφpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < φ u)
    (hprevious : ∀ (μ : Measure (Space n)), admissibleMeasure μ → ∀ f : Space n → ℝ,
      MemLp f 2 μ → actualAppellEnergy μ f k ≤ h*(∫ x, (f x)^2 ∂μ))
    (z : ProbabilityMeasure (Space n) × (DegreeIndex n (k+1) → ℝ))
    (hz : z ∈ normalizedPolynomialPairs (degreeExponent n (k+1))) :
    0 ≤ actualNormalizedAppellQuotient (z.1 : Measure (Space n))
      (polynomialEval (boundedDegreePolynomial z.2)) k h φ := by
  have hn : ‖polynomialLp hz.1.logConcave (boundedDegreePolynomial z.2)‖^2 = 1 := by
    exact (polynomialCoefficientEnergy_eq_norm_sq _ hz.1 z.2).symm.trans hz.2
  have hne : polynomialLp hz.1.logConcave (boundedDegreePolynomial z.2) ≠ 0 := by
    intro he
    simp only [he,norm_zero,zero_pow (by omega : 2 ≠ 0)] at hn
    norm_num at hn
  rw [polynomial_normalized_quotient_eq hz.1 z.2 hz.2]
  exact div_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
    (hφpos _ (actualAppell_ratio_mem_Icc hz.1 hh hprevious _ hne)).le)

 theorem actual_polynomial_quotient_le_joint_max {n k : ℕ}
    {h : ℝ} (hh : 0 < h) {φ : ℝ → ℝ}
    (hφpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < φ u)
    (hprevious : ∀ (μ : Measure (Space n)), admissibleMeasure μ → ∀ f : Space n → ℝ,
      MemLp f 2 μ → actualAppellEnergy μ f k ≤ h*(∫ x, (f x)^2 ∂μ))
    (z : ProbabilityMeasure (Space n) × (DegreeIndex n (k+1) → ℝ))
    (hz : z ∈ normalizedPolynomialPairs (degreeExponent n (k+1)))
    (hmax : ∀ w ∈ normalizedPolynomialPairs (degreeExponent n (k+1)),
      actualNormalizedAppellQuotient (w.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial w.2)) k h φ ≤
      actualNormalizedAppellQuotient (z.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial z.2)) k h φ)
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (c : DegreeIndex n (k+1) → ℝ) :
    coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
      (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ
      (polynomialLp hμ.logConcave (boundedDegreePolynomial c)) ≤
    actualNormalizedAppellQuotient (z.1 : Measure (Space n))
      (polynomialEval (boundedDegreePolynomial z.2)) k h φ := by
  by_cases hc : polynomialLp hμ.logConcave (boundedDegreePolynomial c) = 0
  · simpa only [hc,coefficientQuotient,map_zero,norm_zero,zero_pow (by omega : 2 ≠ 0),
      zero_div] using normalized_polynomial_maximizer_nonneg hh hφpos hprevious z hz
  · obtain ⟨a,ha,han⟩ := normalize_actual_polynomial_pair hμ c hc
    have hm := hmax (μ,a • c) han
    rw [polynomial_normalized_quotient_eq hμ (a • c) han.2] at hm
    change coefficientQuotient _ _ _ _
      (polynomialLp hμ.logConcave (polynomialCombination (degreeExponent n (k+1)) (a • c))) ≤ _ at hm
    rwa [polynomialLp_combination_smul,coefficientQuotient_smul _ _ _ _ _ ha] at hm

/-- Every actual L² test function is bounded by the constructed joint
law/polynomial maximum, with no maximizer or projection premise. -/
 theorem actual_L2_quotient_le_joint_max {n k : ℕ}
    {h : ℝ} (hh : 0 < h) {φ : ℝ → ℝ}
    (hφpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < φ u)
    (hφanti : AntitoneOn φ (Icc (0 : ℝ) 1))
    (hprevious : ∀ (μ : Measure (Space n)), admissibleMeasure μ → ∀ f : Space n → ℝ,
      MemLp f 2 μ → actualAppellEnergy μ f k ≤ h*(∫ x, (f x)^2 ∂μ))
    (z : ProbabilityMeasure (Space n) × (DegreeIndex n (k+1) → ℝ))
    (hz : z ∈ normalizedPolynomialPairs (degreeExponent n (k+1)))
    (hmax : ∀ w ∈ normalizedPolynomialPairs (degreeExponent n (k+1)),
      actualNormalizedAppellQuotient (w.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial w.2)) k h φ ≤
      actualNormalizedAppellQuotient (z.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial z.2)) k h φ)
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (f : Lp ℝ 2 (μ : Measure (Space n))) :
    coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
      (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ f ≤
    actualNormalizedAppellQuotient (z.1 : Measure (Space n))
      (polynomialEval (boundedDegreePolynomial z.2)) k h φ := by
  obtain ⟨c,hcnorm,hce⟩ := exists_actual_polynomial_Appell_energy_projection (d := k+1) hμ f
  let p := polynomialLp hμ.logConcave (boundedDegreePolynomial c)
  have henergy (r : ℕ) (hr : r ≤ k+1) :
      ‖fullClassAppellTensor r p‖^2 = ‖fullClassAppellTensor r f‖^2 := by
    rw [← actualAppellEnergy_eq_norm_sq,← actualAppellEnergy_eq_norm_sq]
    exact (actualAppellEnergy_congr_ae (polynomialLp_coe hμ.logConcave _)).trans (hce r hr)
  have hpmax := actual_polynomial_quotient_le_joint_max hh hφpos hprevious z hz hmax hμ c
  by_cases hp : p = 0
  · have hx : ‖fullClassAppellTensor (k+1) f‖^2 = 0 := by
      rw [← henergy (k+1) le_rfl,hp]
      change ‖fullClassAppellLinearMap hμ.logConcave (k+1) 0‖^2 = 0
      simp only [map_zero,norm_zero,zero_pow (by omega : 2 ≠ 0)]
    have hfzero : coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
        (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ f = 0 := by
      unfold coefficientQuotient
      change ‖fullClassAppellTensor (k+1) f‖^2/(_*φ _) = 0
      rw [hx,zero_div]
    rw [hfzero]
    exact normalized_polynomial_maximizer_nonneg hh hφpos hprevious z hz
  · have hpn : 0 < ‖p‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hp)
    have hgn : ‖p‖^2 ≤ ‖f‖^2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hcnorm
    have hf : f ≠ 0 := by
      intro he
      simp only [he,norm_zero,zero_pow (by omega : 2 ≠ 0)] at hgn
      linarith
    have hup := actualAppell_ratio_mem_Icc hμ hh hprevious p hp
    have huf := actualAppell_ratio_mem_Icc hμ hh hprevious f hf
    have hdenp : 0 < ‖p‖^2*φ (‖fullClassAppellTensor k f‖^2/(h*‖p‖^2)) := by
      rw [← henergy k (by omega)]
      exact mul_pos hpn (hφpos _ hup)
    have hden := barrier_denominator_le_of_projection hφpos hφanti hh
      (sq_nonneg ‖fullClassAppellTensor k f‖) hpn hgn
      (by rwa [henergy k (by omega)] at hup) huf
    have hq : coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
        (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ f ≤
        coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
          (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ p := by
      change ‖fullClassAppellTensor (k+1) f‖^2/
        (‖f‖^2*φ (‖fullClassAppellTensor k f‖^2/(h*‖f‖^2))) ≤
        ‖fullClassAppellTensor (k+1) p‖^2/
        (‖p‖^2*φ (‖fullClassAppellTensor k p‖^2/(h*‖p‖^2)))
      rw [henergy (k+1) le_rfl,henergy k (by omega)]
      exact div_le_div_of_nonneg_left (sq_nonneg _) hdenp hden
    exact hq.trans hpmax

 theorem exists_actual_joint_L2_quotient_maximizer {n k : ℕ}
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n)))
    {h : ℝ} (hh : 0 < h) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 1))
    (hφpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < φ u)
    (hφanti : AntitoneOn φ (Icc (0 : ℝ) 1))
    (hprevious : ∀ (μ : Measure (Space n)), admissibleMeasure μ → ∀ f : Space n → ℝ,
      MemLp f 2 μ → actualAppellEnergy μ f k ≤ h*(∫ x, (f x)^2 ∂μ)) :
    ∃ z ∈ normalizedPolynomialPairs (degreeExponent n (k+1)),
      ∀ (μ : ProbabilityMeasure (Space n)) (hμ : admissibleMeasure (μ : Measure (Space n)))
        (f : Lp ℝ 2 (μ : Measure (Space n))),
      coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
        (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ f ≤
      actualNormalizedAppellQuotient (z.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial z.2)) k h φ := by
  obtain ⟨z,hz,hmax⟩ := exists_actual_normalized_polynomial_quotient_maximizer
    hμ₀ hh hφ hφpos hprevious
  exact ⟨z,hz,fun μ hμ f => actual_L2_quotient_le_joint_max hh hφpos hφanti hprevious z hz hmax hμ f⟩

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_L2_quotient_le_joint_max
#print axioms KLS.DeterministicBridgeNext.exists_actual_joint_L2_quotient_maximizer
