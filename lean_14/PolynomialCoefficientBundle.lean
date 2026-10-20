import PolynomialLawNondegeneracy

/-! Actual finite monomial coefficient bundles over admissible laws. The
quadratic form is exactly the L² norm of the represented polynomial. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal BigOperators
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 def polynomialCombination {n : ℕ} {I : Type*} [Fintype I]
    (d : I → (Fin n →₀ ℕ)) (c : I → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, MvPolynomial.monomial (d i) (c i)

 theorem polynomialCombination_coeff {n : ℕ} {I : Type*} [Fintype I]
    [DecidableEq I] (d : I → (Fin n →₀ ℕ)) (hd : Function.Injective d)
    (c : I → ℝ) (j : I) : (polynomialCombination d c).coeff (d j) = c j := by
  simp only [polynomialCombination,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,hd.eq_iff]
  simp

 theorem polynomialCombination_ne_zero {n : ℕ} {I : Type*} [Fintype I]
    [DecidableEq I] (d : I → (Fin n →₀ ℕ)) (hd : Function.Injective d)
    {c : I → ℝ} (hc : c ≠ 0) : polynomialCombination d c ≠ 0 := by
  intro he
  apply hc
  funext j
  have h := congrArg (fun p : MvPolynomial (Fin n) ℝ => p.coeff (d j)) he
  simpa only [polynomialCombination_coeff d hd,MvPolynomial.coeff_zero,Finsupp.zero_apply,Pi.zero_apply] using h

 theorem polynomialEval_combination {n : ℕ} {I : Type*} [Fintype I]
    (d : I → (Fin n →₀ ℕ)) (c : I → ℝ) (x : Space n) :
    polynomialEval (polynomialCombination d c) x = ∑ i, c i*coordinateMonomial (d i) x := by
  simp only [polynomialCombination,polynomialEval,MvPolynomial.eval_sum,MvPolynomial.eval_monomial]
  rfl

 def polynomialGramEntry {n : ℕ} {I : Type*} (d : I → (Fin n →₀ ℕ))
    (μ : ProbabilityMeasure (Space n)) (i j : I) : ℝ :=
  ∫ x, polynomialEval ((MvPolynomial.monomial (d i) 1)*(MvPolynomial.monomial (d j) 1)) x
    ∂(μ : Measure (Space n))

 def polynomialCoefficientEnergy {n : ℕ} {I : Type*} [Fintype I]
    (d : I → (Fin n →₀ ℕ)) (μ : ProbabilityMeasure (Space n)) (c : I → ℝ) : ℝ :=
  ∑ i, ∑ j, c i*c j*polynomialGramEntry d μ i j

 theorem polynomialGramEntry_eq {n : ℕ} {I : Type*} (d : I → (Fin n →₀ ℕ))
    (μ : ProbabilityMeasure (Space n)) (i j : I) :
    polynomialGramEntry d μ i j =
    ∫ x, coordinateMonomial (d i) x*coordinateMonomial (d j) x ∂(μ : Measure (Space n)) := by
  unfold polynomialGramEntry
  congr 1
  funext x
  simp only [polynomialEval,MvPolynomial.eval_mul,MvPolynomial.eval_monomial,one_mul]
  rfl

 theorem polynomialCoefficientEnergy_eq_integral_sq {n : ℕ} {I : Type*} [Fintype I]
    (d : I → (Fin n →₀ ℕ)) {μ : ProbabilityMeasure (Space n)}
    (hμ : admissibleMeasure (μ : Measure (Space n))) (c : I → ℝ) :
    polynomialCoefficientEnergy d μ c =
      ∫ x, (polynomialEval (polynomialCombination d c) x)^2 ∂(μ : Measure (Space n)) := by
  have hmono (i : I) := coordinateMonomial_memLp_two hμ.logConcave (d i)
  have hij (i j : I) : Integrable (fun x =>
      (c i*c j)*(coordinateMonomial (d i) x*coordinateMonomial (d j) x))
      (μ : Measure (Space n)) := by
    convert ((hmono i).integrable_mul (hmono j)).const_mul (c i*c j) using 1
  have hexp (x : Space n) : (polynomialEval (polynomialCombination d c) x)^2 =
      ∑ i, ∑ j, (c i*c j)*(coordinateMonomial (d i) x*coordinateMonomial (d j) x) := by
    rw [polynomialEval_combination,pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hexp]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hij i j))]
  unfold polynomialCoefficientEnergy
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Finset.univ (fun j _ => hij i j)]
  simp_rw [integral_const_mul,← polynomialGramEntry_eq]

 theorem polynomialCoefficientEnergy_pos {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (d : I → (Fin n →₀ ℕ)) (hd : Function.Injective d)
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    {c : I → ℝ} (hc : c ≠ 0) : 0 < polynomialCoefficientEnergy d μ c := by
  rw [polynomialCoefficientEnergy_eq_integral_sq d hμ c]
  exact integral_polynomialEval_sq_pos hμ _ (polynomialCombination_ne_zero d hd hc)

 theorem polynomialCoefficientEnergy_smul {n : ℕ} {I : Type*} [Fintype I]
    (d : I → (Fin n →₀ ℕ)) (μ : ProbabilityMeasure (Space n)) (c : I → ℝ) (r : ℝ) :
    polynomialCoefficientEnergy d μ (r • c) = r^2*polynomialCoefficientEnergy d μ c := by
  simp only [polynomialCoefficientEnergy,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

 theorem polynomialCoefficientEnergy_continuousOn {n : ℕ} {I : Type*} [Fintype I]
    (d : I → (Fin n →₀ ℕ)) :
    ContinuousOn (fun z : ProbabilityMeasure (Space n) × (I → ℝ) =>
      polynomialCoefficientEnergy d z.1 z.2) ((admissibleProbabilityLaws n) ×ˢ univ) := by
  unfold polynomialCoefficientEnergy
  apply continuousOn_finsetSum
  intro i hi
  apply continuousOn_finsetSum
  intro j hj
  apply ContinuousOn.mul
  · exact ((continuous_apply i).comp continuous_snd).continuousOn.mul
      ((continuous_apply j).comp continuous_snd).continuousOn
  · exact (continuousOn_integral_polynomialEval _).comp continuous_fst.continuousOn
      (by intro z hz; exact hz.1)

/-- Actual-law compactness and actual polynomial nondegeneracy produce a
uniform positive Gram lower bound for any fixed finite list of distinct monomials. -/
 theorem exists_uniform_polynomialCoefficientEnergy_lower
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (d : I → (Fin n →₀ ℕ)) (hd : Function.Injective d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ ∈ admissibleProbabilityLaws n, ∀ c : I → ℝ,
      δ*‖c‖^2 ≤ polynomialCoefficientEnergy d μ c := by
  let S := (admissibleProbabilityLaws n) ×ˢ sphere (0 : I → ℝ) 1
  have hS : IsCompact S :=
    (isCompact_admissible_probability_laws n).prod (isCompact_sphere _ _)
  have hcont : ContinuousOn (fun z : ProbabilityMeasure (Space n) × (I → ℝ) =>
      polynomialCoefficientEnergy d z.1 z.2) S :=
    (polynomialCoefficientEnergy_continuousOn d).mono (by intro z hz; exact ⟨hz.1,mem_univ _⟩)
  have hpos : ∀ z ∈ S, 0 < polynomialCoefficientEnergy d z.1 z.2 := by
    intro z hz
    apply polynomialCoefficientEnergy_pos d hd hz.1
    intro he
    have hn : ‖z.2‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hz.2
    simp only [he,norm_zero] at hn
    norm_num at hn
  obtain ⟨δ,hδ,hbound⟩ := hS.exists_forall_le' hcont hpos
  refine ⟨δ,hδ,?_⟩
  intro μ hμ c
  by_cases hc : c = 0
  · simp only [hc,norm_zero,zero_pow (by omega : 2 ≠ 0),mul_zero]
    rw [polynomialCoefficientEnergy_eq_integral_sq d hμ]
    exact integral_nonneg fun x => sq_nonneg _
  · have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hunit : ‖‖c‖⁻¹ • c‖ = 1 := by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hn.ne']
    have hb := hbound (μ,‖c‖⁻¹ • c) ⟨hμ,by simpa only [mem_sphere,dist_zero_right] using hunit⟩
    rw [polynomialCoefficientEnergy_smul] at hb
    calc
      δ*‖c‖^2 ≤ (‖c‖⁻¹^2*polynomialCoefficientEnergy d μ c)*‖c‖^2 :=
        mul_le_mul_of_nonneg_right hb (sq_nonneg _)
      _ = _ := by field_simp [ne_of_gt hn]

 def normalizedPolynomialPairs {n : ℕ} {I : Type*} [Fintype I]
    (d : I → (Fin n →₀ ℕ)) : Set (ProbabilityMeasure (Space n) × (I → ℝ)) :=
  {z | z.1 ∈ admissibleProbabilityLaws n ∧ polynomialCoefficientEnergy d z.1 z.2 = 1}

 theorem isClosed_normalizedPolynomialPairs {n : ℕ} {I : Type*} [Fintype I]
    (d : I → (Fin n →₀ ℕ)) : IsClosed (normalizedPolynomialPairs d) := by
  have hc := (polynomialCoefficientEnergy_continuousOn d).preimage_isClosed_of_isClosed
    ((isClosed_admissible_probability_laws n).prod isClosed_univ)
    (isClosed_singleton : IsClosed ({1} : Set ℝ))
  convert hc using 1
  ext z
  simp only [normalizedPolynomialPairs,mem_setOf_eq,mem_inter_iff,mem_prod,mem_univ,and_true,
    mem_preimage,mem_singleton_iff]

/-- The literal unit-L² polynomial coefficient bundle over all admissible laws
is compact. This constructs the paper's finite-dimensional normalization step. -/
 theorem isCompact_normalizedPolynomialPairs {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (d : I → (Fin n →₀ ℕ)) (hd : Function.Injective d) :
    IsCompact (normalizedPolynomialPairs d) := by
  obtain ⟨δ,hδ,hbound⟩ := exists_uniform_polynomialCoefficientEnergy_lower d hd
  let R := δ⁻¹+1
  apply ((isCompact_admissible_probability_laws n).prod
    (isCompact_closedBall (0 : I → ℝ) R)).of_isClosed_subset
      (isClosed_normalizedPolynomialPairs d)
  intro z hz
  refine ⟨hz.1,?_⟩
  have hle := hbound z.1 hz.1 z.2
  rw [hz.2] at hle
  have hsq : ‖z.2‖^2 ≤ δ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have hx : ‖z.2‖ ≤ ‖z.2‖^2+1 := by nlinarith [sq_nonneg (‖z.2‖-1),norm_nonneg z.2]
  have hnorm : ‖z.2‖ ≤ R := hx.trans (by dsimp [R]; linarith)
  simpa only [mem_closedBall,dist_zero_right] using hnorm

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.polynomialCoefficientEnergy_pos
#print axioms KLS.DeterministicBridgeNext.polynomialCoefficientEnergy_continuousOn

#print axioms KLS.DeterministicBridgeNext.exists_uniform_polynomialCoefficientEnergy_lower
#print axioms KLS.DeterministicBridgeNext.isCompact_normalizedPolynomialPairs
