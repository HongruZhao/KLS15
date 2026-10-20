import PolynomialCoefficientBundle
import Mathlib.Data.Finsupp.Weight
import Mathlib.Algebra.MvPolynomial.Degrees

/-! Canonical total-degree polynomial coefficient space. This instantiates the
compact normalized bundle with every monomial of total degree at most d. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal BigOperators
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 def DegreeIndex (n d : ℕ) := {s : Fin n →₀ ℕ | s.degree ≤ d}

 instance degreeIndexFintype (n d : ℕ) : Fintype (DegreeIndex n d) :=
  (Finsupp.finite_of_degree_le (σ := Fin n) d).fintype

 instance degreeIndexDecidableEq (n d : ℕ) : DecidableEq (DegreeIndex n d) :=
  Classical.decEq _

 def degreeExponent (n d : ℕ) : DegreeIndex n d → (Fin n →₀ ℕ) := Subtype.val

 theorem degreeExponent_injective (n d : ℕ) : Function.Injective (degreeExponent n d) :=
  Subtype.val_injective

 def boundedDegreePolynomial {n d : ℕ} (c : DegreeIndex n d → ℝ) : MvPolynomial (Fin n) ℝ :=
  polynomialCombination (degreeExponent n d) c

 theorem boundedDegreePolynomial_totalDegree_le {n d : ℕ} (c : DegreeIndex n d → ℝ) :
    (boundedDegreePolynomial c).totalDegree ≤ d := by
  unfold boundedDegreePolynomial polynomialCombination
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro i hi
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans i.property

 theorem boundedDegreePolynomial_coeff {n d : ℕ} (c : DegreeIndex n d → ℝ)
    (s : DegreeIndex n d) : (boundedDegreePolynomial c).coeff s.val = c s :=
  polynomialCombination_coeff _ (degreeExponent_injective n d) c s

 theorem boundedDegreePolynomial_representation {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) :
    boundedDegreePolynomial (fun s : DegreeIndex n d => p.coeff s.val) = p := by
  apply MvPolynomial.ext
  intro s
  by_cases hs : s.degree ≤ d
  · exact boundedDegreePolynomial_coeff _ (⟨s,hs⟩ : DegreeIndex n d)
  · have hcp : p.coeff s = 0 := by
      apply MvPolynomial.notMem_support_iff.mp
      intro hm
      exact hs ((MvPolynomial.le_totalDegree hm).trans hp)
    rw [hcp]
    unfold boundedDegreePolynomial polynomialCombination
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [MvPolynomial.coeff_monomial,if_neg]
    intro he
    exact hs (he ▸ i.property)

 theorem boundedDegreePolynomial_injective (n d : ℕ) :
    Function.Injective (@boundedDegreePolynomial n d) := by
  intro c e h
  funext s
  have hs := congrArg (fun p : MvPolynomial (Fin n) ℝ => p.coeff s.val) h
  simpa only [boundedDegreePolynomial_coeff] using hs

 theorem isCompact_boundedDegree_normalizedPolynomialPairs (n d : ℕ) :
    IsCompact (normalizedPolynomialPairs (degreeExponent n d)) :=
  isCompact_normalizedPolynomialPairs _ (degreeExponent_injective n d)

 theorem exists_uniform_boundedDegree_L2_lower (n d : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ ∈ admissibleProbabilityLaws n, ∀ c : DegreeIndex n d → ℝ,
      δ*‖c‖^2 ≤ ∫ x, (polynomialEval (boundedDegreePolynomial c) x)^2
        ∂(μ : Measure (Space n)) := by
  obtain ⟨δ,hδ,hbound⟩ := exists_uniform_polynomialCoefficientEnergy_lower
    _ (degreeExponent_injective n d)
  refine ⟨δ,hδ,?_⟩
  intro μ hμ c
  simpa only [polynomialCoefficientEnergy_eq_integral_sq _ hμ,boundedDegreePolynomial] using
    hbound μ hμ c

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.boundedDegreePolynomial_representation
#print axioms KLS.DeterministicBridgeNext.isCompact_boundedDegree_normalizedPolynomialPairs
