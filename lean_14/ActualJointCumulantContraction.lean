import ActualAppellTerminalSplit

/-! Joint, dimension-free cumulant contraction from a genuine finite
weighted Appell bound on all L² tests. This retains the square sum over
cumulant degrees before taking any operator norm. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped ContDiff BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def actualCanonicalContractionSquare (μ : Measure (Space n)) (f : Space n → ℝ)
    (a b : ℕ) : ℝ :=
  ∑ α : Fin a → Fin n, ∑ β : Fin b → Fin n,
    (actualCanonicalAppellContraction μ f a b α β)^2

theorem actualCanonicalContractionSquare_nonneg (μ : Measure (Space n))
    (f : Space n → ℝ) (a b : ℕ) : 0 ≤ actualCanonicalContractionSquare μ f a b := by
  unfold actualCanonicalContractionSquare
  positivity

theorem actual_joint_canonical_contraction_square_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (f : Space n → ℝ) (A : Finset ℕ) (w : ℕ → ℝ) {C : ℝ}
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      (∑ a ∈ A, w a*actualAppellEnergy μ g a) ≤ C*(∫ x, (g x)^2 ∂μ))
    (b : ℕ) :
    (∑ a ∈ A, w a*actualCanonicalContractionSquare μ f a b) ≤
      C*actualAppellEnergy μ f (b+1) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let v (β : Fin b → Fin n) : Space n :=
    WithLp.toLp 2 (fun i => actualAppellCoefficient μ f (b+1) (Fin.cons i β))
  have hp (β : Fin b → Fin n) :
      (∑ a ∈ A, w a*(∑ α : Fin a → Fin n,
        (actualCanonicalAppellContraction μ f a b α β)^2)) ≤
      C*(∑ i : Fin n, (actualAppellCoefficient μ f (b+1) (Fin.cons i β))^2) := by
    have hv : (∫ x, (inner ℝ x (v β))^2 ∂μ) =
        ∑ i : Fin n, (actualAppellCoefficient μ f (b+1) (Fin.cons i β))^2 := by
      rw [hμ.isotropic.integral_inner_sq, EuclideanSpace.real_norm_sq_eq]
    have hh := hprevious (fun x => inner ℝ x (v β)) (hμ.isotropic.memLp_inner (v β))
    rw [hv] at hh
    simpa only [actualAppellEnergy,
      actualCanonicalAppellContraction_eq_linear_coefficient hμ.logConcave, v] using hh
  calc
    _ = ∑ β : Fin b → Fin n, ∑ a ∈ A, w a*(∑ α : Fin a → Fin n,
        (actualCanonicalAppellContraction μ f a b α β)^2) := by
      unfold actualCanonicalContractionSquare
      have hs (a : ℕ) : w a*(∑ α : Fin a → Fin n, ∑ β : Fin b → Fin n,
          (actualCanonicalAppellContraction μ f a b α β)^2) =
          ∑ β : Fin b → Fin n, w a*(∑ α : Fin a → Fin n,
            (actualCanonicalAppellContraction μ f a b α β)^2) := by
        rw [Finset.sum_comm, Finset.mul_sum]
      simp_rw [hs]
      rw [Finset.sum_comm]
    _ ≤ ∑ β : Fin b → Fin n, C*(∑ i : Fin n,
        (actualAppellCoefficient μ f (b+1) (Fin.cons i β))^2) := Finset.sum_le_sum (fun β hβ => hp β)
    _ = C*actualAppellEnergy μ f (b+1) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      simpa only [dotProduct,pow_two] using actualAppell_next_slices_square μ f b

theorem actualSubsetAppellContraction_square_eq_canonical
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {d : ℕ} (S : Finset (Fin d)) :
    (∑ γ : Fin d → Fin n, (actualSubsetAppellContraction μ f d S γ)^2) =
      actualCanonicalContractionSquare μ f S.card Sᶜ.card := by
  rw [← (subsetCoordinateEquiv (n := n) S).sum_comp]
  simp only [Fintype.sum_prod_type,actualSubsetAppellContraction_reindex hLC hf]
  rfl

theorem actualSubsetAppellContraction_norm_eq_sqrt_canonical
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {d : ℕ} (S : Finset (Fin d)) :
    ‖(WithLp.toLp 2 (actualSubsetAppellContraction μ f d S) :
      EuclideanSpace ℝ (Fin d → Fin n))‖ =
      Real.sqrt (actualCanonicalContractionSquare μ f S.card Sᶜ.card) := by
  have hsq := EuclideanSpace.real_norm_sq_eq
    (WithLp.toLp 2 (actualSubsetAppellContraction μ f d S) : EuclideanSpace ℝ (Fin d → Fin n))
  rw [actualSubsetAppellContraction_square_eq_canonical hLC hf] at hsq
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

theorem actual_proper_remainder_norm_le_canonical_sum
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (d : ℕ) :
    ‖(WithLp.toLp 2 (actualAppellProperRemainder μ f d) :
      EuclideanSpace ℝ (Fin d → Fin n))‖ ≤
      ∑ a ∈ Finset.Icc 2 (d-1), (d.choose a : ℝ)*
        Real.sqrt (actualCanonicalContractionSquare μ f a (d-a)) := by
  classical
  let V := EuclideanSpace ℝ (Fin d → Fin n)
  have he : (WithLp.toLp 2 (actualAppellProperRemainder μ f d) : V) =
      ∑ S : Finset (Fin d), if 2 ≤ S.card ∧ S.card ≤ d-1 then
        (WithLp.toLp 2 (actualSubsetAppellContraction μ f d S) : V) else 0 := by
    apply PiLp.ext
    intro γ
    change (actualAppellProperRemainder μ f d) γ = _
    unfold actualAppellProperRemainder
    simp only [Finset.sum_apply]
    have hp := map_sum (EuclideanSpace.proj γ)
      (fun S : Finset (Fin d) => if 2 ≤ S.card ∧ S.card ≤ d-1 then
        (WithLp.toLp 2 (actualSubsetAppellContraction μ f d S) : V) else 0) Finset.univ
    change _ = ∑ S : Finset (Fin d), _ at hp
    apply Eq.trans _ hp.symm
    apply Finset.sum_congr rfl
    intro S hS
    split_ifs <;> rfl
  have hc (S : Finset (Fin d)) : Sᶜ.card=d-S.card := by
    have hh : S.card+Sᶜ.card=d := by simp
    omega
  have hsum : (∑ S : Finset (Fin d), if 2 ≤ S.card ∧ S.card ≤ d-1 then
      Real.sqrt (actualCanonicalContractionSquare μ f S.card Sᶜ.card) else 0) =
      ∑ a ∈ Finset.Icc 2 (d-1), (d.choose a : ℝ)*
        Real.sqrt (actualCanonicalContractionSquare μ f a (d-a)) := by
    simp_rw [hc]
    have hs := sum_subsets_card_weight d (fun a => if 2 ≤ a ∧ a ≤ d-1 then
      Real.sqrt (actualCanonicalContractionSquare μ f a (d-a)) else 0)
    rw [hs]
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [he, ← hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun S hS => ?_)
  split_ifs with hp
  · exact (actualSubsetAppellContraction_norm_eq_sqrt_canonical hLC hf S).le
  · simp

theorem actual_proper_pairing_le_canonical_sum
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (d : ℕ) :
    actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d ≤
      Real.sqrt (actualAppellEnergy μ f d)*
        (∑ a ∈ Finset.Icc 2 (d-1), (d.choose a : ℝ)*
          Real.sqrt (actualCanonicalContractionSquare μ f a (d-a))) := by
  have hh := real_inner_le_norm
    (WithLp.toLp 2 (actualAppellCoefficient μ f d) : EuclideanSpace ℝ (Fin d → Fin n))
    (WithLp.toLp 2 (actualAppellProperRemainder μ f d) : EuclideanSpace ℝ (Fin d → Fin n))
  have hn : ‖(WithLp.toLp 2 (actualAppellCoefficient μ f d) :
      EuclideanSpace ℝ (Fin d → Fin n))‖ = Real.sqrt (actualAppellEnergy μ f d) := by
    have hs : ‖(WithLp.toLp 2 (actualAppellCoefficient μ f d) :
        EuclideanSpace ℝ (Fin d → Fin n))‖^2 = actualAppellEnergy μ f d :=
      EuclideanSpace.real_norm_sq_eq _
    rw [← hs, Real.sqrt_sq (norm_nonneg _)]
  rw [hn] at hh
  have hb := mul_le_mul_of_nonneg_left
    (actual_proper_remainder_norm_le_canonical_sum hLC hf d)
      (Real.sqrt_nonneg (actualAppellEnergy μ f d))
  have hh' : actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d ≤
      Real.sqrt (actualAppellEnergy μ f d)*
        ‖(WithLp.toLp 2 (actualAppellProperRemainder μ f d) : EuclideanSpace ℝ (Fin d → Fin n))‖ := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct_comm] using hh
  exact hh'.trans hb

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_joint_canonical_contraction_square_le
#print axioms KLS.DeterministicBridgeNext.actual_proper_pairing_le_canonical_sum
