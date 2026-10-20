import ActualPairAppellSplit
import ActualJointCumulantContraction
import SelectedRowsTriangleYoung

/-! Literal Appell remainder with arbitrary nonnegative subset-size
coefficients. This permits simultaneous retained size-two and size-three
rows without changing the underlying test or law. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def actualProfileProperRemainder (μ : Measure (Space n)) (f : Space n → ℝ)
    (rho : ℕ → ℕ → ℝ) (d : ℕ) : (Fin d → Fin n) → ℝ :=
  ∑ S : Finset (Fin d), if 2 ≤ S.card ∧ S.card ≤ d-1 then
    rho d S.card • actualSubsetAppellContraction μ f d S else 0

theorem actualProfileProperRemainder_split (μ : Measure (Space n))
    (f : Space n → ℝ) (rho : ℕ → ℕ → ℝ) (d : ℕ) :
    actualAppellProperRemainder μ f d = actualProfileProperRemainder μ f rho d +
      actualProfileProperRemainder μ f (fun d a => 1-rho d a) d := by
  classical
  unfold actualAppellProperRemainder actualProfileProperRemainder
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  split_ifs with hp
  · ext a
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  · simp

theorem actualProfileProperRemainder_pairing_split (μ : Measure (Space n))
    (f : Space n → ℝ) (rho : ℕ → ℕ → ℝ) (d : ℕ) :
    actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d =
      actualAppellCoefficient μ f d ⬝ᵥ actualProfileProperRemainder μ f rho d +
      actualAppellCoefficient μ f d ⬝ᵥ
        actualProfileProperRemainder μ f (fun d a => 1-rho d a) d := by
  rw [actualProfileProperRemainder_split μ f rho d,dotProduct_add]

theorem actual_profile_remainder_norm_le_canonical_sum
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (rho : ℕ → ℕ → ℝ) (d : ℕ)
    (hrho : ∀ a, 0 ≤ rho d a) :
    ‖(WithLp.toLp 2 (actualProfileProperRemainder μ f rho d) :
      EuclideanSpace ℝ (Fin d → Fin n))‖ ≤
      ∑ a ∈ Finset.Icc 2 (d-1), rho d a * (d.choose a : ℝ) *
        Real.sqrt (actualCanonicalContractionSquare μ f a (d-a)) := by
  classical
  let V := EuclideanSpace ℝ (Fin d → Fin n)
  have hcoeff (a : ℕ) : 0 ≤ rho d a := by
    exact hrho a
  have he : (WithLp.toLp 2 (actualProfileProperRemainder μ f rho d) : V) =
      ∑ S : Finset (Fin d), if 2 ≤ S.card ∧ S.card ≤ d-1 then
        rho d S.card •
          (WithLp.toLp 2 (actualSubsetAppellContraction μ f d S) : V) else 0 := by
    apply PiLp.ext
    intro γ
    change (actualProfileProperRemainder μ f rho d) γ = _
    unfold actualProfileProperRemainder
    simp only [Finset.sum_apply]
    have hp := map_sum (EuclideanSpace.proj γ)
      (fun S : Finset (Fin d) => if 2 ≤ S.card ∧ S.card ≤ d-1 then
        rho d S.card •
          (WithLp.toLp 2 (actualSubsetAppellContraction μ f d S) : V) else 0) Finset.univ
    change _ = ∑ S : Finset (Fin d), _ at hp
    apply Eq.trans _ hp.symm
    apply Finset.sum_congr rfl
    intro S hS
    split_ifs <;> rfl
  have hc (S : Finset (Fin d)) : Sᶜ.card = d-S.card := by
    have hh : S.card+Sᶜ.card = d := by simp
    omega
  have hsum : (∑ S : Finset (Fin d), if 2 ≤ S.card ∧ S.card ≤ d-1 then
      rho d S.card *
        Real.sqrt (actualCanonicalContractionSquare μ f S.card Sᶜ.card) else 0) =
      ∑ a ∈ Finset.Icc 2 (d-1), rho d a * (d.choose a : ℝ) *
        Real.sqrt (actualCanonicalContractionSquare μ f a (d-a)) := by
    simp_rw [hc]
    have hs := sum_subsets_card_weight d (fun a => if 2 ≤ a ∧ a ≤ d-1 then
      rho d a *
        Real.sqrt (actualCanonicalContractionSquare μ f a (d-a)) else 0)
    rw [hs]
    simp_rw [mul_ite,mul_zero]
    rw [←Finset.sum_filter]
    have hset : (Finset.range (d+1)).filter (fun a => 2 ≤ a ∧ a ≤ d-1) =
        Finset.Icc 2 (d-1) := by
      ext a
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
      omega
    rw [hset]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [he,←hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun S hS => ?_)
  split_ifs with hp
  · rw [norm_smul,Real.norm_of_nonneg (hcoeff _),
      actualSubsetAppellContraction_norm_eq_sqrt_canonical hLC hf S]
  · simp

theorem actual_profile_pairing_le_canonical_sum
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (rho : ℕ → ℕ → ℝ) (d : ℕ)
    (hrho : ∀ a, 0 ≤ rho d a) :
    actualAppellCoefficient μ f d ⬝ᵥ actualProfileProperRemainder μ f rho d ≤
      Real.sqrt (actualAppellEnergy μ f d) *
        (∑ a ∈ Finset.Icc 2 (d-1), rho d a * (d.choose a : ℝ) *
          Real.sqrt (actualCanonicalContractionSquare μ f a (d-a))) := by
  have hh := real_inner_le_norm
    (WithLp.toLp 2 (actualAppellCoefficient μ f d) : EuclideanSpace ℝ (Fin d → Fin n))
    (WithLp.toLp 2 (actualProfileProperRemainder μ f rho d) : EuclideanSpace ℝ (Fin d → Fin n))
  have hn : ‖(WithLp.toLp 2 (actualAppellCoefficient μ f d) :
      EuclideanSpace ℝ (Fin d → Fin n))‖ = Real.sqrt (actualAppellEnergy μ f d) := by
    have hs : ‖(WithLp.toLp 2 (actualAppellCoefficient μ f d) :
        EuclideanSpace ℝ (Fin d → Fin n))‖^2 = actualAppellEnergy μ f d :=
      EuclideanSpace.real_norm_sq_eq _
    rw [←hs,Real.sqrt_sq (norm_nonneg _)]
  rw [hn] at hh
  have hb := mul_le_mul_of_nonneg_left
    (actual_profile_remainder_norm_le_canonical_sum hLC hf rho d hrho)
    (Real.sqrt_nonneg (actualAppellEnergy μ f d))
  have hh' : actualAppellCoefficient μ f d ⬝ᵥ actualProfileProperRemainder μ f rho d ≤
      Real.sqrt (actualAppellEnergy μ f d) *
        ‖(WithLp.toLp 2 (actualProfileProperRemainder μ f rho d) :
          EuclideanSpace ℝ (Fin d → Fin n))‖ := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct_comm] using hh
  exact hh'.trans hb

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_profile_pairing_le_canonical_sum
