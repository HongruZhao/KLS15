import ActualPairAppellSplit
import ActualJointCumulantContraction
import ThetaWeightedTriangleYoung

/-! A literal retained proper remainder: only the size-two subset
coefficient is changed.  Its canonical contraction bound is proved before
any shared joint budget or creation estimate is used. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def actualThetaProperRemainder (μ : Measure (Space n)) (f : Space n → ℝ)
    (theta : ℕ → ℝ) (d : ℕ) : (Fin d → Fin n) → ℝ :=
  ∑ S : Finset (Fin d), if 2 ≤ S.card ∧ S.card ≤ d-1 then
    thetaTriangleCoefficient theta d S.card • actualSubsetAppellContraction μ f d S else 0

theorem actualThetaProperRemainder_add_pair (μ : Measure (Space n))
    (f : Space n → ℝ) (theta : ℕ → ℝ) (d : ℕ) (hd : 3 ≤ d) :
    actualAppellProperRemainder μ f d = actualThetaProperRemainder μ f theta d +
      theta d • actualAppellPairContractionSum μ f d := by
  classical
  unfold actualAppellProperRemainder actualThetaProperRemainder actualAppellPairContractionSum
  rw [Finset.smul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases h2 : S.card = 2
  · have hp : 2 ≤ S.card ∧ S.card ≤ d-1 := by omega
    rw [ite_eq_left hp,ite_eq_left h2,ite_eq_left hp]
    unfold thetaTriangleCoefficient
    rw [ite_eq_left h2]
    ext a
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  · rw [ite_eq_right h2,smul_zero,add_zero]
    by_cases hp : 2 ≤ S.card ∧ S.card ≤ d-1
    · rw [ite_eq_left hp,ite_eq_left hp]
      simp [thetaTriangleCoefficient,h2]
    · rw [ite_eq_right hp,ite_eq_right hp]

theorem actualThetaProperRemainder_pairing_split (μ : Measure (Space n))
    (f : Space n → ℝ) (theta : ℕ → ℝ) (d : ℕ) (hd : 3 ≤ d) :
    actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d =
      actualAppellCoefficient μ f d ⬝ᵥ actualThetaProperRemainder μ f theta d +
        theta d * (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d) := by
  rw [actualThetaProperRemainder_add_pair μ f theta d hd,dotProduct_add]
  simp only [dotProduct,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem actual_theta_remainder_norm_le_canonical_sum
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (theta : ℕ → ℝ) (d : ℕ)
    (htheta : theta d ≤ 1) :
    ‖(WithLp.toLp 2 (actualThetaProperRemainder μ f theta d) :
      EuclideanSpace ℝ (Fin d → Fin n))‖ ≤
      ∑ a ∈ Finset.Icc 2 (d-1), thetaTriangleCoefficient theta d a * (d.choose a : ℝ) *
        Real.sqrt (actualCanonicalContractionSquare μ f a (d-a)) := by
  classical
  let V := EuclideanSpace ℝ (Fin d → Fin n)
  have hcoeff (a : ℕ) : 0 ≤ thetaTriangleCoefficient theta d a := by
    unfold thetaTriangleCoefficient
    split_ifs
    · linarith
    · norm_num
  have he : (WithLp.toLp 2 (actualThetaProperRemainder μ f theta d) : V) =
      ∑ S : Finset (Fin d), if 2 ≤ S.card ∧ S.card ≤ d-1 then
        thetaTriangleCoefficient theta d S.card •
          (WithLp.toLp 2 (actualSubsetAppellContraction μ f d S) : V) else 0 := by
    apply PiLp.ext
    intro γ
    change (actualThetaProperRemainder μ f theta d) γ = _
    unfold actualThetaProperRemainder
    simp only [Finset.sum_apply]
    have hp := map_sum (EuclideanSpace.proj γ)
      (fun S : Finset (Fin d) => if 2 ≤ S.card ∧ S.card ≤ d-1 then
        thetaTriangleCoefficient theta d S.card •
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
      thetaTriangleCoefficient theta d S.card *
        Real.sqrt (actualCanonicalContractionSquare μ f S.card Sᶜ.card) else 0) =
      ∑ a ∈ Finset.Icc 2 (d-1), thetaTriangleCoefficient theta d a * (d.choose a : ℝ) *
        Real.sqrt (actualCanonicalContractionSquare μ f a (d-a)) := by
    simp_rw [hc]
    have hs := sum_subsets_card_weight d (fun a => if 2 ≤ a ∧ a ≤ d-1 then
      thetaTriangleCoefficient theta d a *
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

theorem actual_theta_pairing_le_canonical_sum
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (theta : ℕ → ℝ) (d : ℕ)
    (htheta : theta d ≤ 1) :
    actualAppellCoefficient μ f d ⬝ᵥ actualThetaProperRemainder μ f theta d ≤
      Real.sqrt (actualAppellEnergy μ f d) *
        (∑ a ∈ Finset.Icc 2 (d-1), thetaTriangleCoefficient theta d a * (d.choose a : ℝ) *
          Real.sqrt (actualCanonicalContractionSquare μ f a (d-a))) := by
  have hh := real_inner_le_norm
    (WithLp.toLp 2 (actualAppellCoefficient μ f d) : EuclideanSpace ℝ (Fin d → Fin n))
    (WithLp.toLp 2 (actualThetaProperRemainder μ f theta d) : EuclideanSpace ℝ (Fin d → Fin n))
  have hn : ‖(WithLp.toLp 2 (actualAppellCoefficient μ f d) :
      EuclideanSpace ℝ (Fin d → Fin n))‖ = Real.sqrt (actualAppellEnergy μ f d) := by
    have hs : ‖(WithLp.toLp 2 (actualAppellCoefficient μ f d) :
        EuclideanSpace ℝ (Fin d → Fin n))‖^2 = actualAppellEnergy μ f d :=
      EuclideanSpace.real_norm_sq_eq _
    rw [←hs,Real.sqrt_sq (norm_nonneg _)]
  rw [hn] at hh
  have hb := mul_le_mul_of_nonneg_left
    (actual_theta_remainder_norm_le_canonical_sum hLC hf theta d htheta)
    (Real.sqrt_nonneg (actualAppellEnergy μ f d))
  have hh' : actualAppellCoefficient μ f d ⬝ᵥ actualThetaProperRemainder μ f theta d ≤
      Real.sqrt (actualAppellEnergy μ f d) *
        ‖(WithLp.toLp 2 (actualThetaProperRemainder μ f theta d) :
          EuclideanSpace ℝ (Fin d → Fin n))‖ := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct_comm] using hh
  exact hh'.trans hb

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualThetaProperRemainder_pairing_split
#print axioms KLS.DeterministicBridgeNext.actual_theta_pairing_le_canonical_sum
