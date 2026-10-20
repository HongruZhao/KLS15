import KLSConstantImprovement.ActualProperInfiniteValuePayment

/-! A prescribed upper ratio R adds no loss to the proper scalar minimum
when the initial ratio p already satisfies p ≤ R: the selected minimizing
path decreases and therefore remains below p.  This explains why the true
infinite scalar value is independent of the earlier operator bootstrap.
No admissible law realizing the scalar optimizer is asserted.

This isolated draft has not been compiled by its author. -/

noncomputable section
namespace KLSConstantImprovement.BoundedProperInfiniteScalarMinimum
open KLSConstantImprovement.CompatibleRatioPathCompact
open KLSConstantImprovement.ProperInfiniteRatioPathSelection
open KLSConstantImprovement.ProperInfiniteRatioPathMinimum
open KLSConstantImprovement.ActualProperInfiniteValuePayment
open KLSConstantImprovement.RatioPathOrbitRealization
open KLSConstantImprovement.WeightedOrbitBellmanTail

theorem orbit_upper {A p R : ℝ} {r : ℕ → ℝ}
    (hr : r ∈ ratioPathSet A p) (hpR : p ≤ R) (i : ℕ) :
    orbitZ r p (i + 1) ≤ R * orbitZ r p i := by
  calc
    orbitZ r p (i + 1) = orbitZ r p i * r i := orbitZ_succ_mul hr i
    _ ≤ orbitZ r p i * R :=
      mul_le_mul_of_nonneg_left ((upper hr i).trans hpR) (orbitZ_pos hr i).le
    _ = R * orbitZ r p i := mul_comm _ _

/-- The scalar minimizing witness also satisfies the original upper-ratio
constraint whenever its initial ratio belongs to that interval. -/
theorem exists_exact_bounded_scalar_optimizer {A p R : ℝ} {w : ℕ → ℝ}
    (hA : 0 < A) (hp : 1 ≤ p) (hpR : p ≤ R) (hw : FullFloors w) :
    ∃ Z c : ℕ → ℝ, Z 0 = 1 ∧ Z 1 = p ∧
      (∀ i : ℕ, 0 < Z i) ∧ (∀ i : ℕ, 0 ≤ c i) ∧
      (∀ i : ℕ, Z (i + 1) ^ 2 / Z i - c i = Z (i + 2)) ∧
      (∀ i : ℕ, c i ≤ A * Z i) ∧
      (∀ i : ℕ, Z (i + 1) ≤ R * Z i) ∧
      (∀ N : ℕ, spend w c N ≤ p * infiniteValue A p w) ∧
      (∀ q : ℝ, 1 < q → ∃ M : ℝ, ∀ i : ℕ, Z i ≤ M * q ^ i) := by
  obtain ⟨r, hr, hproper, hbudget, hcost, hminimal⟩ := attained_scalar_minimum hA hp hw
  refine ⟨orbitZ r p, orbitC r p, rfl, orbitZ_one r p,
    orbitZ_pos hr, orbitC_nonneg hr, orbit_recurrence hr, orbit_cap hr,
    orbit_upper hr hpR, ?_, ?_⟩
  · intro N
    rw [spend_eq]
    exact mul_le_mul_of_nonneg_left (hbudget N) (by linarith : 0 ≤ p)
  · exact orbitZ_envelope r hp hproper

end KLSConstantImprovement.BoundedProperInfiniteScalarMinimum

#print axioms KLSConstantImprovement.BoundedProperInfiniteScalarMinimum.orbit_upper
#print axioms KLSConstantImprovement.BoundedProperInfiniteScalarMinimum.exists_exact_bounded_scalar_optimizer
