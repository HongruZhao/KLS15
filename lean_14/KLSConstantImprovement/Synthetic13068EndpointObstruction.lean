import KLSConstantImprovement.SyntheticThirteen068FiniteOrbit20261020
import KLSConstantImprovement.InfiniteValueMonotoneThreshold

/-! A pure endpoint obstruction from the linear synthetic finite budget.
This applies equally to a single current generator certificate or to a
nonnegative mixture after its synthetic-budget bound is proved. It is
not a lower bound for the universal KLS constant.
This isolated source draft has not been compiled by its author. -/

noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.Synthetic13068EndpointObstruction
open KLSConstantImprovement.ProperInfiniteRatioPathSelection
open KLSConstantImprovement.SubexponentialTerminalSupremum
open KLSConstantImprovement.InfiniteValueMonotoneThreshold

theorem endpoint_gt_thirteen068
    (K C : ℝ) (t : ℕ → ℝ) (hKlo : (14571 / 1250 : ℝ) ≤ K)
    (ht : ∀ d, 2 ≤ d → 0 ≤ t d)
    (hF : Nonempty (Floor (fun i => t (i + 2))))
    (hbridge :
      (∑ d ∈ Finset.Icc 2 57, t d * SyntheticThirteen068FiniteOrbit20261020.z d / K ^ d) ≤ C)
    (p : ℝ) (hp : 1 ≤ p)
    (hstrict : C < p * infiniteValue (2 / K ^ 2) p (fun i => t (i + 2))) :
    (3267 / 250 : ℝ) < 1 + K * p := by
  have hK : 0 < K := by linarith
  by_contra hfail
  have hprod : K * p ≤ (3017 / 250 : ℝ) := by linarith
  have hKx : K ≤ SyntheticThirteen068FiniteOrbit20261020.x := by
    norm_num only [SyntheticThirteen068FiniteOrbit20261020.x]
    nlinarith
  have hpHigh : p ≤ SyntheticThirteen068FiniteOrbit20261020.x / K :=
    (le_div_iff₀ hK).mpr
      (by simpa only [SyntheticThirteen068FiniteOrbit20261020.x, mul_comm] using hprod)
  let Z := SyntheticThirteen068FiniteOrbit20261020.Z K
  let c := SyntheticThirteen068FiniteOrbit20261020.c K
  let w : ℕ → ℝ := fun i => t (i + 2)
  obtain ⟨hZ0, hZ1, hZpos, hc, hrec, hcap, hupper, henv⟩ :=
    SyntheticThirteen068FiniteOrbit20261020.uniform_scalar_orbit K hKlo hKx
  have hbudget (j : ℕ) : WeightedOrbitBellmanTail.spend w c j ≤ C :=
    SyntheticThirteen068FiniteOrbit20261020.spend_le_budget K C hK t ht hbridge j
  have hZ1lower : p ≤ Z 1 := by
    change p ≤ SyntheticThirteen068FiniteOrbit20261020.Z K 1
    rw [hZ1]
    exact hpHigh
  have hh := actual_initial_lt_of_strict_budget Z c w (by positivity : 0 ≤ 2 / K ^ 2)
    hF hp (fun i => (hZpos i).le) hc hZ0 (fun i _ _ => hrec i)
    hcap hbudget henv hstrict
  exact (not_lt_of_ge hZ1lower) hh

end KLSConstantImprovement.Synthetic13068EndpointObstruction

#print axioms KLSConstantImprovement.Synthetic13068EndpointObstruction.endpoint_gt_thirteen068
