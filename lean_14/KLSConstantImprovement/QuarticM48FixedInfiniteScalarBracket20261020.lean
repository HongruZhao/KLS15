import KLSConstantImprovement.QuarticM48AffinePayment20261020
import KLSConstantImprovement.QuarticM48ScalarLowerPath20261020
import KLSConstantImprovement.BoundedProperInfiniteScalarMinimum

/-! The full infinite scalar value for the one frozenM48 profile.
The feasible endpoint supremum lies in[13.810854,13.810855]. These are
scalar relaxation endpoints, not lower bounds for an admissible-law KLS
constant and not an optimum over generator profiles. The initial massp
is multiplied exactly once in every infinite-budget comparison.
Root alone compiles this draft. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.QuarticM48FixedInfiniteScalarBracket20261020
open KLSConstantImprovement.CompatibleRatioPathCompact
open KLSConstantImprovement.ProperInfiniteRatioPathSelection
open KLSConstantImprovement.ProperInfiniteRatioPathMinimum
open KLSConstantImprovement.SubexponentialTerminalSupremum
open KLSConstantImprovement.RatioPathOrbitRealization
open KLSConstantImprovement.BoundedProperInfiniteScalarMinimum
open KLSConstantImprovement.QuarticM48Profile20261020Data
open KLSConstantImprovement.QuarticM48TrueCapBellman20261020Data
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

/-- The actual normalized scalar budget, including Z1=p. -/
def infiniteBudget (p : ℝ) : ℝ := p*infiniteValue A p w

def feasibleRatios : Set ℝ :=
  {p | 1 ≤ p ∧ p ≤ ratioUpper ∧ infiniteBudget p ≤ C}

/-- Supremum only over the frozenM48 profile, inside its prescribed ratio cap. -/
def fixedScalarEndpoint : ℝ := 1+K*sSup feasibleRatios

theorem full_floors : FullFloors w := by
  intro ρ hρ
  refine ⟨tau, by norm_num [tau], ?_⟩
  intro i
  have hf : tau ≤ w i := t_floor (i+2) (by omega)
  have hw : 0 ≤ w i := (t_positive (i+2) (by omega)).le
  exact hf.trans (le_mul_of_one_le_right hw (one_le_pow₀ hρ.le))

theorem lower_interval :
    1 ≤ QuarticM48ScalarLowerPath20261020.p ∧
      QuarticM48ScalarLowerPath20261020.p ≤ ratioUpper := by
  norm_num [QuarticM48ScalarLowerPath20261020.p,ratioUpper,K]

theorem lower_infinite_budget :
    infiniteBudget QuarticM48ScalarLowerPath20261020.p ≤ C := by
  have hp0 : 0 < QuarticM48ScalarLowerPath20261020.p := by
    norm_num [QuarticM48ScalarLowerPath20261020.p]
  have hr : QuarticM48ScalarLowerPath20261020.r ∈
      ratioPathSet A QuarticM48ScalarLowerPath20261020.p := by
    simpa only [A,QuarticM48ScalarLowerPath20261020.A,
      QuarticM48ScalarLowerPath20261020.K] using
      QuarticM48ScalarLowerPath20261020.ratio_path_mem
  have hproper : Proper QuarticM48ScalarLowerPath20261020.r :=
    product_envelope_of_eventually_one hr
      ⟨47,QuarticM48ScalarLowerPath20261020.eventually_one⟩
  have hbudget (N : ℕ) :
      prefixSpend w QuarticM48ScalarLowerPath20261020.r N ≤
        C/QuarticM48ScalarLowerPath20261020.p := by
    apply (le_div_iff₀ hp0).mpr
    have hh := QuarticM48ScalarLowerPath20261020.normalized_prefix_budget N
    simpa only [prefixSpend,w,QuarticM48ScalarLowerPath20261020.w,
      QuarticM48ScalarLowerPath20261020.C,mul_comm] using hh
  have hh := infiniteValue_le_of_proper_budget hr (floors_nonempty full_floors)
    hproper hbudget
  simpa only [infiniteBudget,mul_comm] using (le_div_iff₀ hp0).mp hh

/-- Every bounded proper scalar optimizer pays the fixed finite affine line. -/
theorem affine_lower_infinite (p : ℝ) (hp : 1 ≤ p) (hpR : p ≤ ratioUpper) :
    p*(line 0).positive p ≤ infiniteBudget p := by
  obtain ⟨Z,c,hZ0,hZ1,hZ,hc,hrec,hcap,hupper,hbudget,henv⟩ :=
    exists_exact_bounded_scalar_optimizer
      (A:=A) (p:=p) (R:=ratioUpper) (w:=w)
      (by norm_num [A,K]) hp hpR full_floors
  have hzero (i : ℕ) (hi : Z i=0) : Z (i+1)=0 := by
    exact False.elim ((ne_of_gt (hZ i)) hi)
  have hb : ∀ N,WeightedOrbitBellmanTail.spend w c N ≤ infiniteBudget p := by
    intro N
    simpa only [infiniteBudget] using hbudget N
  have hh := QuarticM48AffinePayment20261020.affine_payment Z c (infiniteBudget p)
    (fun i=>(hZ i).le) hc hZ0 hzero (fun i _ _=>(hrec i).le)
    hcap hupper hb henv
  simpa only [hZ1] using hh

theorem upper_infinite_budget_strict : C < infiniteBudget q := by
  exact strict_budget.trans_le (affine_lower_infinite q q_interval.1 q_interval.2)

/-- No scalar budget-feasible starting ratio lies at or above q. -/
theorem infeasible_above_upper (p : ℝ) (hpR : p ≤ ratioUpper) (hqp : q ≤ p) :
    C < infiniteBudget p := by
  have hp : 1 ≤ p := q_interval.1.trans hqp
  have hm := PositiveFiniteHeadBellman.Affine.product_mono (line 0)
    (line_slope_nonneg 0 (by omega)) q_positive.le hqp
  exact strict_budget.trans_le (hm.trans (affine_lower_infinite p hp hpR))

theorem lower_feasible : QuarticM48ScalarLowerPath20261020.p ∈ feasibleRatios :=
  ⟨lower_interval.1,lower_interval.2,lower_infinite_budget⟩

theorem feasible_below_upper (p : ℝ) (hp : p ∈ feasibleRatios) : p < q := by
  rcases hp with ⟨hp1,hpR,hbudget⟩
  by_contra hfail
  have hh := infeasible_above_upper p hpR (le_of_not_gt hfail)
  linarith

theorem feasible_nonempty : feasibleRatios.Nonempty :=
  ⟨QuarticM48ScalarLowerPath20261020.p,lower_feasible⟩

theorem feasible_bounded : BddAbove feasibleRatios := by
  refine ⟨q,?_⟩
  intro p hp
  exact (feasible_below_upper p hp).le

theorem fixed_endpoint_bounds :
    (6905427/500000 : ℝ) ≤ fixedScalarEndpoint ∧
      fixedScalarEndpoint ≤ (2762171/200000 : ℝ) := by
  have hlow : QuarticM48ScalarLowerPath20261020.p ≤ sSup feasibleRatios :=
    le_csSup feasible_bounded lower_feasible
  have hhigh : sSup feasibleRatios ≤ q := by
    apply csSup_le feasible_nonempty
    intro p hp
    exact (feasible_below_upper p hp).le
  have hk : 0 ≤ K := by norm_num [K]
  constructor
  · calc
      _ = 1+K*QuarticM48ScalarLowerPath20261020.p := by
        simpa only [QuarticM48ScalarLowerPath20261020.K] using
          QuarticM48ScalarLowerPath20261020.endpoint_exact.symm
      _ ≤ 1+K*sSup feasibleRatios :=
        add_le_add (le_refl (1 : ℝ)) (mul_le_mul_of_nonneg_left hlow hk)
      _ = fixedScalarEndpoint := rfl
  · calc
      fixedScalarEndpoint = 1+K*sSup feasibleRatios := rfl
      _ ≤ 1+K*q := add_le_add (le_refl (1 : ℝ)) (mul_le_mul_of_nonneg_left hhigh hk)
      _ = _ := QuarticM48TrueCapBellman20261020Data.exact_endpoint

/-- Full fixed-profile infinite-value bracket, with both actual budget signs. -/
theorem fixed_infinite_value_bracket :
    infiniteBudget QuarticM48ScalarLowerPath20261020.p ≤ C ∧
      C < infiniteBudget q ∧
      (6905427/500000 : ℝ) ≤ fixedScalarEndpoint ∧
      fixedScalarEndpoint ≤ (2762171/200000 : ℝ) ∧
      (2762171/200000-6905427/500000 : ℝ)=1/1000000 := by
  exact ⟨lower_infinite_budget,upper_infinite_budget_strict,
    fixed_endpoint_bounds.1,fixed_endpoint_bounds.2,by norm_num⟩

end KLSConstantImprovement.QuarticM48FixedInfiniteScalarBracket20261020
#print axioms KLSConstantImprovement.QuarticM48FixedInfiniteScalarBracket20261020.lower_infinite_budget
#print axioms KLSConstantImprovement.QuarticM48FixedInfiniteScalarBracket20261020.affine_lower_infinite
#print axioms KLSConstantImprovement.QuarticM48FixedInfiniteScalarBracket20261020.upper_infinite_budget_strict
#print axioms KLSConstantImprovement.QuarticM48FixedInfiniteScalarBracket20261020.fixed_infinite_value_bracket
