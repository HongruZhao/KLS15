import KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020Data
import KLSConstantImprovement.QuarticM96MixScalarLowerPath20261020
import KLSConstantImprovement.BoundedProperInfiniteScalarMinimum

/-! The full infinite scalar value for the one frozenMIX96 profile.
The feasible endpoint supremum lies in[13.810832,13.810833]. These are
scalar relaxation endpoints, not lower bounds for an admissible-law KLS
constant and not an optimum over generator profiles. The initial massp
is multiplied exactly once in every infinite-budget comparison.
Root alone compiles this draft. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.QuarticM96MixFixedInfiniteScalarBracket20261020
open KLSConstantImprovement.CompatibleRatioPathCompact
open KLSConstantImprovement.ProperInfiniteRatioPathSelection
open KLSConstantImprovement.ProperInfiniteRatioPathMinimum
open KLSConstantImprovement.SubexponentialTerminalSupremum
open KLSConstantImprovement.RatioPathOrbitRealization
open KLSConstantImprovement.BoundedProperInfiniteScalarMinimum
open KLSConstantImprovement.AcceptedMix96Data
open KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020Data
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

open KLSConstantImprovement.PositiveFiniteHeadBellman
open KLSConstantImprovement.ExactQuadraticCapBellmanCertificates
open KLSConstantImprovement.WeightedOrbitBellmanTail

def qUpper : ℝ := 1281083300000000/1216280801173157

theorem qUpper_positive : 0<qUpper := by norm_num [qUpper]
theorem qUpper_interval : 1 ≤ qUpper ∧ qUpper ≤ ratioUpper := by
  norm_num [qUpper,ratioUpper,K]
theorem strict_budget_upper : C<qUpper*(line 0).positive qUpper := by
  norm_num [C,qUpper,line,Affine.positive,Affine.eval]
theorem upper_endpoint_exact : 1+K*qUpper=(13810833/1000000 : ℝ) := by
  norm_num [K,qUpper]

theorem affine_payment (Z c : ℕ → ℝ) (B : ℝ)
    (hZ : ∀ i,0 ≤ Z i) (hc : ∀ i,0 ≤ c i) (hZ0 : Z 0=1)
    (hzero : ∀ i,Z i=0 → Z (i+1)=0)
    (hrec : ∀ i,0 < Z i → 0 < Z (i+1) →
      Z (i+1)^2/Z i-c i ≤ Z (i+2))
    (hcap : ∀ i,c i ≤ A*Z i)
    (hupper : ∀ i,Z (i+1) ≤ ratioUpper*Z i)
    (hbudget : ∀ N,spend w c N ≤ B)
    (henv : ∀ ρ : ℝ,1 < ρ → ∃ M : ℝ,∀ i,Z i ≤ M*ρ^i) :
    Z 1*(line 0).positive (Z 1) ≤ B := by
  let r : ℕ → ℝ := fun i=>Z (i+1)/Z i
  have hr (i : ℕ) : 0 ≤ r i := div_nonneg (hZ _) (hZ _)
  have hrU (i : ℕ) : r i ≤ ratioUpper := by
    by_cases hz : Z i=0
    · simp only [r,hz,div_zero]
      exact ratioUpper_positive.le
    · have hp : 0 < Z i := lt_of_le_of_ne (hZ _) (Ne.symm hz)
      exact (div_le_iff₀ hp).mpr (hupper i)
  have hstage (i : ℕ) (hi : i < 95) :
      Z (i+1)*(line i).positive (r i) ≤
        w i*c i+Z (i+2)*(line (i+1)).positive (r (i+1)) := by
    by_cases hr1 : r i ≤ 1
    · rw [Affine.positive_zero (line i) (line_slope_nonneg i (by omega))
        (line_at_one i (by omega)) hr1,mul_zero]
      exact add_nonneg (mul_nonneg (stage_certificate i hi).weight_nonneg (hc i))
        (mul_nonneg (hZ _) (Affine.positive_nonneg _ _))
    have hr1' : 1 ≤ r i := (lt_of_not_ge hr1).le
    have hZi : 0 < Z i := by
      by_contra hn
      have hz : Z i=0 := le_antisymm (le_of_not_gt hn) (hZ _)
      have he : r i=0 := by simp [r,hz]
      linarith
    have hz : 0 < Z (i+1) := by
      have hp : 0 < r i := by linarith
      exact (div_pos_iff_of_pos_right hZi).mp hp
    let d : ℝ := c i/Z (i+1)
    have hd : 0 ≤ d := div_nonneg (hc _) hz.le
    have hdrop : r i-r (i+1) ≤ d := by
      have hh := div_le_div_of_nonneg_right (hrec i hZi hz) hz.le
      have he : (Z (i+1)^2/Z i-c i)/Z (i+1)=r i-d := by
        dsimp only [r,d]
        field_simp [ne_of_gt hz,ne_of_gt hZi]
      rw [he] at hh
      change r i-d ≤ r (i+1) at hh
      linarith
    have hdcap : d ≤ A/r i := by
      have hh := div_le_div_of_nonneg_right (hcap i) hz.le
      convert hh using 1 <;> dsimp only [r,d] <;>
        field_simp [ne_of_gt hz,ne_of_gt hZi] <;> ring
    have hh := transition_payment_of_exact_cap (stage_certificate i hi)
      A_nonneg (hZ (i+1)) hr1' (hr (i+1)) hd
      (hrU i) hdrop hdcap
    have hcd : Z (i+1)*d=c i := by
      dsimp only [d]
      field_simp
    have hzs : Z (i+1)*r (i+1)=Z (i+2) := by
      dsimp only [r]
      rw [show i+1+1=i+2 by omega]
      field_simp
    rwa [hcd,hzs] at hh
  have hh := finite_head_payment 95 w c (fun i=>Z (i+1)) r line
    (by
      intro i hi
      simpa only [Nat.add_assoc,Nat.reduceAdd] using hstage i hi)
  have ht : ∀ i,95 ≤ i → w i=tTail := by
    intro i hi
    exact t_eq_tail (i+2) (by omega)
  have hp := tail_payment Z c w 95 (by norm_num [tTail] : 0 < tTail)
    hZ hc hzero hrec ht hbudget henv
  have hterminal : (line 95).positive (r 95)=max 0 (tTail*(Z 96/Z 95-1)) := by
    unfold Affine.positive
    rw [terminal_line]
    simp only [Affine.eval,r]
    congr 1 <;> ring
  rw [hterminal] at hh
  change Z 1*(line 0).positive (r 0) ≤ spend w c 95+
    Z 96*max 0 (tTail*(Z 96/Z 95-1)) at hh
  have htotal : Z 1*(line 0).positive (Z 1) ≤ B := by
    have hr0 : r 0=Z 1 := by simp [r,hZ0]
    rw [hr0] at hh
    linarith
  exact htotal


/-- The actual normalized scalar budget, including Z1=p. -/
def infiniteBudget (p : ℝ) : ℝ := p*infiniteValue A p w

def feasibleRatios : Set ℝ :=
  {p | 1 ≤ p ∧ p ≤ ratioUpper ∧ infiniteBudget p ≤ C}

/-- Supremum only over the frozenMIX96 profile, inside its prescribed ratio cap. -/
def fixedScalarEndpoint : ℝ := 1+K*sSup feasibleRatios

theorem full_floors : FullFloors w := by
  intro ρ hρ
  refine ⟨tau, by norm_num [tau], ?_⟩
  intro i
  have hf : tau ≤ w i := t_floor (i+2) (by omega)
  have hw : 0 ≤ w i := (t_positive (i+2) (by omega)).le
  exact hf.trans (le_mul_of_one_le_right hw (one_le_pow₀ hρ.le))

theorem lower_interval :
    1 ≤ QuarticM96MixScalarLowerPath20261020.p ∧
      QuarticM96MixScalarLowerPath20261020.p ≤ ratioUpper := by
  norm_num [QuarticM96MixScalarLowerPath20261020.p,ratioUpper,K]

theorem lower_infinite_budget :
    infiniteBudget QuarticM96MixScalarLowerPath20261020.p ≤ C := by
  have hp0 : 0 < QuarticM96MixScalarLowerPath20261020.p := by
    norm_num [QuarticM96MixScalarLowerPath20261020.p]
  have hr : QuarticM96MixScalarLowerPath20261020.r ∈
      ratioPathSet A QuarticM96MixScalarLowerPath20261020.p := by
    simpa only [A,QuarticM96MixScalarLowerPath20261020.A,
      QuarticM96MixScalarLowerPath20261020.K] using
      QuarticM96MixScalarLowerPath20261020.ratio_path_mem
  have hproper : Proper QuarticM96MixScalarLowerPath20261020.r :=
    product_envelope_of_eventually_one hr
      ⟨96,QuarticM96MixScalarLowerPath20261020.eventually_one⟩
  have hbudget (N : ℕ) :
      prefixSpend w QuarticM96MixScalarLowerPath20261020.r N ≤
        C/QuarticM96MixScalarLowerPath20261020.p := by
    apply (le_div_iff₀ hp0).mpr
    have hh := QuarticM96MixScalarLowerPath20261020.normalized_prefix_budget N
    simpa only [prefixSpend,w,QuarticM96MixScalarLowerPath20261020.w,
      QuarticM96MixScalarLowerPath20261020.C,mul_comm] using hh
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
  have hh := affine_payment Z c (infiniteBudget p)
    (fun i=>(hZ i).le) hc hZ0 hzero (fun i _ _=>(hrec i).le)
    hcap hupper hb henv
  simpa only [hZ1] using hh

theorem upper_infinite_budget_strict : C < infiniteBudget qUpper := by
  exact strict_budget_upper.trans_le (affine_lower_infinite qUpper qUpper_interval.1 qUpper_interval.2)

/-- No scalar budget-feasible starting ratio lies at or above qUpper. -/
theorem infeasible_above_upper (p : ℝ) (hpR : p ≤ ratioUpper) (hqp : qUpper ≤ p) :
    C < infiniteBudget p := by
  have hp : 1 ≤ p := qUpper_interval.1.trans hqp
  have hm := PositiveFiniteHeadBellman.Affine.product_mono (line 0)
    (line_slope_nonneg 0 (by omega)) qUpper_positive.le hqp
  exact strict_budget_upper.trans_le (hm.trans (affine_lower_infinite p hp hpR))

theorem lower_feasible : QuarticM96MixScalarLowerPath20261020.p ∈ feasibleRatios :=
  ⟨lower_interval.1,lower_interval.2,lower_infinite_budget⟩

theorem feasible_below_upper (p : ℝ) (hp : p ∈ feasibleRatios) : p < qUpper := by
  rcases hp with ⟨hp1,hpR,hbudget⟩
  by_contra hfail
  have hh := infeasible_above_upper p hpR (le_of_not_gt hfail)
  linarith

theorem feasible_nonempty : feasibleRatios.Nonempty :=
  ⟨QuarticM96MixScalarLowerPath20261020.p,lower_feasible⟩

theorem feasible_bounded : BddAbove feasibleRatios := by
  refine ⟨qUpper,?_⟩
  intro p hp
  exact (feasible_below_upper p hp).le

theorem fixed_endpoint_bounds :
    (863177/62500 : ℝ) ≤ fixedScalarEndpoint ∧
      fixedScalarEndpoint ≤ (13810833/1000000 : ℝ) := by
  have hlow : QuarticM96MixScalarLowerPath20261020.p ≤ sSup feasibleRatios :=
    le_csSup feasible_bounded lower_feasible
  have hhigh : sSup feasibleRatios ≤ qUpper := by
    apply csSup_le feasible_nonempty
    intro p hp
    exact (feasible_below_upper p hp).le
  have hk : 0 ≤ K := by norm_num [K]
  constructor
  · calc
      _ = 1+K*QuarticM96MixScalarLowerPath20261020.p := by
        simpa only [QuarticM96MixScalarLowerPath20261020.K] using
          QuarticM96MixScalarLowerPath20261020.endpoint_exact.symm
      _ ≤ 1+K*sSup feasibleRatios :=
        add_le_add (le_refl (1 : ℝ)) (mul_le_mul_of_nonneg_left hlow hk)
      _ = fixedScalarEndpoint := rfl
  · calc
      fixedScalarEndpoint = 1+K*sSup feasibleRatios := rfl
      _ ≤ 1+K*qUpper := add_le_add (le_refl (1 : ℝ)) (mul_le_mul_of_nonneg_left hhigh hk)
      _ = _ := upper_endpoint_exact

/-- Full fixed-profile infinite-value bracket, with both actual budget signs. -/
theorem fixed_infinite_value_bracket :
    infiniteBudget QuarticM96MixScalarLowerPath20261020.p ≤ C ∧
      C < infiniteBudget qUpper ∧
      (863177/62500 : ℝ) ≤ fixedScalarEndpoint ∧
      fixedScalarEndpoint ≤ (13810833/1000000 : ℝ) ∧
      (13810833/1000000-863177/62500 : ℝ)=1/1000000 := by
  exact ⟨lower_infinite_budget,upper_infinite_budget_strict,
    fixed_endpoint_bounds.1,fixed_endpoint_bounds.2,by norm_num⟩

end KLSConstantImprovement.QuarticM96MixFixedInfiniteScalarBracket20261020
#print axioms KLSConstantImprovement.QuarticM96MixFixedInfiniteScalarBracket20261020.lower_infinite_budget
#print axioms KLSConstantImprovement.QuarticM96MixFixedInfiniteScalarBracket20261020.affine_lower_infinite
#print axioms KLSConstantImprovement.QuarticM96MixFixedInfiniteScalarBracket20261020.upper_infinite_budget_strict
#print axioms KLSConstantImprovement.QuarticM96MixFixedInfiniteScalarBracket20261020.fixed_infinite_value_bracket

#print axioms KLSConstantImprovement.QuarticM96MixFixedInfiniteScalarBracket20261020.affine_payment
