import KLSConstantImprovement.AcceptedMix96Data
import KLSConstantImprovement.QuarticM48Support20261020
import KLSConstantImprovement.QuarticM32Support20261020
import KLSConstantImprovement.ExtendedSyntheticDegreeBudget
import KLSConstantImprovement.QuarticEndpointSyntheticCorner
import KLSConstantImprovement.Synthetic13068EndpointObstruction

/-! The same finite57 synthetic dual budget is paid by the actual MIX96
weighted profile. This supplies the precise method-floor interface for
positive mixtures, without treating the mixture as a single generator
ScalarCertificate. It is a restriction on scalar proof certificates, not
a lower bound for universalKLS or an admissible-law extremizer.
Root alone compiles this draft. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.AcceptedMix96MethodFloor13068
open KLSConstantImprovement.AcceptedMix96Data
open KLSConstantImprovement.ProperInfiniteRatioPathSelection
open KLSConstantImprovement.SubexponentialTerminalSupremum
open KLSConstantImprovement.SyntheticThirteen068FiniteOrbit20261020
  (z z_nonnegative z_two z_three z_four z_coupling)
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

theorem base48_synthetic_budget_lt :
    (∑ d ∈ Finset.Icc 2 57,QuarticM48Profile20261020Data.t d*z d/
      QuarticM48Profile20261020Data.K^d) < QuarticM48Profile20261020Data.C := by
  have hcorner : (265/4 : ℝ)+QuarticM48Profile20261020.A*10 ≤
      QuarticM48Profile20261020.B := by
    simpa only [QuarticM48Profile20261020.A,QuarticM48Profile20261020.B] using
      QuarticEndpointSyntheticCorner.endpoint_contains_synthetic_corner
        QuarticM48Support20261020.endpoint_certificate
        (by norm_num [QuarticM48Profile20261020.H])
  have hh := ExtendedSyntheticDegreeBudget.synthetic_budget_lt
    QuarticM48Profile20261020.scalar_certificate
    (by norm_num [QuarticM48Profile20261020.H]) hcorner z 57 (by omega) (by omega)
    (fun d _ _=>z_nonnegative d) z_two z_three z_four z_coupling
  simpa only [QuarticM48Profile20261020Data.profile] using hh

theorem base32_synthetic_budget_lt :
    (∑ d ∈ Finset.Icc 2 57,QuarticM32Profile20261020Data.t d*z d/
      QuarticM32Profile20261020Data.K^d) < QuarticM32Profile20261020Data.C := by
  have hcorner : (265/4 : ℝ)+QuarticM32Profile20261020.A*10 ≤
      QuarticM32Profile20261020.B := by
    simpa only [QuarticM32Profile20261020.A,QuarticM32Profile20261020.B] using
      QuarticEndpointSyntheticCorner.endpoint_contains_synthetic_corner
        QuarticM32Support20261020.endpoint_certificate
        (by norm_num [QuarticM32Profile20261020.H])
  have hh := ExtendedSyntheticDegreeBudget.synthetic_budget_lt
    QuarticM32Profile20261020.scalar_certificate
    (by norm_num [QuarticM32Profile20261020.H]) hcorner z 57 (by omega) (by omega)
    (fun d _ _=>z_nonnegative d) z_two z_three z_four z_coupling
  simpa only [QuarticM32Profile20261020Data.profile] using hh

theorem term_rescale (d : ℕ) :
    rawMix d*z d/K^d=
      QuarticM48Profile20261020Data.t d*z d/K^d+
        a*(QuarticM32Profile20261020Data.t d*z d/L^d) := by
  unfold rawMix
  rw [div_pow]
  field_simp [pow_ne_zero d (ne_of_gt K_positive),
    pow_ne_zero d (ne_of_gt L_positive)] <;> ring

/-- Every retained degree of the synthetic test lies below the96 cutoff. -/
theorem synthetic_sum_identity :
    (∑ d ∈ Finset.Icc 2 57,t d*z d/K^d)=
      (∑ d ∈ Finset.Icc 2 57,QuarticM48Profile20261020Data.t d*z d/K^d)+
        a*(∑ d ∈ Finset.Icc 2 57,QuarticM32Profile20261020Data.t d*z d/L^d) := by
  calc
    _ = ∑ d ∈ Finset.Icc 2 57,
        (QuarticM48Profile20261020Data.t d*z d/K^d+
          a*(QuarticM32Profile20261020Data.t d*z d/L^d)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd96 : d ≤ 96 := by
        have hd57 := (Finset.mem_Icc.mp hd).2
        omega
      rw [t,if_pos hd96]
      exact term_rescale d
    _ = _ := by rw [Finset.sum_add_distrib,←Finset.mul_sum]

theorem mixed_synthetic_budget_lt :
    (∑ d ∈ Finset.Icc 2 57,t d*z d/K^d) < C := by
  have h48 : (∑ d ∈ Finset.Icc 2 57,
      QuarticM48Profile20261020Data.t d*z d/K^d) < QuarticM48Profile20261020Data.C := by
    simpa only [K_eq] using base48_synthetic_budget_lt
  have h32 : (∑ d ∈ Finset.Icc 2 57,
      QuarticM32Profile20261020Data.t d*z d/L^d) < QuarticM32Profile20261020Data.C := by
    simpa only [L_eq] using base32_synthetic_budget_lt
  rw [synthetic_sum_identity,C_eq]
  exact add_lt_add h48 (mul_lt_mul_of_pos_left h32 (by norm_num [a]))

theorem full_floors : FullFloors (fun i=>t (i+2)) := by
  intro ρ hρ
  refine ⟨tau,by norm_num [tau],?_⟩
  intro i
  exact (t_floor (i+2) (by omega)).trans
    (le_mul_of_one_le_right (t_positive (i+2) (by omega)).le (one_le_pow₀ hρ.le))

theorem method_floor_thirteen068 (p : ℝ) (hp : 1 ≤ p)
    (hstrict : C < p*infiniteValue (2/K^2) p (fun i=>t (i+2))) :
    (3267/250 : ℝ) < 1+K*p := by
  exact Synthetic13068EndpointObstruction.endpoint_gt_thirteen068 K C t
    (by norm_num [K]) (fun d hd=>(t_positive d hd).le)
    (floors_nonempty full_floors) mixed_synthetic_budget_lt.le p hp hstrict

end KLSConstantImprovement.AcceptedMix96MethodFloor13068
#print axioms KLSConstantImprovement.AcceptedMix96MethodFloor13068.mixed_synthetic_budget_lt
#print axioms KLSConstantImprovement.AcceptedMix96MethodFloor13068.full_floors
#print axioms KLSConstantImprovement.AcceptedMix96MethodFloor13068.method_floor_thirteen068
