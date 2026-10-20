import JointObservationScalarEndgame
import BootstrapOperatorEndgame
import RealOperatorComplexification

/-! Generic operator endgame for a joint weighted observation estimate.
All law-specific estimates remain explicit inputs in this abstract module. -/
noncomputable section
open InnerProductSpace AdjointOrbitRecurrence
open scoped BigOperators
namespace KLSBelow25.CoupledEnergy
open ContinuousLinearMap
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {𝕜 H E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

def jointObservationBudget (R : H→L[𝕜]H) (L : E→L[𝕜]H) (K C : ℝ) : Prop :=
  ∀ (N : ℕ) (f : H),∑ m∈Finset.Icc 1 N,
    K⁻¹^(m+1)*‖L.adjoint ((R.adjoint^m) f)‖^2 ≤ C*‖f‖^2

theorem observation_norm_sq_le_of_joint_budget
    (R : H→L[𝕜]H) (L : E→L[𝕜]H) {K C : ℝ} (hK : 0<K) (hC : 0≤C)
    (hbudget : jointObservationBudget R L K C) (m : ℕ) (hm : 1 ≤ m) :
    ‖L.adjoint.comp (R.adjoint^m)‖^2≤C*K^(m+1) := by
  have hpoint (f : H) : ‖L.adjoint ((R.adjoint^m) f)‖^2 ≤ C*K^(m+1)*‖f‖^2 := by
    have hs : K⁻¹^(m+1)*‖L.adjoint ((R.adjoint^m) f)‖^2 ≤
        ∑ j∈Finset.Icc 1 m,K⁻¹^(j+1)*‖L.adjoint ((R.adjoint^j) f)‖^2 := by
      apply Finset.single_le_sum (f := fun j : ℕ => K⁻¹^(j+1)*‖L.adjoint ((R.adjoint^j) f)‖^2)
      · intro j hj
        positivity
      · exact Finset.mem_Icc.mpr ⟨hm,le_rfl⟩
    have ht := hs.trans (hbudget m f)
    have hid : K^(m+1)*(K⁻¹^(m+1)*‖L.adjoint ((R.adjoint^m) f)‖^2)=
        ‖L.adjoint ((R.adjoint^m) f)‖^2 := by
      rw [inv_pow]
      field_simp
    have he := mul_le_mul_of_nonneg_left ht (pow_nonneg hK.le (m+1))
    rw [hid] at he
    nlinarith [he]
  have hn : ‖L.adjoint.comp (R.adjoint^m)‖≤Real.sqrt (C*K^(m+1)) := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro f hf
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    simpa only [hf,one_pow,mul_one,ContinuousLinearMap.comp_apply] using hpoint f
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt (by positivity))

theorem energy_recurrence_actual_observation
    (R : H→L[𝕜]H) (L : E→L[𝕜]H)
    (hcomparison : ∀ v,‖R v‖^2≤‖R.adjoint v‖^2+‖L.adjoint v‖^2)
    (f : H) (m : ℕ) (hm : 0<energy R f m) :
    energy R f (m+1)^2/energy R f m-‖L.adjoint (orbit R f (m+1))‖^2≤energy R f (m+2) := by
  have hc := energy_cauchy R f m
  have hp := hcomparison (orbit R f (m+1))
  have he : ‖R.adjoint (orbit R f (m+1))‖^2=energy R f (m+2) := by
    simp only [energy,show m+2=(m+1)+1 by omega,orbit_succ]
  rw [he] at hp
  have hh := hc.trans (mul_le_mul_of_nonneg_left hp hm.le)
  have hd : energy R f (m+1)^2/energy R f m≤
      energy R f (m+2)+‖L.adjoint (orbit R f (m+1))‖^2 :=
    (div_le_iff₀ hm).mpr (by simpa only [mul_comm] using hh)
  linarith

theorem operator_norm_sq_le_rate_mul_one_add_budget
    (R : H→L[𝕜]H) (L : E→L[𝕜]H) {K C : ℝ} (hK : 0<K) (hC : 0≤C)
    (hcomparison : ∀ v,‖R v‖^2≤‖R.adjoint v‖^2+‖L.adjoint v‖^2)
    (hbudget : jointObservationBudget R L K C)
    (henvelope : ∀ rho : ℝ,1<rho → ∃ M : ℝ,∀ n,‖R.adjoint^n‖^2≤M*(K*rho)^n) :
    ‖R‖^2≤K*(1+C) := by
  have hs : 0<K*(1+C) := by positivity
  have hunit (f : H) (hf : ‖f‖=1) : energy R f 1≤K*(1+C) := by
    apply scalar_orbit_le_rate_mul_one_add_budget (energy R f)
      (fun m => ‖L.adjoint (orbit R f m)‖^2) hK hC
    · simp [energy,hf]
    · intro n; positivity
    · intro N
      simpa only [orbit,hf,one_pow,mul_one] using hbudget N f
    · intro n hn _
      exact energy_recurrence_actual_observation R L hcomparison f n hn
    · intro rho hrho
      obtain ⟨M,hM⟩ := henvelope rho hrho
      refine ⟨M,fun n => ?_⟩
      have hn := (R.adjoint^n).le_opNorm f
      rw [hf,mul_one] at hn
      exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (hM n)
  have hn : ‖R.adjoint‖≤Real.sqrt (K*(1+C)) := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro f hf
    apply (Real.le_sqrt (norm_nonneg _) hs.le).mpr
    simpa [energy,orbit] using hunit f hf
  rw [ContinuousLinearMap.adjoint.norm_map] at hn
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt hs.le)

end KLSBelow25.CoupledEnergy
#print axioms KLSBelow25.CoupledEnergy.observation_norm_sq_le_of_joint_budget
#print axioms KLSBelow25.CoupledEnergy.operator_norm_sq_le_rate_mul_one_add_budget

namespace KLSBelow25.CoupledEnergy
open ContinuousLinearMap
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem canonical_operator_endpoint_joint_budget
    (R : H→L[ℂ]H) (L : E→L[ℂ]H) {a K C : ℝ}
    (ha : 0<a) (hK : 0<K) (hC : 0≤C)
    (hcomparison : rationalIntegrationComparison R L a)
    (hbudget : jointObservationBudget R L K C) :
    1+‖R‖^2≤1+K*(1+C) := by
  rcases subsingleton_or_nontrivial H with hsub | hn
  · have hR : R=0 := Subsingleton.elim _ _
    simp only [hR,norm_zero,zero_pow (by decide : 2≠0),add_zero]
    have hp : 0 ≤ K*(1+C) := by positivity
    linarith
  · have hU := canonicalIntegrationResolvent_inverse R L ha.le
    have hlinear := linear_curvature_comparison_of_resolvent R L
      (canonicalIntegrationResolvent R L a) ha hU hcomparison
    have hscalar := scalar_curvature_comparison_of_resolvent R L
      (canonicalIntegrationResolvent R L a) ha hU hcomparison
    have hspec : spectralRadius ℂ R.adjoint≤ENNReal.ofReal (Real.sqrt K) := by
      apply spectralRadius_le_of_scalar_comparison R.adjoint L.adjoint ha hK 1
      · simpa only [adjoint_adjoint] using hscalar
      · intro m hm
        calc
          ‖L.adjoint.comp (R.adjoint^m)‖^2≤C*K^(m+1) :=
            observation_norm_sq_le_of_joint_budget R L hK hC hbudget m hm
          _ = (C*K)*K^m := by rw [pow_succ]; ring
    have henvelope : ∀ rho : ℝ,1<rho → ∃ M : ℝ,∀ n,
        ‖R.adjoint^n‖^2≤M*(K*rho)^n :=
      fun rho hrho => squared_power_envelope_of_spectralRadius_le R.adjoint hK hspec rho hrho
    have hb := operator_norm_sq_le_rate_mul_one_add_budget R L hK hC hlinear hbudget henvelope
    linarith

end KLSBelow25.CoupledEnergy

namespace KLSBelow25.RealHilbertComplexification
open ContinuousLinearMap CoupledEnergy
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem jointObservationBudget_extend
    (R : H→L[ℝ]H) (L : F→L[ℝ]H) {K C : ℝ}
    (hbudget : jointObservationBudget R L K C) :
    jointObservationBudget (extend R) (extend L) K C := by
  intro N z
  have he (m : ℕ) : ‖(extend L).adjoint (((extend R).adjoint^m) z)‖^2=
      ‖L.adjoint ((R.adjoint^m) z.re)‖^2+‖L.adjoint ((R.adjoint^m) z.im)‖^2 := by
    simp only [←extend_adjoint,←extend_pow]
    change ‖extend (L.adjoint.comp (R.adjoint^m)) z‖^2=_
    rw [norm_sq]
    rfl
  simp_rw [he,mul_add]
  rw [Finset.sum_add_distrib]
  have hh := add_le_add (hbudget N z.re) (hbudget N z.im)
  rw [norm_sq]
  nlinarith [hh]

theorem real_canonical_operator_endpoint_joint_budget
    (R : H→L[ℝ]H) (L : F→L[ℝ]H) {a K C : ℝ}
    (ha : 0<a) (hK : 0<K) (hC : 0≤C)
    (hcomparison : realRationalIntegrationComparison R L a)
    (hbudget : jointObservationBudget R L K C) :
    1+‖R‖^2≤1+K*(1+C) := by
  have h := canonical_operator_endpoint_joint_budget (extend R) (extend L) ha hK hC
    (rationalIntegrationComparison_extend R L ha.le hcomparison)
    (jointObservationBudget_extend R L hbudget)
  simpa only [norm_extend] using h

end KLSBelow25.RealHilbertComplexification
#print axioms KLSBelow25.CoupledEnergy.canonical_operator_endpoint_joint_budget
#print axioms KLSBelow25.RealHilbertComplexification.real_canonical_operator_endpoint_joint_budget
