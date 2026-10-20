import CorrelatedInitializationScalarEndgame
import JointTwoHeadObservationOperatorEndgame
import TwoHeadObservationOperatorEndgame
import JointObservationOperatorEndgame

/-! Joint early observation information initializes the third orbit value.
The real orbit proof remains real; complexification supplies only its envelope. -/
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

theorem operator_norm_sq_le_rate_mul_correlated_initialization_threshold
    (R : H→L[𝕜]H) (L : E→L[𝕜]H) {K C p u v r a A B D : ℝ} (hK : 0<K) (_hC : 0≤C)
    (hp : 1<p)
    (hpu : p≤u) (hu : u≤p^2-a) (hpv : p^2≤v)
    (hr : 1<r) (hA : 1/p-1/v≤A) (hB : 1/u-1/v≤B)
    (hcost : r+D+C/v≤p)
    (hcomparison : ∀ v,‖R v‖^2≤‖R.adjoint v‖^2+‖L.adjoint v‖^2)
    (hbudget : jointObservationBudget R L K C)
    (hcap1 : ∀ f : H,K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2≤a*‖f‖^2)
    (hinit : ∀ f : H,‖f‖=1→
      v≤(p^2-K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2)*
        (p-(K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2)/p)-
        K⁻¹^3*‖L.adjoint ((R.adjoint^2) f)‖^2)
    (hjoint : ∀ f : H,A*(K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2)+
      B*(K⁻¹^3*‖L.adjoint ((R.adjoint^2) f)‖^2)≤D*‖f‖^2)
    (henvelope : ∀ rho : ℝ,1<rho → ∃ M : ℝ,∀ n,‖R.adjoint^n‖^2≤M*(K*rho)^n) :
    ‖R‖^2≤K*p := by
  have hs : 0<K*p := by positivity
  have hunit (f : H) (hf : ‖f‖=1) : energy R f 1≤K*p := by
    apply scalar_orbit_le_rate_mul_correlated_initialization_threshold (energy R f)
      (fun m => ‖L.adjoint (orbit R f m)‖^2) hK hp hpu hu hpv hr hA hB hcost
    · simp [energy,hf]
    · intro n; positivity
    · simpa only [orbit,hf,one_pow,mul_one] using hcap1 f
    · simpa only [orbit,hf,one_pow,mul_one] using hinit f hf
    · simpa only [orbit,hf,one_pow,mul_one] using hjoint f
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
  have hn : ‖R.adjoint‖≤Real.sqrt (K*p) := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro f hf
    apply (Real.le_sqrt (norm_nonneg _) hs.le).mpr
    simpa [energy,orbit] using hunit f hf
  rw [ContinuousLinearMap.adjoint.norm_map] at hn
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt hs.le)

end KLSBelow25.CoupledEnergy
#print axioms KLSBelow25.CoupledEnergy.operator_norm_sq_le_rate_mul_correlated_initialization_threshold

namespace KLSBelow25.CoupledEnergy
open ContinuousLinearMap
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem canonical_operator_endpoint_correlated_initialization_budget
    (R : H→L[ℂ]H) (L : E→L[ℂ]H) {κ K C p u v r a A B D : ℝ}
    (hκ : 0<κ) (hK : 0<K) (hC : 0≤C)
    (hp : 1<p)
    (hpu : p≤u) (hu : u≤p^2-a) (hpv : p^2≤v)
    (hr : 1<r) (hA : 1/p-1/v≤A) (hB : 1/u-1/v≤B)
    (hcost : r+D+C/v≤p)
    (hcomparison : rationalIntegrationComparison R L κ)
    (hbudget : jointObservationBudget R L K C)
    (hcap1 : ∀ f : H,K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2≤a*‖f‖^2)
    (hinit : ∀ f : H,‖f‖=1→
      v≤(p^2-K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2)*
        (p-(K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2)/p)-
        K⁻¹^3*‖L.adjoint ((R.adjoint^2) f)‖^2)
    (hjoint : ∀ f : H,A*(K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2)+
      B*(K⁻¹^3*‖L.adjoint ((R.adjoint^2) f)‖^2)≤D*‖f‖^2) :
    1+‖R‖^2≤1+K*p := by
  rcases subsingleton_or_nontrivial H with hsub | hn
  · have hR : R=0 := Subsingleton.elim _ _
    simp only [hR,norm_zero,zero_pow (by decide : 2≠0),add_zero]
    have hp : 0 ≤ K*p := by positivity
    linarith
  · have hU := canonicalIntegrationResolvent_inverse R L hκ.le
    have hlinear := linear_curvature_comparison_of_resolvent R L
      (canonicalIntegrationResolvent R L κ) hκ hU hcomparison
    have hscalar := scalar_curvature_comparison_of_resolvent R L
      (canonicalIntegrationResolvent R L κ) hκ hU hcomparison
    have hspec : spectralRadius ℂ R.adjoint≤ENNReal.ofReal (Real.sqrt K) := by
      apply spectralRadius_le_of_scalar_comparison R.adjoint L.adjoint hκ hK 1
      · simpa only [adjoint_adjoint] using hscalar
      · intro m hm
        calc
          ‖L.adjoint.comp (R.adjoint^m)‖^2≤C*K^(m+1) :=
            observation_norm_sq_le_of_joint_budget R L hK hC hbudget m hm
          _ = (C*K)*K^m := by rw [pow_succ]; ring
    have henvelope : ∀ rho : ℝ,1<rho → ∃ M : ℝ,∀ n,
        ‖R.adjoint^n‖^2≤M*(K*rho)^n :=
      fun rho hrho => squared_power_envelope_of_spectralRadius_le R.adjoint hK hspec rho hrho
    have hb := operator_norm_sq_le_rate_mul_correlated_initialization_threshold R L hK hC hp hpu hu hpv hr hA hB hcost
      hlinear hbudget hcap1 hinit hjoint henvelope
    linarith

end KLSBelow25.CoupledEnergy

#print axioms KLSBelow25.CoupledEnergy.canonical_operator_endpoint_correlated_initialization_budget

namespace KLSBelow25.RealHilbertComplexification
open ContinuousLinearMap CoupledEnergy
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem real_canonical_operator_endpoint_correlated_initialization_budget
    (R : H→L[ℝ]H) (L : F→L[ℝ]H) {κ K C p u v r a A B D : ℝ}
    (hκ : 0<κ) (hK : 0<K) (hC : 0≤C)
    (hp : 1<p)
    (hpu : p≤u) (hu : u≤p^2-a) (hpv : p^2≤v)
    (hr : 1<r) (hA : 1/p-1/v≤A) (hB : 1/u-1/v≤B)
    (hcost : r+D+C/v≤p)
    (hcomparison : realRationalIntegrationComparison R L κ)
    (hbudget : jointObservationBudget R L K C)
    (hcap1 : ∀ f : H,K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2≤a*‖f‖^2)
    (hinit : ∀ f : H,‖f‖=1→
      v≤(p^2-K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2)*
        (p-(K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2)/p)-
        K⁻¹^3*‖L.adjoint ((R.adjoint^2) f)‖^2)
    (hjoint : ∀ f : H,A*(K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2)+
      B*(K⁻¹^3*‖L.adjoint ((R.adjoint^2) f)‖^2)≤D*‖f‖^2) :
    1+‖R‖^2≤1+K*p := by
  rcases subsingleton_or_nontrivial (RealHilbertComplexification H) with hsub | hn
  · have he : extend R=0 := Subsingleton.elim _ _
    have hzero : ‖R‖=0 := by simpa only [norm_extend,norm_zero] using congrArg norm he
    rw [hzero]
    have hpos : 0≤K*p := by positivity
    nlinarith
  · have hcomp := rationalIntegrationComparison_extend R L hκ.le hcomparison
    have hU := canonicalIntegrationResolvent_inverse (extend R) (extend L) hκ.le
    have hlinearC := linear_curvature_comparison_of_resolvent (extend R) (extend L)
      (canonicalIntegrationResolvent (extend R) (extend L) κ) hκ hU hcomp
    have hlinear : ∀ x : H,‖R x‖^2≤‖R.adjoint x‖^2+‖L.adjoint x‖^2 := by
      intro x
      have hx := hlinearC (⟨x,0⟩ : RealHilbertComplexification H)
      simpa [←extend_adjoint,norm_sq] using hx
    have hscalar := scalar_curvature_comparison_of_resolvent (extend R) (extend L)
      (canonicalIntegrationResolvent (extend R) (extend L) κ) hκ hU hcomp
    have hbudgetC := jointObservationBudget_extend R L hbudget
    have hspec : spectralRadius ℂ (extend R).adjoint≤ENNReal.ofReal (Real.sqrt K) := by
      apply spectralRadius_le_of_scalar_comparison (extend R).adjoint (extend L).adjoint hκ hK 1
      · simpa only [adjoint_adjoint] using hscalar
      · intro m hm
        calc
          ‖(extend L).adjoint.comp ((extend R).adjoint^m)‖^2≤C*K^(m+1) :=
            observation_norm_sq_le_of_joint_budget (extend R) (extend L) hK hC hbudgetC m hm
          _ = (C*K)*K^m := by rw [pow_succ]; ring
    have henvelope : ∀ rho : ℝ,1<rho → ∃ M : ℝ,∀ n,
        ‖R.adjoint^n‖^2≤M*(K*rho)^n := by
      intro rho hrho
      obtain ⟨M,hM⟩ := squared_power_envelope_of_spectralRadius_le
        (extend R).adjoint hK hspec rho hrho
      refine ⟨M,fun n => ?_⟩
      simpa only [←extend_adjoint,←extend_pow,norm_extend] using hM n
    have hb := operator_norm_sq_le_rate_mul_correlated_initialization_threshold R L
      hK hC hp hpu hu hpv hr hA hB hcost hlinear hbudget hcap1 hinit hjoint henvelope
    linarith

end KLSBelow25.RealHilbertComplexification
#print axioms KLSBelow25.RealHilbertComplexification.real_canonical_operator_endpoint_correlated_initialization_budget
