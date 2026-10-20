import TwoHeadObservationScalarEndgame
import JointObservationOperatorEndgame

/-! Two separately proved low-degree observation caps sharpen the actual
canonical operator endgame. The operator and all adjoints are literal bounded maps. -/
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

theorem operator_norm_sq_le_rate_mul_two_head_threshold
    (R : H→L[𝕜]H) (L : E→L[𝕜]H) {K C p u v r a b : ℝ} (hK : 0<K) (_hC : 0≤C)
    (hp : 1<p) (ha : 0≤a) (hb : 0≤b) (hCab : a+b≤C)
    (hpu : p≤u) (huv : u≤v) (hu : u≤p^2-a) (hv : v≤u*(p-a/p)-b)
    (hr : 1<r) (hcost : r+a/p+b/u+(C-a-b)/v≤p)
    (hcomparison : ∀ v,‖R v‖^2≤‖R.adjoint v‖^2+‖L.adjoint v‖^2)
    (hbudget : jointObservationBudget R L K C)
    (hcap1 : ∀ f : H,K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2≤a*‖f‖^2)
    (hcap2 : ∀ f : H,K⁻¹^3*‖L.adjoint ((R.adjoint^2) f)‖^2≤b*‖f‖^2)
    (henvelope : ∀ rho : ℝ,1<rho → ∃ M : ℝ,∀ n,‖R.adjoint^n‖^2≤M*(K*rho)^n) :
    ‖R‖^2≤K*p := by
  have hs : 0<K*p := by positivity
  have hunit (f : H) (hf : ‖f‖=1) : energy R f 1≤K*p := by
    apply scalar_orbit_le_rate_mul_two_head_threshold (energy R f)
      (fun m => ‖L.adjoint (orbit R f m)‖^2) hK hp ha hb hCab hpu huv hu hv hr hcost
    · simp [energy,hf]
    · intro n; positivity
    · simpa only [orbit,hf,one_pow,mul_one] using hcap1 f
    · simpa only [orbit,hf,one_pow,mul_one] using hcap2 f
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
#print axioms KLSBelow25.CoupledEnergy.operator_norm_sq_le_rate_mul_two_head_threshold

namespace KLSBelow25.CoupledEnergy
open ContinuousLinearMap
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem canonical_operator_endpoint_two_head_budget
    (R : H→L[ℂ]H) (L : E→L[ℂ]H) {κ K C p u v r a b : ℝ}
    (hκ : 0<κ) (hK : 0<K) (hC : 0≤C)
    (hp : 1<p) (ha : 0≤a) (hb : 0≤b) (hCab : a+b≤C)
    (hpu : p≤u) (huv : u≤v) (hu : u≤p^2-a) (hv : v≤u*(p-a/p)-b)
    (hr : 1<r) (hcost : r+a/p+b/u+(C-a-b)/v≤p)
    (hcomparison : rationalIntegrationComparison R L κ)
    (hbudget : jointObservationBudget R L K C)
    (hcap1 : ∀ f : H,K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2≤a*‖f‖^2)
    (hcap2 : ∀ f : H,K⁻¹^3*‖L.adjoint ((R.adjoint^2) f)‖^2≤b*‖f‖^2) :
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
    have hb := operator_norm_sq_le_rate_mul_two_head_threshold R L hK hC hp ha hb hCab hpu huv hu hv hr hcost
      hlinear hbudget hcap1 hcap2 henvelope
    linarith

end KLSBelow25.CoupledEnergy

#print axioms KLSBelow25.CoupledEnergy.canonical_operator_endpoint_two_head_budget

namespace KLSBelow25.RealHilbertComplexification
open ContinuousLinearMap CoupledEnergy
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem individual_observation_cap_extend
    (R : H→L[ℝ]H) (L : F→L[ℝ]H) (m : ℕ) {K A : ℝ}
    (hcap : ∀ f : H,K⁻¹^(m+1)*‖L.adjoint ((R.adjoint^m) f)‖^2≤A*‖f‖^2) :
    ∀ z : RealHilbertComplexification H,K⁻¹^(m+1)*
      ‖(extend L).adjoint (((extend R).adjoint^m) z)‖^2≤A*‖z‖^2 := by
  intro z
  have he : ‖(extend L).adjoint (((extend R).adjoint^m) z)‖^2=
      ‖L.adjoint ((R.adjoint^m) z.re)‖^2+‖L.adjoint ((R.adjoint^m) z.im)‖^2 := by
    simp only [←extend_adjoint,←extend_pow]
    change ‖extend (L.adjoint.comp (R.adjoint^m)) z‖^2=_
    rw [norm_sq]
    rfl
  rw [he,norm_sq]
  have hh := add_le_add (hcap z.re) (hcap z.im)
  nlinarith [hh]

theorem real_canonical_operator_endpoint_two_head_budget
    (R : H→L[ℝ]H) (L : F→L[ℝ]H) {κ K C p u v r a b : ℝ}
    (hκ : 0<κ) (hK : 0<K) (hC : 0≤C)
    (hp : 1<p) (ha : 0≤a) (hb : 0≤b) (hCab : a+b≤C)
    (hpu : p≤u) (huv : u≤v) (hu : u≤p^2-a) (hv : v≤u*(p-a/p)-b)
    (hr : 1<r) (hcost : r+a/p+b/u+(C-a-b)/v≤p)
    (hcomparison : realRationalIntegrationComparison R L κ)
    (hbudget : jointObservationBudget R L K C)
    (hcap1 : ∀ f : H,K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2≤a*‖f‖^2)
    (hcap2 : ∀ f : H,K⁻¹^3*‖L.adjoint ((R.adjoint^2) f)‖^2≤b*‖f‖^2) :
    1+‖R‖^2≤1+K*p := by
  have h := canonical_operator_endpoint_two_head_budget (extend R) (extend L) hκ hK hC
    hp ha hb hCab hpu huv hu hv hr hcost
    (rationalIntegrationComparison_extend R L hκ.le hcomparison)
    (jointObservationBudget_extend R L hbudget)
    (individual_observation_cap_extend R L 1 hcap1)
    (individual_observation_cap_extend R L 2 hcap2)
  simpa only [norm_extend] using h

end KLSBelow25.RealHilbertComplexification
#print axioms KLSBelow25.RealHilbertComplexification.real_canonical_operator_endpoint_two_head_budget
