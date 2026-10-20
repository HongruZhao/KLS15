import KLSConstantImprovement.ResumeRaw40147BellmanScalar
import KLSConstantImprovement.GeneralWeightedObservation
import KLSConstantImprovement.Cubic239BellmanEndpoint
import KLSConstantImprovement.LongPrefixWeightedProfile
import ActualIndividualObservationCaps
import NormalizedProjectionEnergyInequality

/-! Actual inverse-gradient realization of the positive finite-head
Bellman certificate. The universal raw401.47 observation is the sole additional hypothesis. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace ContinuousLinearMap AdjointOrbitRecurrence
open scoped ContDiff ENNReal BigOperators
namespace KLSConstantImprovement.ResumeRaw40147BellmanOperator
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSBelow25.ProjectionOrbitSlack
open KLSConstantImprovement.ResumeRaw40147BellmanData
open KLSConstantImprovement.WeightedOrbitBellmanTail
set_option maxHeartbeats 110000000
set_option synthInstance.maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  (hμ : admissibleMeasure (potentialMeasure φ))

include hμ in
theorem unit_energy_le
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound (40147/100))
    (f : GradedCenteredTensorHilbert hφ) (hf : ‖f‖=1) :
    ‖(gradedTensorIntegration hφ hκ hlower).adjoint f‖^2 ≤ K*p := by
  let R := gradedTensorIntegration hφ hκ hlower
  let L := gradedConstantIntegration hφ hκ hlower hμ.isotropic
  let P := gradedLinearTensorProjection hφ hκ hlower hμ.isotropic
  let Z := ProjectionOrbitSlack.normalizedOrbit R f K
  let c : ℕ → ℝ := fun i=>‖P (orbit R f (i+1))‖^2/K^(i+2)
  have hK : 0 < K := by norm_num [K]
  have hC : 0 ≤ originalC := by norm_num [originalC]
  have hcomp := actual_graded_linear_projection_comparison hφ hκ hlower hμ.isotropic
  change ∀ v,‖R v‖^2 ≤ ‖R.adjoint v‖^2+‖P v‖^2 at hcomp
  have hbudgetRaw : ∀ (N : ℕ) (g : Lp ℝ 2 (potentialMeasure φ)),
      (∑ d ∈ Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy (potentialMeasure φ) g d/
        (d.factorial : ℝ)^2) ≤ originalC*‖g‖^2 := by
    intro N g
    simpa only [t,LongPrefixCubicBellmanData.t,K,originalC,LongPrefixWeightedProfileData.K,
      LongPrefixWeightedProfileData.C] using
      LongPrefixWeightedProfile.raw_budget_norm_sq N hμ g
  have hZ0 : Z 0=1 := by
    simp [Z,ProjectionOrbitSlack.normalizedOrbit,AdjointOrbitRecurrence.energy,orbit,hf]
  have hZnonneg (i : ℕ) : 0 ≤ Z i := by dsimp [Z,ProjectionOrbitSlack.normalizedOrbit,AdjointOrbitRecurrence.energy];positivity
  have hc (i : ℕ) : 0 ≤ c i := by dsimp [c];positivity
  have hzero (i : ℕ) (hi : Z i=0) : Z (i+1)=0 := by
    have hh : AdjointOrbitRecurrence.energy R f i=0 := by
      have he := congrArg (fun x : ℝ=>x*K^i) hi
      dsimp only [Z,ProjectionOrbitSlack.normalizedOrbit] at he
      field_simp [ne_of_gt hK] at he
      simpa using he
    have hh' := energy_zero_succ R f i hh
    simp [Z,ProjectionOrbitSlack.normalizedOrbit,hh']
  have hrec (i : ℕ) (hi : 0 < Z i) (hi1 : 0 < Z (i+1)) :
      Z (i+1)^2/Z i-c i ≤ Z (i+2) := by
    simpa only [Z,c,show i+1+1=i+2 by omega] using
      normalized_projection_energy_recurrence R P f hK hcomp i hi hi1
  have hcident (i : ℕ) : c i=K⁻¹^(i+2)*‖L.adjoint ((R.adjoint^(i+1)) f)‖^2 := by
    dsimp only [c,P,L,R,orbit]
    rw [gradedLinearTensorProjection_norm]
    simp only [div_eq_mul_inv,inv_pow,mul_comm]
  have hbudget_original (N : ℕ) : spend (fun i=>t (i+2)) c N ≤ originalC := by
    have hb := GeneralWeightedObservation.actual_general_graded_observability
      hφ hκ hlower hμ (fun d=>if 2 ≤ d then t d*K⁻¹^d else 0)
      (fun d=>by
        split_ifs with hd
        · exact mul_nonneg (t_positive d hd).le (pow_nonneg (inv_nonneg.mpr hK.le) d)
        · exact le_refl _) hC
      (by
        intro M g
        convert hbudgetRaw M g using 1
        apply Finset.sum_congr rfl
        intro d hd
        rw [if_pos (Finset.mem_Icc.mp hd).1]) N f
    simp only [hf,one_pow,mul_one] at hb
    have he : spend (fun i=>t (i+2)) c N=
        ∑ i∈Finset.Icc 1 N,(if 2 ≤ i+1 then t (i+1)*K⁻¹^(i+1) else 0)*
          ‖L.adjoint ((R.adjoint^i) f)‖^2 := by
      rw [←KLSBelow25.CoupledEnergy.prefixBudget_eq_Icc]
      unfold KLSBelow25.CoupledEnergy.prefixBudget spend
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only
      rw [if_pos (by omega),hcident]
      simp only [Nat.add_assoc,Nat.reduceAdd]
      ring
    exact he.trans_le hb
  have hscalar (g : Lp ℝ 2 (potentialMeasure φ)) :
      actualAppellEnergy (potentialMeasure φ) g 3 ≤ (40147/100)*‖g‖^2 := by
    have hh := hraw hμ (Lp.memLp g)
    rwa [←actualLp_norm_sq_eq_integral] at hh
  have hdual : dualWeight*c 0+c 1 ≤ dualHeight := by
    have hb0 := actual_first_graded_observation_sq_le hφ hκ hlower hμ f
    have hb1 := actual_individual_graded_observation_sq_le hφ hκ hlower hμ 2
      (by norm_num : (0 : ℝ) ≤ (40147/100)) hscalar f
    have h0 : c 0 ≤ 2/K^2 := by
      have hh : ‖L.adjoint ((R.adjoint^1) f)‖^2 ≤ 2 := by
        simpa only [L,R,hf,one_pow,mul_one] using hb0
      rw [hcident 0]
      calc
        _ ≤ K⁻¹^2*2 := mul_le_mul_of_nonneg_left hh (sq_nonneg _)
        _ = _ := by field_simp <;> ring
    have h1 : c 1 ≤ (40147/100)/(36*K^3) := by
      have hh : ‖L.adjoint ((R.adjoint^2) f)‖^2 ≤ (40147/100)/36 := by
        norm_num [L,R,hf] at hb1 ⊢
        exact hb1
      rw [hcident 1]
      calc
        _ ≤ K⁻¹^3*((40147/100)/36) := mul_le_mul_of_nonneg_left hh (pow_nonneg (inv_nonneg.mpr hK.le) 3)
        _ = _ := by field_simp <;> ring
    calc
      dualWeight*c 0+c 1 ≤ dualWeight*(2/K^2)+(40147/100)/(36*K^3) :=
        add_le_add (mul_le_mul_of_nonneg_left h0 (by norm_num [dualWeight,LongPrefixCubicBellmanData.dualWeight])) h1
      _ = dualHeight := by norm_num [dualHeight,dualWeight,LongPrefixCubicBellmanData.dualWeight,K]
  have hbudget : ∀ N,spend w c N ≤ C := augmented_budget c hc hbudget_original hdual
  have hcap (i : ℕ) : c i ≤ A*Z i := by
    have hb := actual_first_graded_observation_sq_le hφ hκ hlower hμ (orbit R f i)
    have he : ‖P (orbit R f (i+1))‖^2=
        ‖L.adjoint ((R.adjoint^1) (orbit R f i))‖^2 := by
      rw [orbit_succ,gradedLinearTensorProjection_norm]
      simp only [pow_one]
      rfl
    have hd := div_le_div_of_nonneg_right hb (pow_nonneg hK.le (i+2))
    change c i ≤ A*Z i
    dsimp only [c]
    rw [he]
    convert hd using 1 <;> (try dsimp only [A,LongPrefixCubicBellmanData.A,LongPrefixCubicBellmanData.K,K,Z,ProjectionOrbitSlack.normalizedOrbit,AdjointOrbitRecurrence.energy]) <;>
      (try rw [pow_add K i 2]) <;> field_simp <;> ring
  have hold : ‖R‖^2 ≤ 1334537805407/100000000000 := by
    have hh := Cubic239BellmanOperator.operator_norm_sq_le hφ hκ hlower hμ
    calc
      _ ≤ Cubic239BellmanData.K*Cubic239BellmanData.p := hh
      _ = _ := by norm_num [Cubic239BellmanData.K,Cubic239BellmanData.p]
  have hupper (i : ℕ) : Z (i+1) ≤ ratioUpper*Z i := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (R.adjoint.le_opNorm (orbit R f i)) 2
    rw [mul_pow,ContinuousLinearMap.adjoint.norm_map] at hh
    have hb := mul_le_mul_of_nonneg_right hold (sq_nonneg ‖orbit R f i‖)
    have he : AdjointOrbitRecurrence.energy R f (i+1) ≤ (1334537805407/100000000000)*AdjointOrbitRecurrence.energy R f i := by
      simpa only [AdjointOrbitRecurrence.energy,orbit_succ] using hh.trans hb
    have hd := div_le_div_of_nonneg_right he (pow_nonneg hK.le (i+1))
    convert hd using 1 <;> (try dsimp only [Z,ProjectionOrbitSlack.normalizedOrbit,ratioUpper,LongPrefixCubicBellmanData.ratioUpper,LongPrefixCubicBellmanData.K,K]) <;>
      (try rw [pow_succ]) <;> field_simp <;> ring
  have henv : ∀ ρ : ℝ,1 < ρ → ∃ M : ℝ,∀ i,Z i ≤ M*ρ^i := by
    intro ρ hρ
    obtain ⟨M,hM⟩ := GeneralWeightedObservation.actual_general_adjoint_power_envelope
      hφ hκ hlower hμ hK hC (by norm_num [tau,LongPrefixCubicBellmanData.tau] : 0 < tau) t t_floor hbudgetRaw ρ hρ
    refine ⟨M,fun i=>?_⟩
    have hop := pow_le_pow_left₀ (norm_nonneg _) ((R.adjoint^i).le_opNorm f) 2
    simp only [hf,mul_one] at hop
    have he : AdjointOrbitRecurrence.energy R f i ≤ M*(K*ρ)^i := by
      simpa only [AdjointOrbitRecurrence.energy,orbit] using hop.trans (hM i)
    have hd := div_le_div_of_nonneg_right he (pow_nonneg hK.le i)
    convert hd using 1 <;> (try dsimp only [Z,ProjectionOrbitSlack.normalizedOrbit]) <;>
      (try rw [mul_pow]) <;> field_simp <;> ring
  have hh := ResumeRaw40147BellmanScalar.normalized_orbit_bound Z c hZnonneg hc hZ0
    hzero hrec hcap hupper hbudget henv
  have hh' : ‖R.adjoint f‖^2/K ≤ p := by
    simpa only [Z,ProjectionOrbitSlack.normalizedOrbit,AdjointOrbitRecurrence.energy,orbit, pow_one] using hh
  exact (div_le_iff₀ hK).mp hh' |>.trans_eq (mul_comm _ _)

include hμ in
theorem operator_norm_sq_le
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound (40147/100))
    :
    ‖gradedTensorIntegration hφ hκ hlower‖^2 ≤ K*p := by
  let R := gradedTensorIntegration hφ hκ hlower
  have hp : 0 < K*p := by norm_num [K,p]
  have hn : ‖R.adjoint‖ ≤ Real.sqrt (K*p) := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro f hf
    apply (Real.le_sqrt (norm_nonneg _) hp.le).2
    exact unit_energy_le hφ hκ hlower hμ hraw f hf
  rw [ContinuousLinearMap.adjoint.norm_map] at hn
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt hp.le)

end KLSConstantImprovement.ResumeRaw40147BellmanOperator
#print axioms KLSConstantImprovement.ResumeRaw40147BellmanOperator.unit_energy_le
#print axioms KLSConstantImprovement.ResumeRaw40147BellmanOperator.operator_norm_sq_le
