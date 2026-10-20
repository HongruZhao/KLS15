import ActualSeed239ExpandedSharedResourcePayment
import ActualSeed239ExpandedAdjointEnvelope
import ActualProjectionExpandedProfileData
import NormalizedProjectionOrbitRecurrence
import ProjectionSlackFiniteChargeCost
import ProjectionSlackEnvelopeContradiction
import ProjectionFiniteEarlyInitialization
import NormalizedProjectionEnergyInequality

/-! Actual inverse-gradient realization of the shared-resource finite projection anchor endgame.
The conditional payment is invoked only after its current ratio floor has
been proved. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace ContinuousLinearMap AdjointOrbitRecurrence
open scoped ContDiff ENNReal BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLSBelow25 KLSBelow25.ProjectionOrbitSlack KLS.DeterministicBridgeNext
open KLSBelow25.ProjectionExpandedProfileNumerics
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n→ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0<κ)
  (hlower : ∀ x (a : Fin n→ℝ),
    κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  (hμ : admissibleMeasure (potentialMeasure φ))

theorem actual_projection_expanded_profile_normalized_conditional_payment
    (f : GradedCenteredTensorHilbert hφ) (m : ℕ)
    (hl : floorFactor ≤  shiftedOrbitRatio (gradedTensorIntegration hφ hκ hlower) f K m) :
    let R := gradedTensorIntegration hφ hκ hlower
    let P := gradedLinearTensorProjection hφ hκ hlower hμ.isotropic
    eta*shiftedObservation R P f K m ≤ 
      weight*shiftedSlack R P f K m+(1-weight)*shiftedSlack R P f K (m+1) := by
  let R := gradedTensorIntegration hφ hκ hlower
  let P := gradedLinearTensorProjection hφ hκ hlower hμ.isotropic
  have hK : 0<K := K_positive
  have hl0 : 0<floorFactor := by norm_num [floorFactor]
  have hvpos : 0<AdjointOrbitRecurrence.energy R f (m+1) := by
    by_contra hn
    have hz : AdjointOrbitRecurrence.energy R f (m+1)=0 := le_antisymm (le_of_not_gt hn) (by dsimp [AdjointOrbitRecurrence.energy];positivity)
    have hh : shiftedOrbitRatio R f K m=0 := by simp [shiftedOrbitRatio,hz]
    change floorFactor ≤  shiftedOrbitRatio R f K m at hl
    rw [hh] at hl
    linarith
  have hupos : 0<AdjointOrbitRecurrence.energy R f m := by
    by_contra hn
    have hz : AdjointOrbitRecurrence.energy R f m=0 := le_antisymm (le_of_not_gt hn) (by dsimp [AdjointOrbitRecurrence.energy];positivity)
    have hz1 := energy_zero_succ R f m hz
    linarith
  have hratio : K*floorFactor*AdjointOrbitRecurrence.energy R f m ≤ AdjointOrbitRecurrence.energy R f (m+1) := by
    have hh := (le_div_iff₀ (mul_pos hK hupos)).1 hl
    nlinarith only [hh]
  have hp := actual_projection_seed239_expanded_shared_resource_conditional_payment_positive hφ hκ hlower hμ
    (orbit R f m) (orbit R f (m+1)) (orbit R f (m+2))
    (orbit_succ R f m) (by simpa only [Nat.add_assoc,Nat.reduceAdd] using orbit_succ R f (m+1))
    hupos hvpos hratio
  change eta*(‖P (orbit R f (m+1))‖^2/AdjointOrbitRecurrence.energy R f (m+1)) ≤ 
    weight*((AdjointOrbitRecurrence.energy R f (m+2)+‖P (orbit R f (m+1))‖^2-‖orbit R f (m+1)‖^4/AdjointOrbitRecurrence.energy R f m)/AdjointOrbitRecurrence.energy R f (m+1))+
    (1-weight)*((‖R.adjoint (orbit R f (m+2))‖^2+‖P (orbit R f (m+2))‖^2-
      ‖orbit R f (m+2)‖^4/AdjointOrbitRecurrence.energy R f (m+1))/AdjointOrbitRecurrence.energy R f (m+2)) at hp
  have he : ‖R.adjoint (orbit R f (m+2))‖^2=AdjointOrbitRecurrence.energy R f (m+3) := by
    simp only [AdjointOrbitRecurrence.energy,show m+3=(m+2)+1 by omega,orbit_succ]
  rw [he] at hp
  have hm := div_le_div_of_nonneg_right hp hK.le
  change eta*shiftedObservation R P f K m ≤ 
    weight*shiftedSlack R P f K m+(1-weight)*shiftedSlack R P f K (m+1)
  convert hm using 1 <;> dsimp only [shiftedObservation,shiftedSlack,AdjointOrbitRecurrence.energy] <;>
    simp only [Nat.add_assoc,Nat.reduceAdd,div_eq_mul_inv,_root_.mul_inv_rev] <;> ring


include hμ in
theorem actual_projection_expanded_profile_unit_energy_le
    (f : GradedCenteredTensorHilbert hφ) (hf : ‖f‖=1) :
    ‖(gradedTensorIntegration hφ hκ hlower).adjoint f‖^2 ≤ K*p := by
  let R := gradedTensorIntegration hφ hκ hlower
  let L := gradedConstantIntegration hφ hκ hlower hμ.isotropic
  let P := gradedLinearTensorProjection hφ hκ hlower hμ.isotropic
  let Z := ProjectionOrbitSlack.normalizedOrbit R f K
  let z : ℕ→ℝ := fun i=>Z (i+1)
  let cfull : ℕ→ℝ := fun i=>‖P (orbit R f i)‖^2/K^(i+1)
  let c : ℕ→ℝ := fun i=>cfull (i+1)
  let rho := shiftedOrbitRatio R f K
  let d := shiftedObservation R P f K
  let a := shiftedSlack R P f K
  have hK : 0<K := K_positive
  have hcomp := actual_graded_linear_projection_comparison hφ hκ hlower hμ.isotropic
  change ∀ v,‖R v‖^2 ≤ ‖R.adjoint v‖^2+‖P v‖^2 at hcomp
  obtain ⟨hbudget,hcap,hinit,hline⟩ := actual_projection_expanded_profile_data hφ hκ hlower hμ
  change KLSBelow25.CoupledEnergy.jointObservationBudget R L K C at hbudget
  have hcident (i : ℕ) : cfull i=K⁻¹^(i+1)*‖L.adjoint ((R.adjoint^i) f)‖^2 := by
    dsimp only [cfull,P,L,R,orbit]
    rw [gradedLinearTensorProjection_norm]
    simp only [div_eq_mul_inv,inv_pow,mul_comm]
  have hc0 (i : ℕ) : 0 ≤ c i := by dsimp [c,cfull];positivity
  have hZ0 : Z 0=1 := by simp [Z,ProjectionOrbitSlack.normalizedOrbit,AdjointOrbitRecurrence.energy,orbit,hf]
  have hcap1 : cfull 1 ≤ firstCap := by
    rw [hcident]
    simpa only [hf,one_pow,mul_one] using hcap f
  have hcinit : thirdLower ≤ (p^2-cfull 1)*(p-cfull 1/p)-cfull 2 := by
    rw [hcident 1,hcident 2]
    exact hinit f hf
  have hcline : weight1*cfull 1+weight2*cfull 2 ≤  supportCap := by
    rw [hcident 1,hcident 2]
    simpa only [hf,one_pow,mul_one] using hline f
  have hcbudget (N : ℕ) : (∑i∈Finset.range N,c i) ≤ C := by
    change KLSBelow25.CoupledEnergy.prefixBudget cfull N ≤ C
    rw [KLSBelow25.CoupledEnergy.prefixBudget_eq_Icc]
    have hb := hbudget N f
    simp only [hf,one_pow,mul_one] at hb
    convert hb using 1
    apply Finset.sum_congr rfl
    intro i hi
    exact hcident i
  have hZrec (m : ℕ) (hm : 0<Z m) (hm1 : 0<Z (m+1)) :
      Z (m+1)^2/Z m-cfull (m+1) ≤ Z (m+2) := by
    simpa only [Z,cfull,show m+1+1=m+2 by omega] using
      normalized_projection_energy_recurrence R P f hK hcomp m hm hm1
  by_contra hn
  have hfirstRaw : K*p<‖R.adjoint f‖^2 := not_le.mp hn
  have hZ1 : p ≤ Z 1 := by
    dsimp only [Z,ProjectionOrbitSlack.normalizedOrbit,AdjointOrbitRecurrence.energy,orbit]
    simp only [pow_one]
    apply (le_div_iff₀ hK).2
    nlinarith only [hfirstRaw]
  obtain ⟨hp,hl0,hl1,heta0,heta1,hw0,hw1,hgrowth,hRatioFloor,hgamma,hgain,hinterval,_,_⟩ :=
    finite_anchor_parameters
  obtain ⟨_,hpu,hpv,hucap,_,_,_⟩ := head_parameters
  have hUpos : 0<secondLower := (by linarith : 0<p).trans_le hpu
  have hVpos : 0<thirdLower := by norm_num [thirdLower]
  obtain ⟨hz0,hz1,hz2⟩ := ProjectionSlackRatio.normalized_early_correlated_initialization
    Z cfull (by linarith : 0<p) hUpos hucap hZ0 hZ1
    (by dsimp [cfull];positivity) hcap1 hcinit hZrec
  have hfirst : p ≤ rho 0 := by
    change p ≤ shiftedOrbitRatio R f K 0
    rw [shifted_ratio_eq_normalized R f hK]
    change p ≤ Z 1/Z 0
    rw [hZ0,div_one]
    exact hz0
  have hcost (N : ℕ) (hN : 2 ≤ N)
      (hfloor : ∀ (i : ℕ), 2 ≤ i → i < N → floorFactor*thirdLower ≤ z i) :
      (∑i∈Finset.range N,d i) ≤ totalSpend/floorFactor := by
    apply ProjectionSlackRatio.finite_prefix_ratio_cost_le c z d
      floorFactor thirdLower p secondLower supportCap C hl0 hl1.le hVpos
      (by linarith) hUpos hc0
    · intro i
      simpa only [c,cfull,z,Z,show i+1+1=i+2 by omega] using
        shifted_observation_eq_normalized R P f hK i
    · exact hz0
    · exact hz1
    · exact hN
    · exact hfloor
    · exact hcbudget N
    · simpa only [c,weight1,weight2] using hcline
  have hpay (m : ℕ) (hm : floorFactor ≤ rho m) :
      eta*d m ≤ weight*a m+(1-weight)*a (m+1) :=
    actual_projection_expanded_profile_normalized_conditional_payment hφ hκ hlower hμ f m hm
  have hgrow : ∀j,floorFactor*thirdLower*growth^j ≤ z (j+3) := by
    apply ProjectionSlackRatio.finite_anchor_orbit_growth z rho d a p totalSpend
      floorFactor thirdLower eta weight correctedLower remainingSpend growth
      hl0 hl1.le hVpos heta0.le heta1.le (by linarith) hw1
      (by norm_num [floorFactor]) (by norm_num [remainingSpend,totalSpend,supportCap,C,thirdLower,floorFactor,p])
      rfl rfl hRatioFloor hinterval hgamma hgrowth.le hgain hfirst
    · intro m
      exact shifted_slack_nonneg R P f hK hcomp m
    · intro m
      exact shifted_observation_nonneg R P f hK m
    · intro m
      exact shifted_ratio_recurrence R P f hK m
    · exact hpay
    · intro m
      simpa only [z,Z,show m+1+1=m+2 by omega] using normalized_orbit_ratio_step R f hK m
    · exact hcost
    · exact hz2
  have henv : ∀r : ℝ,1<r→∃M : ℝ,∀j,z j ≤ M*r^j := by
    intro r hr
    obtain ⟨M,hM⟩ := actual_seed239_expanded_adjoint_power_envelope hφ hκ hlower hμ r hr
    refine ⟨M*r,fun j=>?_⟩
    have hop := (R.adjoint^(j+1)).le_opNorm f
    rw [hf,mul_one] at hop
    have he : AdjointOrbitRecurrence.energy R f (j+1) ≤ M*(K*r)^(j+1) :=
      (pow_le_pow_left₀ (norm_nonneg _) hop 2).trans (hM (j+1))
    have hd := div_le_div_of_nonneg_right he (pow_nonneg hK.le (j+1))
    change AdjointOrbitRecurrence.energy R f (j+1)/K^(j+1) ≤ (M*r)*r^j
    convert hd using 1
    rw [mul_pow,pow_succ]
    field_simp
    ring
  exact ProjectionSlackRatio.shifted_growth_contradicts_all_rate_envelope z
    (mul_pos hl0 hVpos) hgrowth hgrow henv

include hμ in
theorem actual_projection_expanded_profile_operator_norm_sq_le :
    ‖gradedTensorIntegration hφ hκ hlower‖^2 ≤ K*p := by
  let R := gradedTensorIntegration hφ hκ hlower
  have hs : 0<K*p := by norm_num [K,p]
  have hn : ‖R.adjoint‖ ≤ Real.sqrt (K*p) := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro f hf
    apply (Real.le_sqrt (norm_nonneg _) hs.le).2
    exact actual_projection_expanded_profile_unit_energy_le hφ hκ hlower hμ f hf
  rw [ContinuousLinearMap.adjoint.norm_map] at hn
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt hs.le)

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_projection_expanded_profile_normalized_conditional_payment

#print axioms KLS.DeterministicBridgeIntegration.actual_projection_expanded_profile_unit_energy_le
#print axioms KLS.DeterministicBridgeIntegration.actual_projection_expanded_profile_operator_norm_sq_le
