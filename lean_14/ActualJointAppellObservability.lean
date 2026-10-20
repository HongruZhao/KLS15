import ActualRepeatedAppellObservation
import GradedJointObservationTransfer
import AdjointOrbitRecurrence

/-! Coupled actual Appell energies pass to every free tensor rank with
no dimension or rank factor. The same component test is used at each degree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open MeasureTheory InnerProductSpace Set Filter Matrix ContinuousLinearMap
open scoped ContDiff BigOperators RealInnerProductSpace Topology ENNReal
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25 KLSBelow25.GradedHilbert
variable {n : ℕ} {φ : Space n→ℝ} {κ : ℝ}
variable [IsProbabilityMeasure (potentialMeasure φ)]
variable (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0<κ)
  (hlower : ∀ x (v : Fin n→ℝ), κ*(v ⬝ᵥ v)≤v ⬝ᵥ (coordinateHessian φ x *ᵥ v))
  (hμ : admissibleMeasure (potentialMeasure φ))

abbrev actualPowerObservationBlock (d r : ℕ) :=
  powerObservationBlock (centeredTensorIntegration hφ hκ hlower)
    (constantTensorIntegration hφ hκ hlower) (Real.sqrt_nonneg _)
    (centeredTensorIntegration_opNorm_le hφ hκ hlower) zero_le_one
    (constantTensorIntegration_opNorm_le_one hφ hκ hlower hμ.isotropic) d r

lemma listAppellTensorField_inner_sq_le (r d : ℕ) (t : List (Fin n)→ℝ)
    (v : OrderedTensorField φ r) :
    (inner ℝ (listAppellTensorField hμ r d t) v)^2 ≤
      (d.factorial : ℝ)⁻¹^2*(∑ I, actualAppellEnergy (potentialMeasure φ) (v I) d)*
        ‖orderedConstantTensorField (φ := φ) (fun J : Fin (d+r)→Fin n => t (List.ofFn J))‖^2 := by
  have he : inner ℝ (listAppellTensorField hμ r d t) v=
      (d.factorial : ℝ)⁻¹*∑ I, ∑ a : Fin d→Fin n,
        listAppellSlice t I a*actualAppellCoefficient (potentialMeasure φ) (v I) d a := by
    rw [PiLp.inner_apply]
    simp_rw [listAppellTensorField_apply,real_inner_smul_left,
      inner_polynomialLp_eq_integral,contractedAppellPolynomial_pairing hμ d _ (Lp.memLp _)]
    exact (Finset.mul_sum _ _ _).symm
  rw [he,mul_pow,orderedConstantTensorField_norm_sq]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ((Fin r→Fin n)×(Fin d→Fin n)))
    (fun p => actualAppellCoefficient (potentialMeasure φ) (v p.1) d p.2)
    (fun p => listAppellSlice t p.1 p.2)
  simp only [Fintype.sum_prod_type] at hc
  simp_rw [mul_comm (actualAppellCoefficient _ _ _ _)] at hc
  have ht := listAppellSlice_norm_sum (n := n) r d t
  simp only [actualAppellEnergy] at ⊢
  rw [←ht]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc (sq_nonneg ((d.factorial : ℝ)⁻¹))

/-- Literal adjoint observation bound. Full symmetry of the input
restricts the raw coefficient tensor by an orthogonal contraction, so
there is no extra binomial coefficient. -/
theorem actual_repeated_observation_block_adjoint_sq_le (d r : ℕ)
    (v : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r) :
    ‖(actualPowerObservationBlock hφ hκ hlower hμ d r).adjoint v‖^2 ≤
      ((d+1).factorial : ℝ)⁻¹^2*∑ I, actualAppellEnergy (potentialMeasure φ)
        ((v : OrderedTensorField φ r) I) (d+1) := by
  let B := actualPowerObservationBlock hφ hκ hlower hμ d r
  let F := B.adjoint v
  let T : (Fin (r+d+1)→Fin n)→ℝ := fun I => ∫ x, F.val I x ∂potentialMeasure φ
  let t : List (Fin n)→ℝ := symmetricListExtension (r+d+1) T
  have hT : ∀ I J, List.Perm (List.ofFn I) (List.ofFn J) → T I=T J := by
    intro I J hIJ
    exact congrArg (fun f : Lp ℝ 2 (potentialMeasure φ) => ∫ x, f x ∂potentialMeasure φ)
      ((mem_orderedTensorSymmetricSubspace_iff F.val).mp F.property.1.1 I J hIJ)
  have ht : ListTensorSymmetric t := symmetricListExtension_perm (r+d+1) T hT
  have hF : F=listConstantCompatibleTensor hφ (r+d+1) t ht := by
    apply Subtype.ext
    rw [constantCompatibleTensor_eq hφ (r+d+1) F]
    apply PiLp.ext
    intro I
    simp only [orderedConstantTensorField_apply]
    change T I • CenteredL2.oneLp (potentialMeasure φ)=
      symmetricListExtension (r+d+1) T (List.ofFn I) • CenteredL2.oneLp (potentialMeasure φ)
    rw [symmetricListExtension_ofFn]
  have he := actual_repeated_observation_field hφ hκ hlower hμ hμ.isotropic d r t ht
    (lp.single 2 (r+d) F) (by simpa using hF)
  have hb := listAppellTensorField_inner_sq_le hμ r (d+1) t (v : OrderedTensorField φ r)
  rw [show (d+1)+r=r+d+1 by omega] at hb
  have hc : orderedConstantTensorField (φ := φ)
      (fun I : Fin (r+d+1)→Fin n => t (List.ofFn I))=(F : OrderedTensorField φ (r+d+1)) := by
    rw [hF]
    rfl
  rw [hc] at hb
  have hp : inner ℝ (listAppellTensorField hμ r (d+1) t) (v : OrderedTensorField φ r)=‖F‖^2 := by
    rw [←he]
    change inner ℝ (B F) v=‖F‖^2
    calc
      _ = inner ℝ v (B F) := real_inner_comm _ _
      _ = inner ℝ (B.adjoint v) F := (adjoint_inner_left B F v).symm
      _ = ‖F‖^2 := real_inner_self_eq_norm_sq F
  rw [hp] at hb
  change (‖F‖^2)^2 ≤ _*‖F‖^2 at hb
  change ‖F‖^2 ≤ _
  by_cases hz : ‖F‖^2=0
  · rw [hz]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => actualAppellEnergy_nonneg _ _ _))
  · have hp : 0<‖F‖^2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    rw [pow_two (‖F‖^2)] at hb
    exact le_of_mul_le_mul_right hb hp

/-- A single scalar coupled-energy estimate controls the same joint
sum of adjoint observations at every free tensor rank. -/
theorem actual_joint_observation_block_le {K C : ℝ} (hK : 0<K)
    (hcoupled : ∀ (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)),
      ∑d∈Finset.Icc 2 N,K⁻¹^d*actualAppellEnergy (potentialMeasure φ) f d/(d.factorial : ℝ)^2≤C*‖f‖^2)
    (M r : ℕ) (v : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r) :
    ∑m∈Finset.Icc 1 M,K⁻¹^(m+1)*‖(actualPowerObservationBlock hφ hκ hlower hμ m r).adjoint v‖^2≤C*‖v‖^2 := by
  calc
    _ ≤ ∑m∈Finset.Icc 1 M,K⁻¹^(m+1)*(((m+1).factorial : ℝ)⁻¹^2*
        ∑I,actualAppellEnergy (potentialMeasure φ) ((v : OrderedTensorField φ r) I) (m+1)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left
        (actual_repeated_observation_block_adjoint_sq_le hφ hκ hlower hμ m r v)
        (pow_nonneg (inv_nonneg.mpr hK.le) _)
    _ = ∑I,∑m∈Finset.Icc 1 M,K⁻¹^(m+1)*
        actualAppellEnergy (potentialMeasure φ) ((v : OrderedTensorField φ r) I) (m+1)/
          ((m+1).factorial : ℝ)^2 := by
      simp_rw [←mul_assoc,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro m hm
      simp only [div_eq_mul_inv,inv_pow]
      ring
    _ = ∑I,∑d∈Finset.Icc 2 (M+1),K⁻¹^d*
        actualAppellEnergy (potentialMeasure φ) ((v : OrderedTensorField φ r) I) d/(d.factorial : ℝ)^2 := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_bij (fun m _ => m+1)
      · intro m hm
        simp only [Finset.mem_Icc] at hm ⊢
        omega
      · intro a ha b hb he
        omega
      · intro d hd
        simp only [Finset.mem_Icc] at hd
        refine ⟨d-1,?_,?_⟩
        · simp only [Finset.mem_Icc]
          omega
        · omega
      · intro m hm
        rfl
    _ ≤ ∑I,C*‖(v : OrderedTensorField φ r) I‖^2 :=
      Finset.sum_le_sum (fun I _ => hcoupled (M+1) ((v : OrderedTensorField φ r) I))
    _ = _ := by
      rw [←Finset.mul_sum,←PiLp.norm_sq_eq_of_L2]
      rfl

/-- Coupled scalar Appell control gives the genuine joint observability
bound on the entire graded tensor Hilbert space, with identical constants. -/
theorem actual_joint_graded_observability {K C : ℝ} (hK : 0<K) (hC : 0≤C)
    (hcoupled : ∀ (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)),
      ∑d∈Finset.Icc 2 N,K⁻¹^d*actualAppellEnergy (potentialMeasure φ) f d/(d.factorial : ℝ)^2≤C*‖f‖^2)
    (M : ℕ) (f : GradedCenteredTensorHilbert hφ) :
    ∑m∈Finset.Icc 1 M,K⁻¹^(m+1)*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^m) f)‖^2≤C*‖f‖^2 := by
  have hb := weighted_joint_adjoint_observation_le_of_blocks
    (centeredTensorIntegration hφ hκ hlower) (constantTensorIntegration hφ hκ hlower)
    (Real.sqrt_nonneg _) (centeredTensorIntegration_opNorm_le hφ hκ hlower) zero_le_one
    (constantTensorIntegration_opNorm_le_one hφ hκ hlower hμ.isotropic)
    (Finset.Icc 1 M) (fun m => K⁻¹^(m+1)) hC
    (fun r v => actual_joint_observation_block_le hφ hκ hlower hμ hK hcoupled M r v) f
  change ∑m∈Finset.Icc 1 M,K⁻¹^(m+1)*
    ‖(((gradedTensorIntegration hφ hκ hlower)^m).comp
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic)).adjoint f‖^2≤C*‖f‖^2 at hb
  simpa only [adjoint_comp,AdjointOrbitRecurrence.adjoint_pow,ContinuousLinearMap.comp_apply] using hb

end KLS.DeterministicBridgeIntegration
end
#print axioms KLS.DeterministicBridgeIntegration.actual_repeated_observation_block_adjoint_sq_le

#print axioms KLS.DeterministicBridgeIntegration.actual_joint_observation_block_le
#print axioms KLS.DeterministicBridgeIntegration.actual_joint_graded_observability
